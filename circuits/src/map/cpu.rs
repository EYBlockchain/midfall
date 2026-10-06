// This file is part of MIDNIGHT-ZK.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! CPU implementation of Succinct Key-Value Map Representation Using Merkle
//! Trees

use std::{collections::HashMap, fmt::Debug, marker::PhantomData};

use num_bigint::BigUint;

use crate::{
    instructions::{hash::HashCPU, map::MapCPU},
    utils::util::big_to_fe,
    CircuitField,
};

/// This constant defines the height of the tree. This is a lower bound
/// on the security parameter of the primitive, so it needs to be chosen
/// carefully.
pub(crate) const TREE_HEIGHT: u8 = 255;

const NODE_INDEX_BYTES: usize = 32;

/// A node's position within a level of the tree.
///
/// The index is stored in little-endian order and is always a 255-bit value;
/// the most significant bit of the final byte is unused. Keeping the index in
/// bytes avoids the overflow-prone integer arithmetic that a 255-level tree
/// would otherwise require.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct NodeIndex([u8; NODE_INDEX_BYTES]);

impl NodeIndex {
    fn from_canonical_le_bytes(bytes: &[u8]) -> Self {
        assert_eq!(bytes.len(), NODE_INDEX_BYTES);

        let mut index = [0; NODE_INDEX_BYTES];
        index.copy_from_slice(bytes);
        assert_eq!(index[NODE_INDEX_BYTES - 1] & 0x80, 0);

        Self(index)
    }

    fn is_right(self) -> bool {
        self.0[0] & 1 == 1
    }

    fn sibling(mut self) -> Self {
        self.0[0] ^= 1;
        self
    }

    fn move_to_parent(&mut self) {
        for i in 0..NODE_INDEX_BYTES - 1 {
            self.0[i] = (self.0[i] >> 1) | (self.0[i + 1] << 7);
        }
        self.0[NODE_INDEX_BYTES - 1] >>= 1;
    }

    fn bit_len(self) -> usize {
        self.0.iter().rposition(|byte| *byte != 0).map_or(0, |i| {
            i * 8 + (u8::BITS - self.0[i].leading_zeros()) as usize
        })
    }
}

/// A [MapMt] is a succinct key-value map representation using merkle trees. We
/// do not store all nodes. Instead, we only store the default nodes for each
/// level, and those that have been modified. The map requires a 255-bit field
/// with a 32-byte canonical representation.
#[derive(Clone, Debug)]
pub struct MapMt<F: CircuitField, H: HashCPU<F, F>> {
    pub(crate) root: F,
    // We organise nodes by their height and their position in that level.
    nodes: HashMap<(u8, NodeIndex), F>,
    // Map containing keys and values.
    map: HashMap<BigUint, F>,
    // Tree nodes, organised from leaves to root (though the root is treated separately)
    default_nodes: [F; TREE_HEIGHT as usize],
    _marker: PhantomData<H>,
}

impl<F: CircuitField, H: HashCPU<F, F>> PartialEq for MapMt<F, H> {
    fn eq(&self, other: &Self) -> bool {
        self.root == other.root
            && self.nodes == other.nodes
            && self.default_nodes == other.default_nodes
            && self.map == other.map
    }
}

impl<F: CircuitField, H: HashCPU<F, F>> Eq for MapMt<F, H> {}

impl<F, H> MapCPU<F, F, F> for MapMt<F, H>
where
    F: CircuitField,
    H: HashCPU<F, F>,
{
    fn new(default: &F) -> Self {
        assert_eq!(
            F::NUM_BITS as usize,
            TREE_HEIGHT as usize,
            "MapMt requires a 255-bit field"
        );
        assert_eq!(
            F::NUM_BYTES,
            NODE_INDEX_BYTES,
            "MapMt requires a 32-byte canonical field representation"
        );

        // The set of 'modified' nodes is empty
        let nodes = HashMap::new();
        let map = HashMap::new();

        let mut default_nodes = [*default; TREE_HEIGHT as usize];

        for i in 1..TREE_HEIGHT as usize {
            default_nodes[i] =
                <H as HashCPU<F, F>>::hash(&[default_nodes[i - 1], default_nodes[i - 1]]);
        }

        let top_default = default_nodes[TREE_HEIGHT as usize - 1];
        let root = <H as HashCPU<F, F>>::hash(&[top_default, top_default]);

        Self {
            root,
            nodes,
            map,
            default_nodes,
            _marker: PhantomData,
        }
    }

    fn succinct_repr(&self) -> F {
        self.root
    }

    fn insert(&mut self, key: &F, value: &F) {
        self.map.insert(key.to_biguint(), *value);

        // We initialise the child with the new representation of the element.
        let mut child = *value;
        let mut node_index = Self::compute_node_index(key);

        for height in 0..TREE_HEIGHT {
            self.nodes.insert((height, node_index), child);

            let sibling = self.get_sibling(node_index, height);
            let (x, y) = conditional_swap(node_index.is_right(), &child, &sibling);
            child = <H as HashCPU<F, F>>::hash(&[x, y]);
            node_index.move_to_parent();
        }

        self.root = child;
    }

    fn get(&self, key: &F) -> F {
        self.map.get(&key.to_biguint()).copied().unwrap_or(self.default_nodes[0])
    }
}

impl<F, H> IntoIterator for MapMt<F, H>
where
    F: CircuitField,
    H: HashCPU<F, F>,
{
    type Item = (F, F);
    type IntoIter = std::iter::Map<
        std::collections::hash_map::IntoIter<BigUint, F>,
        fn((BigUint, F)) -> (F, F),
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter().map(|(key, value)| (big_to_fe(key), value))
    }
}

impl<F, H> MapMt<F, H>
where
    F: CircuitField,
    H: HashCPU<F, F>,
{
    /// Returns the nodes in the path for the given key.
    pub(crate) fn get_path(&self, key: &F) -> [F; TREE_HEIGHT as usize] {
        let mut node_index = Self::compute_node_index(key);

        let mut nodes = [F::ZERO; TREE_HEIGHT as usize];

        for (i, val) in nodes.iter_mut().enumerate() {
            *val = self.get_sibling(node_index, i as u8);
            node_index.move_to_parent();
        }

        nodes
    }

    /// Verify that the pair (key, value) is part of the existing map.
    ///
    /// Used for testing
    #[cfg(test)]
    fn verify_mem_proof(root: &F, path: &[F; TREE_HEIGHT as usize], key: &F, value: F) -> bool {
        let mut node_index = Self::compute_node_index(key);
        let mut child = value;

        for node in path {
            let (x, y) = conditional_swap(node_index.is_right(), &child, node);
            child = <H as HashCPU<F, F>>::hash(&[x, y]);
            node_index.move_to_parent();
        }

        *root == child
    }

    /// Get the sibling of an indexed node at a given height
    fn get_sibling(&self, node_index: NodeIndex, height: u8) -> F {
        debug_assert!(node_index.bit_len() <= usize::from(TREE_HEIGHT - height));

        // Flipping the least-significant bit selects the adjacent node at this level.
        let sibling_index = node_index.sibling();

        // If the sibling does not exist, we use the default node for this height
        *self
            .nodes
            .get(&(height, sibling_index))
            .unwrap_or(&self.default_nodes[height as usize])
    }

    /// Get the node index at the leaf level for a given element, represented by
    /// all 255 canonical little-endian bits of the hash output.
    fn compute_node_index(element: &F) -> NodeIndex {
        let hashed_value = <H as HashCPU<F, F>>::hash(&[*element, F::ZERO]);
        let bytes = hashed_value.to_bytes_le();

        NodeIndex::from_canonical_le_bytes(bytes.as_ref())
    }
}

// Takes two inputs and conditionally swaps them before hashing.
fn conditional_swap<F: CircuitField>(cond: bool, left_input: &F, right_input: &F) -> (F, F) {
    if cond {
        (*right_input, *left_input)
    } else {
        (*left_input, *right_input)
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;
    use crate::hash::poseidon::{constants::PoseidonField, PoseidonChip};

    #[derive(Clone, Debug)]
    struct FirstInputHash;

    impl HashCPU<midnight_curves::Fq, midnight_curves::Fq> for FirstInputHash {
        fn hash(inputs: &[midnight_curves::Fq]) -> midnight_curves::Fq {
            inputs[0]
        }
    }

    #[test]
    fn node_index_uses_all_255_canonical_bits() {
        type F = midnight_curves::Fq;

        let key_as_biguint =
            (BigUint::from(1u8) << 254) | (BigUint::from(1u8) << 128) | BigUint::from(1u8);
        let key = F::from_biguint(&key_as_biguint).unwrap();
        let mut index = MapMt::<F, FirstInputHash>::compute_node_index(&key);

        assert!(index.is_right());
        for _ in 0..128 {
            index.move_to_parent();
        }
        assert!(index.is_right());
        for _ in 128..254 {
            index.move_to_parent();
        }
        assert!(index.is_right());
        index.move_to_parent();
        assert_eq!(index.bit_len(), 0);
    }

    fn test_map<F, H>()
    where
        F: CircuitField,
        H: HashCPU<F, F> + Debug,
    {
        let mut rng = ChaCha8Rng::seed_from_u64(0xc0ffee);
        let mut mt = MapMt::<F, H>::new(&F::ZERO);

        // Let's add 100 random keys with one as a value.
        for _ in 0..100 {
            mt.insert(&F::random(&mut rng), &F::ONE);
        }

        // Now let's add key one, with one as a value
        mt.insert(&F::ONE, &F::ONE);
        assert_eq!(mt.get(&F::ONE), F::ONE);

        // If we insert two times the same element, it should equal the old map
        let old_mt = mt.clone();
        mt.insert(&F::ONE, &F::ONE);

        assert_eq!(old_mt, mt);

        // Now we test path generation for proving that a (key, value) pair is part of
        // the map
        let one_path = mt.get_path(&F::ONE);
        let member = MapMt::<F, H>::verify_mem_proof(&mt.root, &one_path, &F::ONE, F::ONE);
        assert!(member);

        let non_member = MapMt::<F, H>::verify_mem_proof(&mt.root, &one_path, &F::ONE, F::ZERO);
        assert!(!non_member);

        // Values that have not been explicitly added have a zero as a value
        let new_value = F::random(&mut rng);
        let path = mt.get_path(&new_value);
        let non_member = MapMt::<F, H>::verify_mem_proof(&mt.root, &path, &new_value, F::ZERO);
        assert!(non_member);
    }

    fn run_poseidon_test<F: PoseidonField>() {
        test_map::<F, PoseidonChip<F>>();
    }

    #[test]
    fn test_map_poseidon() {
        run_poseidon_test::<midnight_curves::Fq>();
    }
}
