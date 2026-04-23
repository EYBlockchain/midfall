use std::{io, io::Read};

use blake2b_simd::{Params, State as Blake2bState};
use ff::{FromUniformBytes, PrimeField};
use group::GroupEncoding;
#[cfg(feature = "dev-curves")]
use midnight_curves::bn256::{Fr, G1};
#[cfg(feature = "keccak-transcript")]
use sha3::{Digest, Keccak256};

#[cfg(feature = "keccak-transcript")]
use crate::transcript::{KECCAK256_PREFIX_CHALLENGE, KECCAK256_PREFIX_COMMON};
use crate::transcript::{
    Hashable, Sampleable, TranscriptHash, BLAKE2B_PREFIX_CHALLENGE, BLAKE2B_PREFIX_COMMON,
};

impl TranscriptHash for Blake2bState {
    type Input = Vec<u8>;
    type Output = Vec<u8>;

    fn init() -> Self {
        Params::new().hash_length(64).key(b"Domain separator for transcript").to_state()
    }

    fn absorb(&mut self, input: &Self::Input) {
        self.update(&[BLAKE2B_PREFIX_COMMON]);
        self.update(input);
    }

    fn squeeze(&mut self) -> Self::Output {
        self.update(&[BLAKE2B_PREFIX_CHALLENGE]);
        self.finalize().as_bytes().to_vec()
    }
}

impl<T: TranscriptHash<Input = Vec<u8>>> Hashable<T> for u32 {
    fn to_input(&self) -> Vec<u8> {
        self.to_le_bytes().to_vec()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.to_le_bytes().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = [0u8; 4];
        buffer.read_exact(&mut bytes)?;
        Ok(u32::from_le_bytes(bytes))
    }
}

#[cfg(feature = "dev-curves")]
impl Hashable<Blake2bState> for G1 {
    /// Converts it to compressed form in bytes
    fn to_input(&self) -> Vec<u8> {
        Hashable::<Blake2bState>::to_bytes(self)
    }

    fn to_bytes(&self) -> Vec<u8> {
        <Self as GroupEncoding>::to_bytes(self).as_ref().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as GroupEncoding>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_bytes(&bytes))
            .ok_or_else(|| io::Error::other("Invalid BN point encoding in proof"))
    }
}

#[cfg(feature = "dev-curves")]
impl Hashable<Blake2bState> for Fr {
    fn to_input(&self) -> Vec<u8> {
        self.to_bytes().to_vec()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.to_bytes().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as PrimeField>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_repr(bytes))
            .ok_or_else(|| io::Error::other("Invalid BN scalar encoding in proof"))
    }
}

#[cfg(feature = "dev-curves")]
impl Sampleable<Blake2bState> for Fr {
    fn sample(hash_output: Vec<u8>) -> Self {
        assert!(hash_output.len() <= 64);
        let mut bytes = [0u8; 64];
        bytes[..hash_output.len()].copy_from_slice(&hash_output);
        Fr::from_uniform_bytes(&bytes)
    }
}

// //////////////////////////////////////////////////////////
// /// Implementation of Hashable for BLS12-381 with Blake //
// //////////////////////////////////////////////////////////

impl Hashable<Blake2bState> for midnight_curves::G1Projective {
    /// Converts it to compressed form in bytes
    fn to_input(&self) -> Vec<u8> {
        Hashable::<Blake2bState>::to_bytes(self)
    }

    fn to_bytes(&self) -> Vec<u8> {
        <Self as GroupEncoding>::to_bytes(self).as_ref().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as GroupEncoding>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_bytes(&bytes))
            .ok_or_else(|| io::Error::other("Invalid BLS12-381 point encoding in proof"))
    }
}

impl Hashable<Blake2bState> for midnight_curves::Fq {
    fn to_input(&self) -> Vec<u8> {
        self.to_repr().to_vec()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.to_repr().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as PrimeField>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_repr(bytes))
            .ok_or_else(|| io::Error::other("Invalid BLS12-381 scalar encoding in proof"))
    }
}

impl Sampleable<Blake2bState> for midnight_curves::Fq {
    fn sample(hash_output: Vec<u8>) -> Self {
        assert!(hash_output.len() <= 64);
        assert!(hash_output.len() >= (midnight_curves::Fq::NUM_BITS as usize / 8) + 12);
        let mut bytes = [0u8; 64];
        bytes[..hash_output.len()].copy_from_slice(&hash_output);
        midnight_curves::Fq::from_uniform_bytes(&bytes)
    }
}

// /////////////////////////////////////////////////////////////////////
// /// Implementation of TranscriptHash for Keccak256                 //
// /////////////////////////////////////////////////////////////////////

#[cfg(feature = "keccak-transcript")]
impl TranscriptHash for Keccak256 {
    type Input = Vec<u8>;
    type Output = Vec<u8>;

    fn init() -> Self {
        let mut hasher = Keccak256::new();
        hasher.update(b"Domain separator for transcript");
        hasher
    }

    fn absorb(&mut self, input: &Self::Input) {
        self.update([KECCAK256_PREFIX_COMMON]);
        self.update(input);
    }

    fn squeeze(&mut self) -> Self::Output {
        self.update([KECCAK256_PREFIX_CHALLENGE]);

        // Keccak256 produces a 32-byte digest, which is not wide enough to
        // safely sample a uniformly random scalar in a ~256-bit field via
        // `from_uniform_bytes`. We therefore produce 64 bytes by running two
        // domain-separated Keccak256 finalisations over the current state.
        let mut h1 = self.clone();
        h1.update([0u8]);
        let out1 = h1.finalize();

        let mut h2 = self.clone();
        h2.update([1u8]);
        let out2 = h2.finalize();

        let mut out = Vec::with_capacity(64);
        out.extend_from_slice(&out1);
        out.extend_from_slice(&out2);

        // Re-seed the state with the squeezed challenge so that subsequent
        // absorb/squeeze calls depend on the challenge we just produced.
        let mut new_hasher = Keccak256::new();
        new_hasher.update(&out);
        *self = new_hasher;

        out
    }
}

#[cfg(all(feature = "dev-curves", feature = "keccak-transcript"))]
impl Hashable<Keccak256> for G1 {
    fn to_input(&self) -> Vec<u8> {
        Hashable::<Keccak256>::to_bytes(self)
    }

    fn to_bytes(&self) -> Vec<u8> {
        <Self as GroupEncoding>::to_bytes(self).as_ref().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as GroupEncoding>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_bytes(&bytes))
            .ok_or_else(|| io::Error::other("Invalid BN point encoding in proof"))
    }
}

#[cfg(all(feature = "dev-curves", feature = "keccak-transcript"))]
impl Hashable<Keccak256> for Fr {
    fn to_input(&self) -> Vec<u8> {
        self.to_bytes().to_vec()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.to_bytes().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as PrimeField>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_repr(bytes))
            .ok_or_else(|| io::Error::other("Invalid BN scalar encoding in proof"))
    }
}

#[cfg(all(feature = "dev-curves", feature = "keccak-transcript"))]
impl Sampleable<Keccak256> for Fr {
    fn sample(hash_output: Vec<u8>) -> Self {
        assert!(hash_output.len() <= 64);
        let mut bytes = [0u8; 64];
        bytes[..hash_output.len()].copy_from_slice(&hash_output);
        Fr::from_uniform_bytes(&bytes)
    }
}

#[cfg(feature = "keccak-transcript")]
impl Hashable<Keccak256> for midnight_curves::G1Projective {
    fn to_input(&self) -> Vec<u8> {
        Hashable::<Keccak256>::to_bytes(self)
    }

    fn to_bytes(&self) -> Vec<u8> {
        <Self as GroupEncoding>::to_bytes(self).as_ref().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as GroupEncoding>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_bytes(&bytes))
            .ok_or_else(|| io::Error::other("Invalid BLS12-381 point encoding in proof"))
    }
}

#[cfg(feature = "keccak-transcript")]
impl Hashable<Keccak256> for midnight_curves::Fq {
    fn to_input(&self) -> Vec<u8> {
        self.to_repr().to_vec()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.to_repr().to_vec()
    }

    fn read(buffer: &mut impl Read) -> io::Result<Self> {
        let mut bytes = <Self as PrimeField>::Repr::default();

        buffer.read_exact(bytes.as_mut())?;

        Option::from(Self::from_repr(bytes))
            .ok_or_else(|| io::Error::other("Invalid BLS12-381 scalar encoding in proof"))
    }
}

#[cfg(feature = "keccak-transcript")]
impl Sampleable<Keccak256> for midnight_curves::Fq {
    fn sample(hash_output: Vec<u8>) -> Self {
        assert!(hash_output.len() <= 64);
        assert!(hash_output.len() >= (midnight_curves::Fq::NUM_BITS as usize / 8) + 12);
        let mut bytes = [0u8; 64];
        bytes[..hash_output.len()].copy_from_slice(&hash_output);
        midnight_curves::Fq::from_uniform_bytes(&bytes)
    }
}
