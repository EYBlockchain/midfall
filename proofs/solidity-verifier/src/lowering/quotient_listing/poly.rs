// SPDX-License-Identifier: CC0-1.0
//! Sparse multivariate polynomials over BLS12-381 Fr used by the quotient
//! listing.
//!
//! Variables are verifier memory addresses (evaluation slots, challenges,
//! Lagrange values). Monomials are sorted address multisets, so two
//! polynomials are equal exactly when their canonical term maps are equal.
//! Expansion is capped: identities whose expansion would exceed
//! [`POLY_TERM_CAP`] monomials are reported as "not expanded" instead of
//! consuming unbounded time or memory.

use std::collections::BTreeMap;

use ff::Field;
use midnight_curves::Fq;
use ruint::aliases::U256;

use crate::lowering::{encoding::fe_to_u256, quotient_numerator::vm::disasm::fr_modulus};

/// Maximum number of monomials kept in any intermediate expansion.
pub(crate) const POLY_TERM_CAP: usize = 4096;
/// Maximum number of monomial products tried by one multiplication.
const POLY_MUL_WORK_CAP: usize = 1 << 20;

/// Sparse polynomial `sum coeff * prod vars`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Poly {
    terms: BTreeMap<Vec<u32>, Fq>,
}

impl Poly {
    /// The zero polynomial.
    pub(crate) fn zero() -> Self {
        Self::default()
    }

    /// A constant polynomial.
    pub(crate) fn constant(value: Fq) -> Self {
        let mut poly = Self::zero();
        if value != Fq::ZERO {
            poly.terms.insert(Vec::new(), value);
        }
        poly
    }

    /// The degree-one polynomial for one memory slot.
    pub(crate) fn var(addr: u32) -> Self {
        let mut poly = Self::zero();
        poly.terms.insert(vec![addr], Fq::ONE);
        poly
    }

    /// Number of monomials with a non-zero coefficient.
    pub(crate) fn len(&self) -> usize {
        self.terms.len()
    }

    /// Total degree (zero for constants and the zero polynomial).
    pub(crate) fn degree(&self) -> usize {
        self.terms.keys().map(Vec::len).max().unwrap_or(0)
    }

    /// Iterate over `(monomial, coefficient)` pairs in canonical order.
    pub(crate) fn terms(&self) -> impl Iterator<Item = (&Vec<u32>, &Fq)> {
        self.terms.iter()
    }

    /// Add `coeff * monomial`, dropping cancelled terms.
    fn accumulate(&mut self, monomial: Vec<u32>, coeff: Fq) {
        if coeff == Fq::ZERO {
            return;
        }
        match self.terms.entry(monomial) {
            std::collections::btree_map::Entry::Vacant(slot) => {
                slot.insert(coeff);
            }
            std::collections::btree_map::Entry::Occupied(mut slot) => {
                let sum = *slot.get() + coeff;
                if sum == Fq::ZERO {
                    slot.remove();
                } else {
                    *slot.get_mut() = sum;
                }
            }
        }
    }

    /// Fail when the expansion grows beyond the cap.
    fn check_cap(self) -> Result<Self, String> {
        if self.terms.len() > POLY_TERM_CAP {
            Err(format!("expansion exceeds {POLY_TERM_CAP} monomials"))
        } else {
            Ok(self)
        }
    }

    /// Polynomial sum.
    pub(crate) fn add(mut self, other: Self) -> Result<Self, String> {
        for (monomial, coeff) in other.terms {
            self.accumulate(monomial, coeff);
        }
        self.check_cap()
    }

    /// Polynomial product.
    pub(crate) fn mul(&self, other: &Self) -> Result<Self, String> {
        if self.terms.len().saturating_mul(other.terms.len()) > POLY_MUL_WORK_CAP {
            return Err(format!("expansion exceeds {POLY_TERM_CAP} monomials"));
        }
        let mut out = Self::zero();
        for (lhs, lhs_coeff) in &self.terms {
            for (rhs, rhs_coeff) in &other.terms {
                let mut monomial = Vec::with_capacity(lhs.len() + rhs.len());
                monomial.extend_from_slice(lhs);
                monomial.extend_from_slice(rhs);
                monomial.sort_unstable();
                out.accumulate(monomial, *lhs_coeff * rhs_coeff);
            }
            if out.terms.len() > POLY_TERM_CAP {
                return Err(format!("expansion exceeds {POLY_TERM_CAP} monomials"));
            }
        }
        out.check_cap()
    }

    /// Polynomial negation.
    pub(crate) fn neg(mut self) -> Self {
        for coeff in self.terms.values_mut() {
            *coeff = -*coeff;
        }
        self
    }

    /// Largest monomial dividing every term (as a sorted address multiset).
    pub(crate) fn common_factor(&self) -> Vec<u32> {
        if self.terms.len() < 2 {
            return Vec::new();
        }
        let mut iter = self.terms.keys();
        let mut common = iter.next().cloned().unwrap_or_default();
        for monomial in iter {
            common = multiset_intersection(&common, monomial);
            if common.is_empty() {
                break;
            }
        }
        common
    }

    /// Divide every monomial by `factor` (which must divide all of them).
    pub(crate) fn divide_monomial(&self, factor: &[u32]) -> Self {
        let mut out = Self::zero();
        for (monomial, coeff) in &self.terms {
            out.terms.insert(multiset_difference(monomial, factor), *coeff);
        }
        out
    }
}

/// Intersection of two sorted multisets.
fn multiset_intersection(lhs: &[u32], rhs: &[u32]) -> Vec<u32> {
    let (mut i, mut j) = (0usize, 0usize);
    let mut out = Vec::new();
    while i < lhs.len() && j < rhs.len() {
        match lhs[i].cmp(&rhs[j]) {
            std::cmp::Ordering::Less => i += 1,
            std::cmp::Ordering::Greater => j += 1,
            std::cmp::Ordering::Equal => {
                out.push(lhs[i]);
                i += 1;
                j += 1;
            }
        }
    }
    out
}

/// Remove one occurrence of each element of `factor` from sorted `monomial`.
fn multiset_difference(monomial: &[u32], factor: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(monomial.len());
    let mut j = 0usize;
    for &var in monomial {
        if j < factor.len() && factor[j] == var {
            j += 1;
        } else {
            out.push(var);
        }
    }
    out
}

/// Readable magnitude of a field element: small decimals, `2^k`, `m*2^k`,
/// or hexadecimal.
fn magnitude(value: U256) -> String {
    if value == U256::ZERO {
        return "0".to_string();
    }
    let trailing = value.trailing_zeros();
    let odd = value >> trailing;
    if odd == U256::from(1u64) && trailing >= 8 {
        return format!("2^{trailing}");
    }
    if trailing >= 16 && odd < U256::from(1u64 << 16) {
        return format!("{odd}*2^{trailing}");
    }
    if value < U256::from(1u64 << 32) {
        return format!("{value}");
    }
    format!("0x{value:x}")
}

/// Split a field element into `(is_negative, magnitude)` so that elements
/// closer to `r` than to zero print as negatives.
pub(crate) fn signed_fr(value: Fq) -> (bool, U256) {
    let word = fe_to_u256::<Fq>(&value);
    let modulus = fr_modulus();
    let half = modulus >> 1;
    if word > half {
        (true, modulus - word)
    } else {
        (false, word)
    }
}

/// Readable form of a field element: `1`, `2^56`, `-1`, `-2^56`, `0x…`, or
/// `r - 0x…` for elements near the modulus without a short form.
pub(crate) fn readable_fr(value: Fq) -> String {
    let (negative, mag) = signed_fr(value);
    let text = magnitude(mag);
    if !negative {
        text
    } else if text.starts_with("0x") {
        format!("r - {text}")
    } else {
        format!("-{text}")
    }
}

/// Compact form used inside instruction operands (long hex abbreviated).
///
/// Prints the canonical value as hex (abbreviated above 20 digits; the full
/// word is in the listing's constant table) followed by the readable form when
/// that adds information: `0x100000000000000 (2^56)`,
/// `0x73eda753..00000000 (-1)`, `0x3212e00c..0347fcb8`.
pub(crate) fn compact_fr(value: Fq) -> String {
    let hex = abbreviate_hex(&format!("0x{:x}", fe_to_u256::<Fq>(&value)));
    let readable = abbreviate_hex(&readable_fr(value));
    if readable == hex {
        hex
    } else {
        format!("{hex} ({readable})")
    }
}

/// Abbreviate any `0x` literal longer than 20 hex digits as
/// `0xAAAAAAAA..BBBBBBBB`.
fn abbreviate_hex(text: &str) -> String {
    let Some(pos) = text.find("0x") else {
        return text.to_string();
    };
    let (prefix, hex) = text.split_at(pos);
    let digits = &hex[2..];
    if digits.len() <= 20 {
        return text.to_string();
    }
    format!(
        "{prefix}0x{}..{}",
        &digits[..8],
        &digits[digits.len() - 8..]
    )
}

/// Render a monomial as `name^k * name`, using `name_of` for each address.
pub(crate) fn monomial_string(monomial: &[u32], name_of: &dyn Fn(u32) -> String) -> String {
    if monomial.is_empty() {
        return "1".to_string();
    }
    let mut parts = Vec::new();
    let mut i = 0usize;
    while i < monomial.len() {
        let var = monomial[i];
        let mut count = 1usize;
        while i + count < monomial.len() && monomial[i + count] == var {
            count += 1;
        }
        let name = name_of(var);
        parts.push(if count == 1 {
            name
        } else {
            format!("{name}^{count}")
        });
        i += count;
    }
    parts.join(" * ")
}

/// Render the polynomial as one signed term per line, factoring out the
/// largest monomial common to all terms.
pub(crate) fn polynomial_lines(poly: &Poly, name_of: &dyn Fn(u32) -> String) -> Vec<String> {
    if poly.len() == 0 {
        return vec!["0".to_string()];
    }
    let factor = poly.common_factor();
    let body = if factor.is_empty() {
        poly.clone()
    } else {
        poly.divide_monomial(&factor)
    };
    let mut ordered = body.terms().collect::<Vec<_>>();
    ordered.sort_by(|(a, _), (b, _)| a.len().cmp(&b.len()).then_with(|| a.cmp(b)));
    let mut terms = Vec::with_capacity(ordered.len());
    for (monomial, coeff) in ordered {
        let (negative, mag) = signed_fr(*coeff);
        let sign = if negative { "-" } else { "+" };
        let mag_text = magnitude(mag);
        let term = if monomial.is_empty() {
            mag_text
        } else if mag == U256::from(1u64) {
            monomial_string(monomial, name_of)
        } else {
            format!("{mag_text} * {}", monomial_string(monomial, name_of))
        };
        terms.push(format!("{sign} {term}"));
    }
    if factor.is_empty() {
        terms
    } else {
        let mut lines = vec![format!("{} * (", monomial_string(&factor, name_of))];
        lines.extend(terms.into_iter().map(|term| format!("    {term}")));
        lines.push(")".to_string());
        lines
    }
}
