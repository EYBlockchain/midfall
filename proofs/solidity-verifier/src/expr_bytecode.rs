//! Serialises `midnight_proofs::plonk::Expression<Fq>` trees into a compact
//! RPN (reverse-polish) bytecode that the Solidity verifier evaluates with a
//! small stack machine.
//!
//! Rationale: the alternative (emitting inline Solidity per gate) would
//! produce thousands of lines of generated code that is brittle under
//! circuit changes. The bytecode interpreter is ~200 lines of Solidity, is
//! trivially correct given the closed-form semantics of `Expression`, and
//! keeps the contract fully generic w.r.t. the circuit.
//!
//! # Opcode reference
//!
//! | Code  | Mnemonic          | Args                          | Stack effect    |
//! |-------|-------------------|-------------------------------|-----------------|
//! | 0x00  | CONST             | 32-byte Fr (BE)               | — → c           |
//! | 0x01  | FIXED             | u16 index (BE)                | — → fe[i]       |
//! | 0x02  | ADVICE            | u16 index (BE)                | — → ae[i]       |
//! | 0x03  | INSTANCE          | u16 index (BE)                | — → ie[i]       |
//! | 0x04  | CHALLENGE         | u16 index (BE)                | — → ch[i]       |
//! | 0x05  | L_0               |                               | — → L_0(x)      |
//! | 0x06  | L_LAST            |                               | — → L_last(x)   |
//! | 0x07  | L_BLIND           |                               | — → L_blind(x)  |
//! | 0x08  | BETA              |                               | — → β           |
//! | 0x09  | GAMMA             |                               | — → γ           |
//! | 0x0A  | THETA             |                               | — → θ           |
//! | 0x0B  | TRASH_CHALLENGE   |                               | — → τ           |
//! | 0x0C  | X                 |                               | — → x           |
//! | 0x20  | NEG               |                               | a → -a          |
//! | 0x21  | ADD               |                               | a,b → a+b       |
//! | 0x22  | MUL               |                               | a,b → a*b       |
//! | 0x23  | SCALED            | 32-byte Fr (BE)               | a → a*k         |
//! | 0xFF  | END               |                               |                 |
//!
//! A complete bytecode program evaluates to a single Fr value on top of
//! the stack at END. An expression list (gate polynomials) is a sequence
//! of such programs, each terminated by END.

use ff::PrimeField;
use midnight_curves::Fq;
use midnight_proofs::plonk::{AdviceQuery, Expression, FixedQuery, InstanceQuery};

pub const OP_CONST: u8 = 0x00;
pub const OP_FIXED: u8 = 0x01;
pub const OP_ADVICE: u8 = 0x02;
pub const OP_INSTANCE: u8 = 0x03;
pub const OP_CHALLENGE: u8 = 0x04;
pub const OP_L_0: u8 = 0x05;
pub const OP_L_LAST: u8 = 0x06;
pub const OP_L_BLIND: u8 = 0x07;
pub const OP_BETA: u8 = 0x08;
pub const OP_GAMMA: u8 = 0x09;
pub const OP_THETA: u8 = 0x0A;
pub const OP_TRASH: u8 = 0x0B;
pub const OP_X: u8 = 0x0C;
pub const OP_NEG: u8 = 0x20;
pub const OP_ADD: u8 = 0x21;
pub const OP_MUL: u8 = 0x22;
pub const OP_SCALED: u8 = 0x23;
pub const OP_END: u8 = 0xFF;

fn fq_be(v: &Fq) -> [u8; 32] {
    let mut le = v.to_repr();
    le.reverse();
    le
}

/// Recursively serialise `Expression<Fq>` into RPN. Uses midnight-proofs'
/// own `Expression::evaluate` closure API with `T = Vec<u8>`; each callback
/// appends opcodes/operands to the accumulator.
pub fn encode_expression(expr: &Expression<Fq>) -> Vec<u8> {
    let bytes: Vec<u8> = expr.evaluate(
        &|c: Fq| {
            let mut out = vec![OP_CONST];
            out.extend_from_slice(&fq_be(&c));
            out
        },
        &|_sel| {
            panic!(
                "Expression::Selector still present in verifier-side gate; \
                 ConstraintSystem should have folded selectors into fixed columns"
            )
        },
        &|q: FixedQuery| {
            let idx = q
                .index()
                .expect("FixedQuery without resolved index") as u16;
            let mut out = vec![OP_FIXED];
            out.extend_from_slice(&idx.to_be_bytes());
            out
        },
        &|q: AdviceQuery| {
            let idx = q
                .index
                .expect("AdviceQuery without resolved index") as u16;
            let mut out = vec![OP_ADVICE];
            out.extend_from_slice(&idx.to_be_bytes());
            out
        },
        &|q: InstanceQuery| {
            let idx = q
                .index
                .expect("InstanceQuery without resolved index") as u16;
            let mut out = vec![OP_INSTANCE];
            out.extend_from_slice(&idx.to_be_bytes());
            out
        },
        &|ch| {
            let idx = ch.index() as u16;
            let mut out = vec![OP_CHALLENGE];
            out.extend_from_slice(&idx.to_be_bytes());
            out
        },
        &|a: Vec<u8>| {
            let mut out = a;
            out.push(OP_NEG);
            out
        },
        &|a: Vec<u8>, b: Vec<u8>| {
            let mut out = a;
            out.extend(b);
            out.push(OP_ADD);
            out
        },
        &|a: Vec<u8>, b: Vec<u8>| {
            let mut out = a;
            out.extend(b);
            out.push(OP_MUL);
            out
        },
        &|a: Vec<u8>, k: Fq| {
            let mut out = a;
            out.push(OP_SCALED);
            out.extend_from_slice(&fq_be(&k));
            out
        },
    );
    let mut final_bytes = bytes;
    final_bytes.push(OP_END);
    final_bytes
}

/// Evaluate a single RPN program (one expression terminated by END) using
/// the same closure interface as Rust's `Expression::evaluate`. This is a
/// *reference* implementation used to sanity-check serialisation: the
/// result of `eval_bytecode(&encode_expression(expr), env)` must equal the
/// result of `expr.evaluate(...)` with the same environment.
///
/// Returns `(value, consumed_bytes)` so callers that concatenate multiple
/// programs know how far to advance.
pub fn eval_bytecode<F: Fn(u8, u16) -> Fq, G: Fn(u8) -> Fq>(
    bytecode: &[u8],
    lookup: &F,
    special: &G,
) -> (Fq, usize) {
    let mut stack: Vec<Fq> = Vec::with_capacity(32);
    let mut i = 0usize;
    while i < bytecode.len() {
        let op = bytecode[i];
        i += 1;
        match op {
            OP_CONST => {
                let mut be = [0u8; 32];
                be.copy_from_slice(&bytecode[i..i + 32]);
                i += 32;
                let mut le = be;
                le.reverse();
                stack.push(Fq::from_repr(le).unwrap());
            }
            OP_FIXED | OP_ADVICE | OP_INSTANCE | OP_CHALLENGE => {
                let idx = u16::from_be_bytes([bytecode[i], bytecode[i + 1]]);
                i += 2;
                stack.push(lookup(op, idx));
            }
            OP_L_0 | OP_L_LAST | OP_L_BLIND | OP_BETA | OP_GAMMA | OP_THETA
            | OP_TRASH | OP_X => {
                stack.push(special(op));
            }
            OP_NEG => {
                let a = stack.pop().unwrap();
                stack.push(-a);
            }
            OP_ADD => {
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                stack.push(a + b);
            }
            OP_MUL => {
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                stack.push(a * b);
            }
            OP_SCALED => {
                let mut be = [0u8; 32];
                be.copy_from_slice(&bytecode[i..i + 32]);
                i += 32;
                let mut le = be;
                le.reverse();
                let k = Fq::from_repr(le).unwrap();
                let a = stack.pop().unwrap();
                stack.push(a * k);
            }
            OP_END => {
                assert_eq!(stack.len(), 1, "stack not singleton at END");
                return (stack.pop().unwrap(), i);
            }
            _ => panic!("unknown opcode 0x{:02x} at {}", op, i - 1),
        }
    }
    panic!("bytecode ran off end without END");
}
