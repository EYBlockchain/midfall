// SPDX-License-Identifier: CC0-1.0
//! Yul emission for the direct quotient lowering.
//!
//! Every gate identity becomes `function q_identity_<j>(r)` whose body is the
//! identity's `DirectExpr` written node by node in tree order. Left-deep
//! `Sum` / `Product` chains become accumulate statements
//! (`e := addmod(e, <term>, r)`) so no statement nests deeper than a few calls;
//! small sub-trees (at most `MAX_NODES` nodes and `MAX_DEPTH` levels) are
//! written inline. Simple selectors evaluate to one and `1 * x` is written as
//! `x`, as in `partially_evaluate_identities`. Helper calls are atomic leaves
//! preceded by a comment that spells out their terms.

use std::collections::BTreeSet;

use ff::{Field, PrimeField};
use midnight_curves::Fq;

use super::{
    folds::{FoldBucket, FoldLabel, FoldRecord, FoldSite, FoldWeight, SiteLabel},
    is_pooled,
    layout::{DirectLayout, SectionOp},
    rotation_suffix, sym_const, DirectCall, DirectExpr, DirectGateIdentity, DirectQuotientProgram,
    DirectTarget, HelperShapes, RunKind,
};
use crate::lowering::{encoding::fe_to_u256, layout::WORD_BYTES};

/// Largest sub-tree (nodes) written inline in one statement.
const MAX_NODES: usize = 7;
/// Deepest sub-tree written inline in one statement.
const MAX_DEPTH: usize = 3;
/// A helper call counts as this many nodes, so a statement holds at most one
/// call plus a negation or factor.
const CALL_SIZE: usize = 4;
/// Column of the aligned trailing comments.
const COMMENT_COLUMN: usize = 100;
/// Indentation unit.
const IND: &str = "    ";

/// Yul constant expression for a field constant.
pub(crate) fn const_yul(program: &DirectQuotientProgram, value: &Fq) -> String {
    if is_pooled(value) {
        let idx = program.pool_index(value).expect("pooled constant collected");
        format!("mload(QC_{idx})")
    } else {
        small_const_name(value)
    }
}

/// Name of a small constant (a Solidity literal constant), e.g. `QK_0x2`.
pub(crate) fn small_const_name(value: &Fq) -> String {
    format!("QK_{:#x}", fe_to_u256::<Fq>(value))
}

/// Rendered sub-expression: Yul text, symbolic comment text, and the helper
/// calls it contains (whose comments precede the statement).
#[derive(Clone, Debug, Default)]
struct Rendered {
    yul: String,
    sym: String,
    calls: Vec<DirectCall>,
}

/// One output line of an identity body.
#[derive(Clone, Debug)]
enum Line {
    Comment(String),
    Code(String, Option<String>),
}

/// Parenthesise a symbolic operand unless it is atomic or one balanced group.
fn par(s: &str) -> String {
    if !s.contains(' ') {
        return s.to_string();
    }
    if s.starts_with('(') && s.ends_with(')') {
        let mut depth = 0i32;
        let mut closes_early = false;
        for (i, ch) in s.char_indices() {
            if ch == '(' {
                depth += 1;
            } else if ch == ')' {
                depth -= 1;
            }
            if depth == 0 && i < s.len() - 1 {
                closes_early = true;
                break;
            }
        }
        if !closes_early {
            return s.to_string();
        }
    }
    format!("({s})")
}

/// Whether an expression evaluates to one (simple selector or constant 1).
fn is_one(expr: &DirectExpr) -> bool {
    match expr {
        DirectExpr::SimpleSelector(_) => true,
        DirectExpr::Constant(c) => *c == Fq::ONE,
        _ => false,
    }
}

/// Tree emitter for one identity body.
struct TreeEmitter<'p> {
    program: &'p DirectQuotientProgram,
    shapes: &'p HelperShapes,
    out: Vec<Line>,
    declared: BTreeSet<usize>,
}

impl<'p> TreeEmitter<'p> {
    fn reg(k: usize) -> String {
        if k == 0 {
            "e".to_string()
        } else {
            format!("t{k}")
        }
    }

    /// `(nodes, depth)` of a sub-tree, with `1 * x` elided.
    fn size(expr: &DirectExpr) -> (usize, usize) {
        match expr {
            DirectExpr::Constant(_) | DirectExpr::SimpleSelector(_) | DirectExpr::Slot(_) => (1, 0),
            DirectExpr::Call(_) => (CALL_SIZE, 1),
            DirectExpr::Negated(inner) => {
                let (n, d) = Self::size(inner);
                (n + 1, d + 1)
            }
            DirectExpr::Product(lhs, rhs) if is_one(lhs) => Self::size(rhs),
            DirectExpr::Product(lhs, rhs) if is_one(rhs) => Self::size(lhs),
            DirectExpr::Sum(lhs, rhs) | DirectExpr::Product(lhs, rhs) => {
                let (n1, d1) = Self::size(lhs);
                let (n2, d2) = Self::size(rhs);
                (n1 + n2 + 1, d1.max(d2) + 1)
            }
        }
    }

    /// Inline rendering of a small sub-tree.
    fn simple(&self, expr: &DirectExpr) -> Option<Rendered> {
        let (n, d) = Self::size(expr);
        (n <= MAX_NODES && d <= MAX_DEPTH).then(|| self.expr(expr))
    }

    /// Render a sub-tree inline.
    fn expr(&self, expr: &DirectExpr) -> Rendered {
        match expr {
            DirectExpr::Constant(c) => Rendered {
                yul: const_yul(self.program, c),
                sym: sym_const(c),
                calls: Vec::new(),
            },
            DirectExpr::SimpleSelector(_) => Rendered {
                yul: "1".to_string(),
                sym: "1".to_string(),
                calls: Vec::new(),
            },
            DirectExpr::Slot(slot) => Rendered {
                yul: format!("mload({})", slot.name()),
                sym: slot.short(),
                calls: Vec::new(),
            },
            DirectExpr::Call(call) => {
                let text = call_text(self.program, self.shapes, *call);
                Rendered {
                    yul: text.clone(),
                    sym: text,
                    calls: vec![*call],
                }
            }
            DirectExpr::Negated(inner) => {
                let r = self.expr(inner);
                Rendered {
                    yul: format!("sub(r, {})", r.yul),
                    sym: format!("-{}", par(&r.sym)),
                    calls: r.calls,
                }
            }
            DirectExpr::Product(lhs, rhs) if is_one(lhs) => self.expr(rhs),
            DirectExpr::Product(lhs, rhs) if is_one(rhs) => self.expr(lhs),
            DirectExpr::Product(lhs, rhs) => {
                let a = self.expr(lhs);
                let b = self.expr(rhs);
                Rendered {
                    yul: format!("mulmod({}, {}, r)", a.yul, b.yul),
                    sym: format!("{} * {}", par(&a.sym), par(&b.sym)),
                    calls: [a.calls, b.calls].concat(),
                }
            }
            DirectExpr::Sum(lhs, rhs) => {
                let a = self.expr(lhs);
                let b = self.expr(rhs);
                let sym = match b.sym.strip_prefix('-') {
                    Some(rest) => format!("{} - {rest}", a.sym),
                    None => format!("{} + {}", a.sym, b.sym),
                };
                Rendered {
                    yul: format!("addmod({}, {}, r)", a.yul, b.yul),
                    sym,
                    calls: [a.calls, b.calls].concat(),
                }
            }
        }
    }

    fn assign(&mut self, k: usize, rhs: String, comment: String, calls: &[DirectCall]) {
        for call in calls {
            for line in call_comment(self.program, *call) {
                self.out.push(Line::Comment(line));
            }
        }
        let reg = Self::reg(k);
        let code = if self.declared.insert(k) {
            format!("let {reg} := {rhs}")
        } else {
            format!("{reg} := {rhs}")
        };
        self.out.push(Line::Code(code, Some(comment)));
    }

    /// Emit `expr` into register `k`.
    fn gen(&mut self, expr: &DirectExpr, k: usize) {
        let reg = Self::reg(k);
        if let Some(s) = self.simple(expr) {
            self.assign(k, s.yul, format!("{reg} = {}", s.sym), &s.calls);
            return;
        }
        let (lhs, rhs, is_add) = match expr {
            DirectExpr::Negated(inner) => {
                self.gen(inner, k);
                self.assign(k, format!("sub(r, {reg})"), format!("{reg} = -{reg}"), &[]);
                return;
            }
            DirectExpr::Product(lhs, rhs) if is_one(lhs) => return self.gen(rhs, k),
            DirectExpr::Product(lhs, rhs) if is_one(rhs) => return self.gen(lhs, k),
            DirectExpr::Product(lhs, rhs) => (lhs.as_ref(), rhs.as_ref(), false),
            DirectExpr::Sum(lhs, rhs) => (lhs.as_ref(), rhs.as_ref(), true),
            // Leaves and calls are always simple.
            _ => unreachable!("leaf sub-trees are inline"),
        };
        let op = if is_add { "addmod" } else { "mulmod" };
        let sgn = if is_add { "+" } else { "*" };
        if let Some(sb) = self.simple(rhs) {
            self.gen(lhs, k);
            let comment = match (is_add, sb.sym.strip_prefix('-')) {
                (true, Some(rest)) => format!("- {rest}"),
                (true, None) => format!("+ {}", sb.sym),
                (false, _) => format!("* {}", par(&sb.sym)),
            };
            self.assign(k, format!("{op}({reg}, {}, r)", sb.yul), comment, &sb.calls);
            return;
        }
        if is_add {
            if let DirectExpr::Negated(neg) = rhs {
                // X - Y with a large Y: evaluate Y into the next register.
                self.gen(lhs, k);
                self.gen(neg, k + 1);
                let reg1 = Self::reg(k + 1);
                self.assign(
                    k,
                    format!("addmod({reg}, sub(r, {reg1}), r)"),
                    format!("{reg} = {reg} - {reg1}"),
                    &[],
                );
                return;
            }
        }
        if let Some(sa) = self.simple(lhs) {
            self.gen(rhs, k);
            self.assign(
                k,
                format!("{op}({}, {reg}, r)", sa.yul),
                format!("{reg} = {} {sgn} {reg}", par(&sa.sym)),
                &sa.calls,
            );
            return;
        }
        self.gen(lhs, k);
        self.gen(rhs, k + 1);
        let reg1 = Self::reg(k + 1);
        self.assign(
            k,
            format!("{op}({reg}, {reg1}, r)"),
            format!("{reg} = {reg} {sgn} {reg1}"),
            &[],
        );
    }
}

/// Yul text of a helper call.
pub(crate) fn call_text(
    program: &DirectQuotientProgram,
    shapes: &HelperShapes,
    call: DirectCall,
) -> String {
    match call {
        DirectCall::SumExprs { run, vector } => format!(
            "{}({}, {})",
            shapes.sum_exprs_name(program.runs[run].values.len()),
            program.runs[run].name,
            program.vectors[vector].name
        ),
        DirectCall::SumExprsByDegree { run, table } => format!(
            "{}({}, {})",
            shapes.sum_exprs_by_degree_name(program.runs[run].values.len()),
            program.runs[run].name,
            program.tables[table].name
        ),
    }
}

/// Symbolic name of limb `i` of a vector (for comments).
fn limb_sym(program: &DirectQuotientProgram, vector: usize, i: usize) -> String {
    let v = &program.vectors[vector];
    let base = format!(
        "a{}{}",
        v.first_column + i,
        rotation_suffix(v.rotation).to_ascii_lowercase()
    );
    match v.shift {
        None => base,
        Some(_) => format!("({base} + s)"),
    }
}

/// Comment lines spelling out the terms of a helper call.
pub(crate) fn call_comment(program: &DirectQuotientProgram, call: DirectCall) -> Vec<String> {
    match call {
        DirectCall::SumExprs { run, vector } => {
            let r = &program.runs[run];
            let v = &program.vectors[vector];
            let terms = r
                .values
                .iter()
                .enumerate()
                .map(|(i, c)| format!("{}*{}", sym_const(c), limb_sym(program, vector, i)))
                .collect::<Vec<_>>()
                .join(" + ");
            let mut lines = vec![
                format!("sum_exprs({}, {}) = {terms}", r.name, v.name),
                format!(
                    "    coeffs = {} (VK table, {} words, zeros kept), exprs = {} = {}",
                    r.name,
                    r.values.len(),
                    v.name,
                    v.describe()
                ),
            ];
            if let Some((_, shift)) = v.shift {
                lines.push(format!("    s = {}", sym_const(&shift)));
            }
            lines
        }
        DirectCall::SumExprsByDegree { run, table } => {
            let r = &program.runs[run];
            let t = &program.tables[table];
            let (xs, ys) = (&program.vectors[t.xs], &program.vectors[t.ys]);
            let terms = r
                .values
                .iter()
                .enumerate()
                .map(|(k, c)| format!("{}*T[{k}]", sym_const(c)))
                .collect::<Vec<_>>()
                .join(" + ");
            vec![
                format!(
                    "sum_exprs_by_degree({}, {}) = sum_{{i,j}} c_ij * xs[i]*ys[j]  (a pair_wise_prod sum; c_ij = {}[i+j], checked on every coefficient)",
                    r.name, t.name, r.name
                ),
                format!("    = {terms}"),
                format!(
                    "    T[t] = sum_{{i+j=t}} xs[i]*ys[j],  xs = {} = {},  ys = {} = {}",
                    xs.name,
                    xs.describe(),
                    ys.name,
                    ys.describe()
                ),
            ]
        }
    }
}

/// Render a list of lines with aligned trailing comments.
fn render_lines(lines: &[Line], indent: &str) -> Vec<String> {
    lines
        .iter()
        .map(|line| match line {
            Line::Comment(text) => format!("{indent}// {text}"),
            Line::Code(code, None) => format!("{indent}{code}"),
            Line::Code(code, Some(comment)) => {
                let mut out = format!("{indent}{code}");
                if out.len() < COMMENT_COLUMN {
                    out = format!("{out:<COMMENT_COLUMN$}");
                }
                format!("{out} // {comment}")
            }
        })
        .collect()
}

/// Fold bucket of an identity target.
fn fold_bucket(target: DirectTarget) -> FoldBucket {
    match target {
        DirectTarget::Main => FoldBucket::Main,
        DirectTarget::Selector { bucket, .. } => FoldBucket::Selector(bucket),
    }
}

/// Name of the Yul function of gate identity `j`.
pub(crate) fn identity_function_name(j: usize) -> String {
    format!("q_identity_{j}")
}

/// Names of the structured family functions.
pub(crate) const PERMUTATION_FUNCTION: &str = "q_permutation";
pub(crate) const LOOKUP_FUNCTION: &str = "q_lookups";
pub(crate) const TRASH_FUNCTION: &str = "q_trash";

/// Count helper calls of an identity: `(sum_exprs, sum_exprs_by_degree)`.
fn call_counts(expr: &DirectExpr) -> (usize, usize) {
    let mut counts = (0, 0);
    super::layout::visit_calls(expr, &mut |call| match call {
        DirectCall::SumExprs { .. } => counts.0 += 1,
        DirectCall::SumExprsByDegree { .. } => counts.1 += 1,
    });
    counts
}

/// `function q_identity_<j>(r)` for one gate identity, and its fold site.
pub(crate) fn identity_function(
    program: &DirectQuotientProgram,
    shapes: &HelperShapes,
    identity: &DirectGateIdentity,
    trace_id: Option<u64>,
    call_trace_ids: Option<&[u64]>,
) -> (Vec<String>, FoldSite) {
    let j = identity.global_index;
    let k = program.y_exponent(j);
    let site = FoldSite {
        function: identity_function_name(j),
        label: SiteLabel::Fixed(FoldLabel::Gate {
            gate_index: identity.gate_index,
            polynomial_index: identity.polynomial_index,
        }),
        weight: FoldWeight::Fixed(k),
        bucket: fold_bucket(identity.target),
    };
    let bucket = site.bucket.name();
    let bar =
        "// ---------------------------------------------------------------------------------";
    let mut lines = vec![
        bar.to_string(),
        format!("// identity j = {j}  (of m = {})", program.m),
    ];
    let constraint = if identity.constraint_name.is_empty() {
        String::new()
    } else {
        format!("  constraint \"{}\"", identity.constraint_name)
    };
    lines.push(format!(
        "//   source : cs.gates()[{}] \"{}\" polynomial[{}]{constraint}",
        identity.gate_index, identity.gate_name, identity.polynomial_index
    ));
    lines.push(match identity.target {
        DirectTarget::Main => format!("//   bucket : None = fully evaluated  ->  {bucket}"),
        DirectTarget::Selector { fixed_column, .. } => format!(
            "//   bucket : Some({fixed_column}) = simple selector, fixed column {fixed_column}  ->  {bucket}"
        ),
    });
    lines.push(format!(
        "//   weight : y_pow = y^{k} = Y_POW[m-1-j]  ->  YP_{k}"
    ));
    let (sums, degrees) = call_counts(&identity.expr);
    lines.push(if sums + degrees == 0 {
        "//   form   : Expression tree, node by node".to_string()
    } else {
        format!(
            "//   form   : Expression tree, node by node; {sums} sum_exprs + {degrees} sum_exprs_by_degree helper calls"
        )
    });
    lines.push(bar.to_string());
    lines.push(format!("function {}(r) {{", site.function));
    lines.push(format!(
        "{IND}if iszero(r) {{ leave }}   // never taken (r != 0); keeps this identity a separate function"
    ));
    if let Some(ids) = call_trace_ids {
        // Trace renders: one LOG per helper-call result (direct trace ids,
        // docs/reference/TRACE_VARIABLES.md), recomputed by the same pure call.
        let mut calls = Vec::new();
        super::layout::visit_calls(&identity.expr, &mut |call| calls.push(call));
        for (n, (call, id)) in calls.iter().zip(ids).enumerate() {
            lines.push(format!(
                "{IND}trace_u256({id}, {})   // {}",
                call_text(program, shapes, *call),
                program.call_name(j, n, *call)
            ));
        }
    }
    let mut emitter = TreeEmitter {
        program,
        shapes,
        out: Vec::new(),
        declared: BTreeSet::new(),
    };
    emitter.gen(&identity.expr, 0);
    lines.extend(render_lines(&emitter.out, IND));
    if let Some(id) = trace_id {
        lines.push(format!("{IND}trace_u256({id}, e)"));
    }
    lines.push(format!("{IND}{}", site.statement("e")));
    lines.push("}".to_string());
    (lines, site)
}

/// The dead self call that keeps a helper out of line.
fn barrier(call: &str, first_arg: &str) -> Vec<String> {
    vec![
        format!("{IND}// Never taken (the first operand is a non-zero memory pointer). The dead self call makes"),
        format!("{IND}// the function recursive, which keeps solc from inlining or cloning it per call site."),
        format!("{IND}if iszero({first_arg}) {{ {call} leave }}"),
    ]
}

/// Helper functions for the shapes in use.
pub(crate) fn helper_functions(
    program: &DirectQuotientProgram,
    shapes: &HelperShapes,
) -> Vec<String> {
    let mut out = Vec::new();
    let off = |i: usize, base: &str| {
        if i == 0 {
            format!("mload({base})")
        } else {
            format!("mload(add({base}, {:#x}))", i * WORD_BYTES)
        }
    };
    if !shapes.linear.is_empty() {
        out.push(
            "// sum_exprs(coeffs, exprs)   circuits/src/field/foreign/util.rs sum_exprs"
                .to_string(),
        );
        out.push(
            "//   Rust: exprs.zip(coeffs).map(|(v, b)| Constant(b) * v).fold(0, |acc, e| acc + e)"
                .to_string(),
        );
        out.push("//   = sum_i coeffs[i] * exprs[i] over a VK coefficient run and a limb vector (memory pointers).".to_string());
        out.push("//   Zero coefficients are multiplied, not skipped (the Rust tree drops them; the value is the same).".to_string());
    }
    for len in &shapes.linear {
        let name = shapes.sum_exprs_name(*len);
        out.push(format!("function {name}(coeffs, exprs) -> s {{"));
        out.extend(barrier(&format!("s := {name}(coeffs, exprs)"), "coeffs"));
        out.push(format!("{IND}let r := mload(Q_R_MPTR)"));
        out.push(format!(
            "{IND}s := mulmod({}, {}, r)",
            off(0, "coeffs"),
            off(0, "exprs")
        ));
        for i in 1..*len {
            out.push(format!(
                "{IND}s := addmod(s, mulmod({}, {}, r), r)",
                off(i, "coeffs"),
                off(i, "exprs")
            ));
        }
        out.push("}".to_string());
    }
    if !shapes.by_degree.is_empty() {
        out.push("// sum_exprs_by_degree(coeffs, t)   sum_exprs over pair_wise_prod(xs, ys) after grouping by i+j".to_string());
        out.push("//   = sum_t coeffs[t] * T[t], T = pair_wise_prod_by_degree(xs, ys); valid because the generator checked".to_string());
        out.push("//   on the actual constants that the coefficient of xs[i]*ys[j] depends only on i+j (coeffs[i+j]).".to_string());
    }
    for len in &shapes.by_degree {
        let name = shapes.sum_exprs_by_degree_name(*len);
        out.push(format!("function {name}(coeffs, t) -> s {{"));
        out.extend(barrier(&format!("s := {name}(coeffs, t)"), "coeffs"));
        out.push(format!("{IND}let r := mload(Q_R_MPTR)"));
        out.push(format!(
            "{IND}s := mulmod({}, {}, r)",
            off(0, "coeffs"),
            off(0, "t")
        ));
        for i in 1..*len {
            out.push(format!(
                "{IND}s := addmod(s, mulmod({}, {}, r), r)",
                off(i, "coeffs"),
                off(i, "t")
            ));
        }
        out.push("}".to_string());
    }
    if !shapes.products.is_empty() {
        out.push("// pair_wise_prod_by_degree(t, xs, ys)   circuits/src/field/foreign/util.rs pair_wise_prod".to_string());
        out.push("//   pair_wise_prod(xs, ys) = [xs[i] * ys[j] for i, for j]; writes T[k] = sum_{i+j=k} xs[i] * ys[j]".to_string());
        out.push("//   (every product once, summed by degree). Computed once per gate and pair of vectors.".to_string());
    }
    for (nx, ny) in &shapes.products {
        let name = shapes.pair_wise_prod_name((*nx, *ny));
        out.push(format!("function {name}(t, xs, ys) {{"));
        out.extend(barrier(&format!("{name}(t, xs, ys)"), "t"));
        out.push(format!("{IND}let r := mload(Q_R_MPTR)"));
        out.push(format!("{IND}let s"));
        for k in 0..(nx + ny - 1) {
            let terms: Vec<(usize, usize)> = (0..*nx)
                .filter_map(|i| k.checked_sub(i).filter(|j| *j < *ny).map(|j| (i, j)))
                .collect();
            out.push(format!(
                "{IND}// T[{k}] = {}",
                terms
                    .iter()
                    .map(|(i, j)| format!("xs[{i}]*ys[{j}]"))
                    .collect::<Vec<_>>()
                    .join(" + ")
            ));
            for (n, (i, j)) in terms.iter().enumerate() {
                if n == 0 {
                    out.push(format!(
                        "{IND}s := mulmod({}, {}, r)",
                        off(*i, "xs"),
                        off(*j, "ys")
                    ));
                } else {
                    out.push(format!(
                        "{IND}s := addmod(s, mulmod({}, {}, r), r)",
                        off(*i, "xs"),
                        off(*j, "ys")
                    ));
                }
            }
            if k == 0 {
                out.push(format!("{IND}mstore(t, s)"));
            } else {
                out.push(format!("{IND}mstore(add(t, {:#x}), s)", k * WORD_BYTES));
            }
        }
        out.push("}".to_string());
    }
    let _ = program;
    out
}

/// Body of one structured family function and the fold sites its emitter
/// recorded.
#[derive(Clone, Debug, Default)]
pub(crate) struct FamilyBody {
    pub(crate) lines: Vec<String>,
    pub(crate) sites: Vec<FoldSite>,
}

/// Structured family functions supplied by the orchestrator (bodies are the
/// generator's existing permutation / lookup / trash emitters with the
/// explicit fold).
#[derive(Clone, Debug, Default)]
pub(crate) struct DirectFamilies {
    pub(crate) permutation: Option<FamilyBody>,
    pub(crate) lookup: Option<FamilyBody>,
    pub(crate) trash: Option<FamilyBody>,
    /// Whether the family bodies call `q_pow5`.
    pub(crate) pow5: bool,
}

/// Wrap a family body into `function <name>(r)`.
fn family_function(name: &str, header: &[String], body: &[String]) -> Vec<String> {
    let mut out: Vec<String> = header.iter().map(|h| format!("// {h}")).collect();
    out.push(format!("function {name}(r) {{"));
    out.push(format!(
        "{IND}if iszero(r) {{ leave }}   // never taken (r != 0); keeps this family a separate function"
    ));
    out.extend(indent_block(body, IND));
    out.push("}".to_string());
    out
}

/// Re-indent flat generated Yul lines by brace depth.
pub(crate) fn indent_block(lines: &[String], base: &str) -> Vec<String> {
    let mut depth = 0usize;
    let mut out = Vec::with_capacity(lines.len());
    for line in lines {
        let trimmed = line.trim();
        let opens = trimmed.matches('{').count();
        let closes = trimmed.matches('}').count();
        let leading_close = trimmed.starts_with('}');
        let this_depth = if leading_close {
            depth.saturating_sub(1)
        } else {
            depth
        };
        out.push(format!("{base}{}{trimmed}", IND.repeat(this_depth)));
        depth = (depth + opens).saturating_sub(closes);
    }
    out
}

/// Solidity constant declarations of the direct quotient section.
pub(crate) fn solidity_constants(
    program: &DirectQuotientProgram,
    layout: &DirectLayout,
) -> Vec<String> {
    let mut entries: Vec<(String, String, String)> = Vec::new();
    let hex = |v: usize| format!("{v:#06x}");
    for (s, column) in program.sorted_simple.iter().enumerate() {
        entries.push((
            format!("Q_BUCKET_{s}"),
            hex(layout.buckets[s]),
            format!(
                "simple selector, fixed column {column} (SELECTOR_ACC_MPTR + {:#x})",
                s * WORD_BYTES
            ),
        ));
    }
    entries.push((
        "Q_MAIN_ACC".into(),
        hex(layout.main_acc),
        "fully evaluated identities (None bucket)".into(),
    ));
    entries.push((
        "Q_R_MPTR".into(),
        hex(layout.r_slot),
        "r (FR_MODULUS), stored once by the quotient section".into(),
    ));
    entries.push((
        "Y_POW_MPTR".into(),
        hex(layout.y_pow),
        "Y_POW[k] = y^k at Y_POW_MPTR + 0x20*k".into(),
    ));
    for k in 0..program.m {
        entries.push((
            format!("YP_{k}"),
            hex(layout.y_pow_addr(k)),
            format!("y^{k}"),
        ));
    }
    for (slot, addr) in &layout.slots {
        entries.push((slot.name(), hex(*addr), slot.describe()));
    }
    for (v, vector) in program.vectors.iter().enumerate() {
        let how = if vector.shift.is_some() {
            "view computed once by its first gate".to_string()
        } else if layout.view_copies.iter().any(|(cv, _)| *cv == v) {
            "view copied once (limbs are not adjacent in the evaluation table)".to_string()
        } else {
            format!(
                "adjacent in the evaluation table (= {})",
                vector.slot(0).name()
            )
        };
        entries.push((
            vector.name.clone(),
            hex(layout.vector_addr[v]),
            format!("{}: {how}", vector.describe()),
        ));
    }
    for (t, table) in program.tables.iter().enumerate() {
        entries.push((
            table.name.clone(),
            hex(layout.table_addr[t]),
            format!(
                "{} words: T[t] = sum_{{i+j=t}} {}[i]*{}[j] (gate {})",
                table.len,
                program.vectors[table.xs].name,
                program.vectors[table.ys].name,
                table.gate_index
            ),
        ));
    }
    for (r, run) in program.runs.iter().enumerate() {
        let kind = match run.kind {
            RunKind::Linear => "sum_exprs coefficients",
            RunKind::ByDegree => "pair_wise_prod coefficients by degree",
        };
        entries.push((
            run.name.clone(),
            hex(layout.run_addr[r]),
            format!("VK table, {} words: {kind}", run.values.len()),
        ));
    }
    for (i, value) in program.pool.iter().enumerate() {
        entries.push((
            format!("QC_{i}"),
            hex(layout.pool_addr[i]),
            format!("VK table: {}", sym_const(value)),
        ));
    }
    for value in small_constants(program) {
        entries.push((
            small_const_name(&value),
            format!("{:#x}", fe_to_u256::<Fq>(&value)),
            "identity constant (literal)".into(),
        ));
    }
    let width = entries.iter().map(|(n, _, _)| n.len()).max().unwrap_or(0);
    let mut out = vec![
        "// ----------------------------------------------------------------------".to_string(),
        "// Direct quotient section layout (QuotientLowering::Direct).".to_string(),
        "// ----------------------------------------------------------------------".to_string(),
    ];
    for (name, value, comment) in entries {
        out.push(format!(
            "uint256 internal constant {name:<width$} = {value}; // {comment}"
        ));
    }
    out
}

/// Small (non-pooled) constants used by the identities, deduplicated.
pub(crate) fn small_constants(program: &DirectQuotientProgram) -> Vec<Fq> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for identity in &program.gates {
        let mut stack = vec![&identity.expr];
        while let Some(expr) = stack.pop() {
            match expr {
                DirectExpr::Constant(c) => {
                    if !is_pooled(c) && seen.insert(c.to_repr()) {
                        out.push(*c);
                    }
                }
                DirectExpr::Negated(inner) => stack.push(inner),
                DirectExpr::Sum(lhs, rhs) | DirectExpr::Product(lhs, rhs) => {
                    stack.push(rhs);
                    stack.push(lhs);
                }
                _ => {}
            }
        }
    }
    for v in &program.vectors {
        if let Some((_, shift)) = v.shift {
            if !is_pooled(&shift) && seen.insert(shift.to_repr()) {
                out.push(shift);
            }
        }
    }
    out
}

/// Rendered direct quotient Yul: function definitions (placed at the top of
/// the verifier's assembly block, before `let r := FR_MODULUS`, because Yul
/// forbids a parameter named `r` where the outer `r` is visible), the
/// section block (placed at the quotient position), and the fold sites and
/// section calls for the fold check.
#[derive(Clone, Debug, Default)]
pub(crate) struct DirectYul {
    pub(crate) functions: Vec<String>,
    pub(crate) section: Vec<String>,
    pub(crate) folds: FoldRecord,
}

/// The direct quotient Yul: identity / helper / family function definitions
/// and the section statements that call them.
pub(crate) fn quotient_block(
    program: &DirectQuotientProgram,
    layout: &DirectLayout,
    families: &DirectFamilies,
    trace_base: Option<u64>,
) -> DirectYul {
    let shapes = program.helper_shapes();
    let mut functions = vec![
        "// ===============================================================".to_string(),
        "// Direct quotient lowering: identity functions, helpers and argument families."
            .to_string(),
        "// Called by the batched identity numerator section below (see its header).".to_string(),
        "// ===============================================================".to_string(),
    ];
    let mut out = vec![
        "// ===============================================================".to_string(),
        "// Batched identity numerator / linearization target (QuotientLowering::Direct).".to_string(),
        "//".to_string(),
        "// Rust source of truth:".to_string(),
        "//   proofs/src/plonk/mod.rs::partially_evaluate_identities: identity stream in the order".to_string(),
        format!(
            "//     gates -> permutation -> lookups -> trash, m = {} identities ({} gate, {} permutation, {} lookup, {} trash)",
            program.m,
            program.gates.len(),
            program.permutation.count,
            program.lookup.count,
            program.trash.count
        ),
        "//   proofs/src/plonk/linearization/verifier.rs::compute_linearization_commitment:".to_string(),
        "//     identity j carries y^(m-1-j); Some(col) identities go to the selector bucket of col, None".to_string(),
        "//     identities are summed and negated into expected_eval (QUOTIENT_EVAL_MPTR).".to_string(),
        "// Every gate identity is one function q_identity_<j> (header: j, source gate/polynomial, bucket,".to_string(),
        "// weight) whose body is the gate's Expression tree written node by node; sub-trees recognised as".to_string(),
        "// sum_exprs / pair_wise_prod sums are helper calls, each preceded by its terms. At code".to_string(),
        "// generation, the lowered gate IR was checked against Expression::evaluate at random points".to_string(),
        "// (IR translation validation, not this Yul), and every fold below (gate functions and family".to_string(),
        "// loops) was checked against the identity manifest: each j once, weight Y_POW[m-1-j], its bucket.".to_string(),
        "// ===============================================================".to_string(),
        "{".to_string(),
    ];
    let trace_ids = trace_base.map(|_| {
        program
            .trace_ids()
            .expect("direct trace ids are validated when the plan is built")
    });
    let mut folds = FoldRecord::default();
    let mut defs: Vec<String> = Vec::new();
    for (index, identity) in program.gates.iter().enumerate() {
        let trace_id = trace_base.map(|base| base + identity.global_index as u64);
        let call_ids = trace_ids.as_ref().map(|ids| ids.calls[index].as_slice());
        let (lines, site) = identity_function(program, &shapes, identity, trace_id, call_ids);
        defs.extend(lines);
        defs.push(String::new());
        folds.sites.push(site);
    }
    defs.extend(helper_functions(program, &shapes));
    if families.pow5 {
        defs.push("// x^5 (Poseidon S-box) used by the structured family bodies.".to_string());
        defs.push("function q_pow5(x) -> z {".to_string());
        defs.push(format!("{IND}let q_r := mload(Q_R_MPTR)"));
        defs.push(format!("{IND}let x2 := mulmod(x, x, q_r)"));
        defs.push(format!("{IND}z := mulmod(x, mulmod(x2, x2, q_r), q_r)"));
        defs.push("}".to_string());
    }
    let range = |r: super::IdentityRange| {
        format!(
            "identities j = {}..{} (of m = {})",
            r.base,
            r.base + r.count - 1,
            program.m
        )
    };
    let mut family_sites = |name: &str, body: &FamilyBody| {
        folds.sites.extend(body.sites.iter().cloned().map(|site| FoldSite {
            function: name.to_string(),
            ..site
        }));
    };
    if let Some(body) = &families.permutation {
        family_sites(PERMUTATION_FUNCTION, body);
        defs.push(String::new());
        defs.extend(family_function(
            PERMUTATION_FUNCTION,
            &[
                format!("{}: permutation argument (proofs/src/plonk/permutation.rs), None bucket -> Q_MAIN_ACC", range(program.permutation)),
                "generator's structured permutation loop; each identity folds main += Y_POW[m-1-j] * e".to_string(),
            ],
            &body.lines,
        ));
    }
    if let Some(body) = &families.lookup {
        family_sites(LOOKUP_FUNCTION, body);
        defs.push(String::new());
        defs.extend(family_function(
            LOOKUP_FUNCTION,
            &[
                format!("{}: LogUp lookups (proofs/src/plonk/logup.rs), None bucket -> Q_MAIN_ACC", range(program.lookup)),
                "generator's structured lookup emitter; each identity folds main += Y_POW[m-1-j] * e".to_string(),
            ],
            &body.lines,
        ));
    }
    if let Some(body) = &families.trash {
        family_sites(TRASH_FUNCTION, body);
        defs.push(String::new());
        defs.extend(family_function(
            TRASH_FUNCTION,
            &[
                format!("{}: trash argument (proofs/src/plonk/trash.rs), None bucket -> Q_MAIN_ACC", range(program.trash)),
                "generator's structured trash emitter; each identity folds main += Y_POW[m-1-j] * e".to_string(),
            ],
            &body.lines,
        ));
    }
    functions.extend(defs);

    // ---------------- section statements ----------------
    let mut sec: Vec<String> = vec![
        "let y := mload(Y_MPTR)".to_string(),
        "// r is stored once and read back below, so that it is a run-time value inside the section"
            .to_string(),
        "// (a DUP / one mload) rather than a 32-byte literal re-materialised at every use.".to_string(),
        "mstore(Q_R_MPTR, r)".to_string(),
    ];
    let nb = program.sorted_simple.len();
    let buckets_end = layout.buckets.last().map(|b| b + WORD_BYTES);
    if nb > 0 && buckets_end == Some(layout.main_acc) {
        sec.push(format!(
            "// Selector buckets Q_BUCKET_0..{} and Q_MAIN_ACC (adjacent) start at zero.",
            nb - 1
        ));
        sec.push(format!(
            "for {{ let q_o := 0 }} lt(q_o, {:#x}) {{ q_o := add(q_o, 0x20) }} {{ mstore(add(Q_BUCKET_0, q_o), 0) }}",
            (nb + 1) * WORD_BYTES
        ));
    } else {
        if nb > 0 {
            sec.push("// Selector buckets start at zero.".to_string());
            sec.push(format!(
                "for {{ let q_o := 0 }} lt(q_o, {:#x}) {{ q_o := add(q_o, 0x20) }} {{ mstore(add(Q_BUCKET_0, q_o), 0) }}",
                nb * WORD_BYTES
            ));
        }
        sec.push("mstore(Q_MAIN_ACC, 0)".to_string());
    }
    if !layout.view_copies.is_empty() {
        sec.push("// Limb views: these vectors' limbs are not adjacent in the evaluation table, so they are".to_string());
        sec.push(
            "// copied once into adjacent words (the other vectors are read in place).".to_string(),
        );
        for (v, runs) in &layout.view_copies {
            let vector = &program.vectors[*v];
            for run in runs {
                let dst = if run.view_word == 0 {
                    vector.name.clone()
                } else {
                    format!("add({}, {:#x})", vector.name, run.view_word * WORD_BYTES)
                };
                let src = vector.slot(run.view_word).name();
                let last = vector.slot(run.view_word + run.words - 1).short();
                if run.words == 1 {
                    sec.push(format!(
                        "mstore({dst}, mload({src}))   // {}[{}] = {}",
                        vector.name,
                        run.view_word,
                        vector.slot(run.view_word).short()
                    ));
                } else {
                    sec.push(format!(
                        "mcopy({dst}, {src}, {:#x})   // {}[{}..{}] = {}..{last}",
                        run.words * WORD_BYTES,
                        vector.name,
                        run.view_word,
                        run.view_word + run.words - 1,
                        vector.slot(run.view_word).short()
                    ));
                }
            }
        }
    }
    if let Some(ids) = &trace_ids {
        for (v, vector) in program.vectors.iter().enumerate() {
            if vector.shift.is_none() {
                trace_vector(&mut sec, vector, ids.vectors[v]);
            }
        }
    }
    sec.push("let q_r := mload(Q_R_MPTR)".to_string());
    sec.push(
        "// Y_POW[k] = y^k for k in [0, m)   (Rust: y_pow = ONE; ...; y_pow *= y).".to_string(),
    );
    sec.push("{".to_string());
    sec.push(format!("{IND}let q_y_pow := 1"));
    sec.push(format!(
        "{IND}for {{ let q_p := Y_POW_MPTR }} lt(q_p, {:#x}) {{ q_p := add(q_p, 0x20) }} {{",
        layout.y_pow_addr(program.m)
    ));
    sec.push(format!("{IND}{IND}mstore(q_p, q_y_pow)"));
    sec.push(format!("{IND}{IND}q_y_pow := mulmod(q_y_pow, y, q_r)"));
    sec.push(format!("{IND}}}"));
    sec.push("}".to_string());
    sec.push("// Identities in Rust stream order.".to_string());
    let mut last_gate = None;
    for op in &layout.schedule {
        match *op {
            SectionOp::ShiftView { vector, .. } => {
                let v = &program.vectors[vector];
                let (base, shift) = v.shift.expect("shift view");
                gate_banner(program, &mut sec, &mut last_gate, op, layout);
                sec.push(format!(
                    "// {} = {}: shifted limbs x_i + shift (as norm.rs `shifted_x`), shift = {}",
                    v.name,
                    v.describe(),
                    sym_const(&shift)
                ));
                sec.push(format!(
                    "for {{ let q_i := 0 }} lt(q_i, {:#x}) {{ q_i := add(q_i, 0x20) }} {{",
                    v.len * WORD_BYTES
                ));
                sec.push(format!(
                    "{IND}mstore(add({}, q_i), addmod(mload(add({}, q_i)), {}, q_r))",
                    v.name,
                    program.vectors[base].name,
                    const_yul(program, &shift)
                ));
                sec.push("}".to_string());
                if let Some(ids) = &trace_ids {
                    trace_vector(&mut sec, v, ids.vectors[vector]);
                }
            }
            SectionOp::ProductTable { table } => {
                gate_banner(program, &mut sec, &mut last_gate, op, layout);
                let t = &program.tables[table];
                let (xs, ys) = (&program.vectors[t.xs], &program.vectors[t.ys]);
                sec.push(format!(
                    "// {} = pair_wise_prod({}, {}) summed by i+j, shared by the polynomials of gate {}",
                    t.name, xs.name, ys.name, t.gate_index
                ));
                sec.push(format!(
                    "{}({}, {}, {})",
                    shapes.pair_wise_prod_name((xs.len, ys.len)),
                    t.name,
                    xs.name,
                    ys.name
                ));
                if let Some(ids) = &trace_ids {
                    for k in 0..t.len {
                        sec.push(format!(
                            "trace_u256({}, mload({}))   // {}[{k}]",
                            ids.tables[table] + k as u64,
                            word_ptr(&t.name, k),
                            t.name
                        ));
                    }
                }
            }
            SectionOp::Identity { index } => {
                gate_banner(program, &mut sec, &mut last_gate, op, layout);
                sec.push(folds.call(&identity_function_name(program.gates[index].global_index)));
            }
        }
    }
    if families.permutation.is_some() {
        sec.push(folds.call(PERMUTATION_FUNCTION));
    }
    if families.lookup.is_some() {
        sec.push(folds.call(LOOKUP_FUNCTION));
    }
    if families.trash.is_some() {
        sec.push(folds.call(TRASH_FUNCTION));
    }
    sec.push("// Rust: `None => expected_eval -= eval`.".to_string());
    sec.push("mstore(QUOTIENT_EVAL_MPTR, addmod(0, sub(q_r, mload(Q_MAIN_ACC)), q_r))".to_string());
    out.extend(indent_block(&sec, IND));
    out.push("}".to_string());
    DirectYul {
        functions,
        section: out,
        folds,
    }
}

/// Comment line naming the gate before its first section statement.
fn gate_banner(
    program: &DirectQuotientProgram,
    sec: &mut Vec<String>,
    last_gate: &mut Option<usize>,
    op: &SectionOp,
    _layout: &DirectLayout,
) {
    let gate = match *op {
        SectionOp::Identity { index } => program.gates[index].gate_index,
        SectionOp::ProductTable { table } => program.tables[table].gate_index,
        SectionOp::ShiftView { gate, .. } => gate,
    };
    if *last_gate != Some(gate) {
        *last_gate = Some(gate);
        if let Some(identity) = program.gates.iter().find(|g| g.gate_index == gate) {
            sec.push(format!("// cs.gates()[{gate}] \"{}\"", identity.gate_name));
        }
    }
}

/// `NAME` or `add(NAME, 0x..)` for word `k` of a named memory vector.
fn word_ptr(name: &str, k: usize) -> String {
    if k == 0 {
        name.to_string()
    } else {
        format!("add({name}, {:#x})", k * WORD_BYTES)
    }
}

/// Trace every word of a limb vector (trace renders only).
fn trace_vector(sec: &mut Vec<String>, vector: &super::LimbVector, base_id: u64) {
    for i in 0..vector.len {
        sec.push(format!(
            "trace_u256({}, mload({}))   // {}[{i}]",
            base_id + i as u64,
            word_ptr(&vector.name, i),
            vector.name
        ));
    }
}
