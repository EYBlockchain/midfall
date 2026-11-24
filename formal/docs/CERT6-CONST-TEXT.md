# CERT.6 constant-text leaves — measured state

## What is proved

### Character lemmas (`formal/Midfall/Generator/ConstText.lean`)

- `toString_chars`: every character of `toString n` is a decimal digit.
- `hexDigits_chars` / `hexFilter_*` / `hexPaddedFilter_*`: the rendered
  `0x` forms start with `0x`, have a non-empty body, and that body contains
  only lowercase hex digits (`0-9`, `a-f`).
- `printPtr_integer_nonneg`: `printPtr (Value.integer i)` for `0 ≤ i` is
  `hexFilter i.toNat`.
- `printPtr_valueFromNat`, `printPtr_memory_add`, `printPtr_calldata_sub`:
  the concrete numeric pointer forms used by `renderConstants` are
  `hexFilter` of a Nat, including the word-addressed `Ptr.add`/`Ptr.sub`
  shapes.

These are uniform in the numeric fields; none of them depends on a concrete
model.

### Concrete instance

- `formal/Midfall/Instances/ConstsCert6.lean`
  - `poseidon_constLinesLiteral`:
    `LoweringV3.constLinesLiteral poseidonM = true`.
  - `poseidon_constTable`:
    `LoweringV2.constTableOf poseidonM == LoweringV3.expectedConsts poseidonPv poseidonM`.
- `formal/Midfall/Instances/CertMeasure.lean`
  - `f1_constLinesLiteral`: the same line predicate at the F1 render.
  - `f1_constTable`: the same table equality at F1.

Both concrete instances are `native_decide` (the instance-confinement rule;
D-P17/D-P20). The pre-existing `ConstsKats.coherent_ok` `#eval` already
printed the poseidon coincidence; the two theorems above are the kernel
statements, not a new computation.

## Exact generic residual

The generic targets in `Generator/Certified.lean` remain:

```lean
prog_constLinesLiteral : constLinesLiteral (renderOf gi o).model = true
prog_constTable :
  (constTableOf (renderOf gi o).model ==
    expectedConsts (renderOf gi o).pv (renderOf gi o).model) = true
```

The missing generic step is the **line decomposition of `renderConstants`**,
not any character-level fact:

1. `constLinesLiteral` and `constTableOf` both call
   `(renderConstants (partialCtxOfVerifier m)).splitOn "\n"`.
   `renderConstants` is one large concatenation of template text and
   interpolations. There is no lemma in the tree that writes it as
   `String.intercalate "\n" lines`, and `String.splitOn` on a symbolic string
   does not reduce (it is defined through `splitOnAux`).
2. A generic proof therefore needs a proof-only
   `renderConstants_lines` (or equivalent `splitOn`/append) lemma and a
   per-line `solConstantLine?` round-trip. The latter must show
   `natOfLiteral` inverts both `toString n` (decimal) and
   `hexFilter`/`hexPaddedFilter pad n` (lowercase hex), including the leading
   spaces, `=` and `;` trimming.
3. The four optional template arms are:
   - `expectedVkCodehash` `some`/`none`;
   - `quotientExternal` × `expectedQuotientCodehash`;
   - `expectedHasAccumulator`;
   - `quotientDirect`.
   The first three emit only the fixed-format lines covered by the character
   lemmas; the `quotientDirect` arm emits arbitrary `qdirect.constants` text
   and is excluded by the already-proved `prog_noDirect hg hs`
   (`quotientDirect.isNone = true`). No target proof was weakened to assume
   this: the generic target still has to consume `prog_noDirect`.

`native_decide` cannot close the generic statement because `m`/`pv` contain
free variables; the concrete F1 and poseidon instances above are the
kernel-checked witnesses, not a substitution for the generic line lemma.

## Build

`lake build Midfall.Generator.ConstText Midfall.Instances.ConstsCert6
Midfall.Instances.CertMeasure Midfall.Generator.Certified` is green.
`SupportedInput`, `ValidV3`, rows/root and the target statements are
untouched.
