# CERT.6 constant-text leaves — measured state

## What is proved

### `String.splitOn` at a newline (`formal/Midfall/Generator/SplitOnLines.lean`)

The toolchain has no inverse lemma for the legacy `String.splitOn`, which is
why the earlier residual could not even state a line decomposition. That gap
is now closed for the newline separator:

- `splitOn_newline_eq_splitToList`: `s.splitOn "\n" = s.splitToList (· == '\n')`,
  proved by simulating the byte-level `splitOnAux` against the Batteries
  `splitAux` characterization.
- `intercalate_splitOn_newline`: `String.intercalate "\n" (s.splitOn "\n") = s`.
- `splitOn_newline_ne_nil`, `splitOn_newline_no_nl`: split pieces are nonempty
  as a list and contain no embedded newline.
- `splitOn_intercalate_newline`: for a nonempty line list with no embedded
  newline, `(String.intercalate "\n" l).splitOn "\n" = l`.

### Generic template chunks (`formal/Midfall/Generator/ConstLines.lean`)

`renderConstants` is transcribed into literal chunks, one chunk per `++`
segment, with a named `litN` definition for every closed literal so the
transcription is inspectable without reducing the whole template:

- `vkSeg` / `qeSeg` / `fixedSeg` / `accSeg` / `buildSeg` / `directSeg`, and the
  matching `vkText` / `qeText` / `fixedText` / `accText` / `buildText` /
  `directText` strings.
- `vk_eq`, `qe_eq`, `fixed_eq`, `acc_eq`, `build_eq`, `direct_eq`: each arm's
  text is the `String.join` of its chunks. The optional VK, quotient, and
  accumulator arms and the arbitrary `quotientDirect` arm are all present.
- `linesOfChunks` / `prepend`: merge chunk splits on newlines while joining the
  boundary line.
- `linesOfChunks_spec`: `String.intercalate "\n" (linesOfChunks cs)` is the
  `String.join` of the chunk texts.
- `linesOfChunks_no_nl`: every produced line is newline-free.
- `splitOn_newline_chunks`: splitting the chunk concatenation at newlines
  returns exactly `linesOfChunks cs`.
- `renderConstantsLines`, `renderConstantsLines_ne_nil`,
  `renderConstantsLines_no_nl`: the named generic line list for the full
  `renderConstantsChunks` template.

### Reduced residual interface (`Generator/ConstTextResidual.lean`)

`ConstTextWitness` no longer carries an arbitrary `lines` field or a separate
`split_eq`; it now names the generic list and only asks for:

```lean
render_eq :
  renderConstants (partialCtxOfVerifier m) =
    String.intercalate "\n" (renderConstantsLines (partialCtxOfVerifier m))
lines_literal :
  (renderConstantsLines (partialCtxOfVerifier m)).all LineLiteral = true
table_eq :
  (constTableOf m == expectedConsts pv m) = true
```

`split_eq_of_render_eq` derives the split equality from `render_eq` using the
proved `splitOn_intercalate_newline`; `constLinesLiteral_of_witness` and
`constTable_of_witness` are the unchanged reductions to the two targets.

### Concrete instance

`formal/Midfall/Instances/ConstsCert6.lean` inhabits the reduced witness at the
tracked poseidon fixture (`poseidonConstTextWitness`); `render_eq`,
`lines_literal`, and `table_eq` are closed by `native_decide` on the closed
render. The F1 concrete gates remain in `Instances/CertMeasure.lean`.

## Exact remaining generic obligations

The generic target statements in `Generator/Certified.lean` are unchanged:

```lean
prog_constLinesLiteral : constLinesLiteral (renderOf gi o).model = true
prog_constTable :
  (constTableOf (renderOf gi o).model ==
    expectedConsts (renderOf gi o).pv (renderOf gi o).model) = true
```

Two obligations remain, both named rather than hidden:

1. **Template reassociation (`render_eq`).** `renderConstants` is one
   left-associated `++` chain. The chunk transcription is definitionally the
   same atom sequence, but closing the equality by `rfl` forces the kernel to
   normalise the full string chain. Measured: `fixed_eq` alone takes about 46 s
   with `maxHeartbeats 20000000`; the full template `rfl` exceeds a five-minute
   budget and was stopped. This is a kernel-reduction cost, not a missing
   mathematical fact; the named `litN` definitions give a route to a
   reflection/`conv` proof that rewrites literals to `litN` without normalising
   the string contents. The target was not weakened to assume `render_eq`.
2. **Per-line `LineLiteral` / `solConstantLine?` round-trips.** `LineLiteral`
   calls `String.splitOn "uint256 internal constant "`, a *multi-character*
   separator, for which the toolchain still has no append/inverse lemma (the
   new `SplitOnLines` file covers the one-character `"\n"` case). The same
   applies to the `=` / `;` fields of `solConstantLine?` and to
   `natOfLiteral`'s inversion of `toString` / `hexFilter` / `hexPaddedFilter`.
   The concrete poseidon and F1 instances discharge these by `native_decide`;
   a generic proof needs that multi-character split lemma first.

No target statement was weakened, no row/root hypothesis was added, and the
`prog_noDirect` exclusion of the arbitrary `quotientDirect` arm remains the
only option-level hypothesis needed.

## Build

`lake build Midfall.Generator.SplitOnLines Midfall.Generator.ConstLines
Midfall.Generator.ConstTextResidual Midfall.Instances.ConstsCert6
Midfall.Generator.Certified` is green.
