# Moonlight wrap verifier specification

`Halo2VerifierSpec.tex` is a line-faithful specification of the two contracts
under `fixtures/moonlight-wrap/`:

- `Halo2Verifier.sol` — the circuit-specialised Halo2/KZG verifier (4,130 lines)
- `Halo2VerifyingKey.sol` — the data-only verifying-key contract (695 lines)

It documents every guard, constant, loop bound, memory address, precompile call
and revert condition in those artifacts, gives the algebraic relations they
compute, and quotes the code with line references. Assessment call-outs
(`Finding N`) record what a reviewer should act on or consciously accept; they
are consolidated in the assessment and critique sections.

The empirical results it reports come from
`tests/moonlight_wrap_fixture_adversarial.rs`, which replays these exact
artifacts under revm.

## Building

Needs a TeX distribution with `latexmk` (TeX Live, MacTeX or MiKTeX). No
non-default packages: everything used ships with `texlive-latex-recommended`
plus `algorithm`/`algorithmic` and `listings`.

```sh
cd docs/spec
latexmk -pdf Halo2VerifierSpec.tex
```

or, without latexmk (three passes, for the table of contents and cross
references):

```sh
pdflatex Halo2VerifierSpec.tex && pdflatex Halo2VerifierSpec.tex && pdflatex Halo2VerifierSpec.tex
```

## Checking the excerpts

The document quotes 130 code excerpts with explicit line ranges. `check_excerpts.py`
re-verifies every one of them against `fixtures/moonlight-wrap/`, so a re-render that
moves lines is detected rather than silently mis-cited:

```sh
python3 docs/spec/check_excerpts.py
```

It needs no TeX and no toolchain. Exit status is non-zero if any excerpt contains a
line that does not appear in the range it cites.

## Scope and staleness

The document describes the `fixtures/moonlight-wrap/` render, not the older
`^0.8.24` render under `deployments/sepolia/moonlight-wrap/`. The two share a
proof layout but differ in the pragma, the typed error taxonomy and part of the
quotient-program encoding, so line numbers do not transfer.

Like the fixtures themselves, this is a snapshot. Re-rendering the verifier
invalidates the line references; the structural description survives, the
citations do not.
