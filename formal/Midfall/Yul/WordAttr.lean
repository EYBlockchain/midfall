/-
  Midfall.Yul.WordAttr

  MAKES `yul_word` A REAL SIMP ATTRIBUTE (ticket WORDATTR, the follow-up T3.5 measured and
  reported instead of hacking around).

  WHY A SECOND FILE EXISTS AT ALL. `Lean.Meta.registerSimpAttr` may only run during module
  initialization, and an `initialize` block runs when its module is IMPORTED, not while the
  module itself is being elaborated. So the attribute cannot be registered and applied in the
  same file: Lean answers `Unknown attribute` for the tagging command. The registration
  therefore lives here, in a module imported BEFORE the tagging site, which is the block at
  the bottom of `Midfall/Yul/Word.lean`. That is a property of the mechanism and not a
  choice: `Word.lean`'s declarations, statements and proofs are untouched.

  WHAT THIS BUYS OVER THE `macro_rules` PAIR IN `Word.lean`. A macro matches syntax, so the
  pair only fires on the two shapes it spells out. An attribute is resolved by `simp` itself,
  so all of these now work (the first two did not):

    ```lean
    simp only [Midfall.Yul.Word.yul_word] at h
    simp only [extra1, Midfall.Yul.Word.yul_word]
    simp [Midfall.Yul.Word.yul_word] at h ⊢
    ```

  i.e. a location clause, and any position in the argument list, which is what GEN.1 and the
  M6 rows need. The `macro_rules` pair is left in place: it is what T3.5's existing call sites
  elaborate through, and it expands to exactly the same 29 lemmas this attribute carries, so the
  two spellings cannot drift apart in meaning. Nothing here is `@[simp]` globally - a projection
  set of this size, always on, would rewrite memory terms in files that were proved without it
  (the reason T3.5 gave for keeping the set named rather than global).

  The lemmas themselves are in `Midfall/Yul/Word.lean`; see that file's header for what is in
  the set. To add a lemma to the set, tag it `@[Midfall.Yul.Word.yul_word]` in the file that
  declares it (that file must import this one) - do not append to the `macro_rules` list.
-/
import Lean

/-- **The `yul_word` simp attribute.** Registering the name `Midfall.Yul.Word.yul_word` as a
    custom simp set, so that `simp`/`simp only` resolve it as a lemma source anywhere a simp
    argument is allowed - including under an `at` clause and in a non-first position, which the
    `macro_rules` pair in `Midfall/Yul/Word.lean` cannot reach. The lemmas are tagged with it at
    the bottom of that file. -/
initialize yulWordExt : Lean.Meta.SimpExtension ←
  Lean.Meta.registerSimpAttr `Midfall.Yul.Word.yul_word
    "the Yul word/memory simp set: Boolean words, touchMemory projections, read-over-write"
