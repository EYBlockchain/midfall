/-
  Midfall.Common.Except

  OBJ.8 step 1 (PLAN-V3): THE TOTAL PROJECTION OF AN `Except` ALONG A `Bool` PROOF, and the
  equation that makes it usable as a clause.

  WHY THIS FILE EXISTS. `Render.Valid.generated` (`LoweringV2/Statements.lean`) says the
  render's plan, quotient blocks and model are the three fields of the value that
  `generateAll` returns for the render's own inputs. `generateAll` returns an
  `Except Fault GenOut`, and the generator run at a deployment is a computation the KERNEL
  cannot perform - `generateVerifierFromPlan` is VM-reducible and not kernel-reducible
  (`Instances/PoseidonV2.lean` gap (c): `by decide` and `rfl` on `poseidonModel.isOk = true`
  both get stuck at the `match`). So the clause cannot be discharged by handing the kernel a
  reduction; it is discharged by projecting the run along a proof that the run does not fail,
  and citing the projection back. That is exactly what these two names give:

    h : gen.isOk = true            by `native_decide`, i.e. by RUNNING the ported generator
    gen = .ok (gen.getOk h)        `eq_ok_getOk`, so the run IS its own projection
    (gen.getOk h).plan = R.plan    `rfl`, once R.plan is defined as that projection

  The motive is NON-dependent in the scrutinee - the proof argument is about a `Bool` and not
  about the value - which is the one thing `poseidonModelVal`'s
  `match h : poseidonModel with ... False.elim ...` lacks and the reason that older route had
  to spell out the error arm by hand. `poseidonModelVal` stays where it is (other cards' cones
  cite it); this is the generic form, and OBJ.8 step 3 uses it.

  PROVENANCE. Both texts are the scratch definitions the card's Needs line names
  (docs/plans/V3-evidence/lean/object/ObjectV3Full.lean:123-129, which records them as
  typechecking with axioms `propext`), landed in the library proper rather than left in the
  evidence directory. `Midfall/Common/` is the right home: it sits below both the generator and
  the statement surface, it states no theorem about either, and D-P17's confinement of
  `native_decide` to `Midfall/Instances/` is untouched - there is no `native_decide` in this
  file at all, and the two proofs are `simp`/`cases` over a `Bool`.

  WITNESS AND FALSIFIER (W15). Witness: `#print axioms` below lists `propext` and nothing
  else, and `getOk_ok` / `eq_ok_getOk` are the two equations a caller needs. Falsifier: the
  `.error` arm is not defaulted - `not_isOk_getOk` shows a failing run carries no `isOk`
  proof at all, so there is nothing to project.
-/

namespace Except

/-- **THE `.ok` VALUE OF AN `Except` WHOSE `isOk` IS `true`.** The error arm is unreachable
    and is closed by `simp` on the definition of `isOk`, not by a default value: nothing is
    invented for a run that fails. -/
def getOk {ε α : Type} : (e : Except ε α) → e.isOk = true → α
  | .ok a, _ => a
  | .error _, h => by simp [Except.isOk, Except.toBool] at h

/-- **THE PROJECTION ROUND-TRIPS.** A run whose `isOk` is `true` IS `.ok` of its own
    projection. This is the equation `Render.Valid.generated` is discharged with. -/
theorem eq_ok_getOk {ε α : Type} (e : Except ε α) (h : e.isOk = true) : e = .ok (e.getOk h) := by
  cases e with
  | ok a => rfl
  | error _ => simp [Except.isOk, Except.toBool] at h

/-- THE WITNESS AT THE SHAPE A CALLER USES: projecting a run that is `.ok a` recovers `a`. -/
theorem getOk_ok {ε α : Type} (a : α) (h : (Except.ok a : Except ε α).isOk = true) :
    (Except.ok a : Except ε α).getOk h = a := rfl

/-- THE FALSIFIER: a failing run carries no `isOk` proof, so there is nothing to project.
    Stated as the negation rather than left as an omission, so the gate sees the arm is closed
    and not defaulted. -/
theorem not_isOk_getOk {ε α : Type} (e : ε) : ¬ ((Except.error e : Except ε α).isOk = true) := by
  simp [Except.isOk, Except.toBool]

end Except

#print axioms Except.getOk
#print axioms Except.eq_ok_getOk
#print axioms Except.getOk_ok
#print axioms Except.not_isOk_getOk
