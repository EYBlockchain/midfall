import RunLib
set_option autoImplicit false
/-! The three measurements of item 3, on formal/fixtures/conformance/poseidon. -/

-- (A) the tree as it is, at a REAL codec and the REAL commitments: raw import, tree grouping
#eval RefRun.run "A. raw cs (Rotation.value), tree grouping" Midfall.Instances.PoseidonFixture.poseidonCs false false

-- (B) rotation repaired (S1), tree grouping
#eval RefRun.run "B. canonical rotations, tree grouping (kzgCommitBeq by value)" RefRun.csCanon false false

-- (C) both repairs: THE REFERENCE GATE
#eval RefRun.run "C. canonical rotations + slot grouping" RefRun.csCanon true true
