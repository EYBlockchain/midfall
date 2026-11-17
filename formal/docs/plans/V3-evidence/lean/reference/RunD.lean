import RunLib
set_option autoImplicit false
/-! Falsifiers for the reference gate: each must report MISMATCH / a fault. -/

-- (D) both repairs but the deployment's placeholder delta := 2 (E-4 / G-5 / H-7)
#eval RefRun.run "D. both repairs, delta := 2 (the placeholder)" RefRun.csCanon true false (2 : Midfall.Fr Midfall.Yul.blsR)

-- the value of Fr::DELTA the gate uses, and its order facts
#eval (RefRun.frHex RefRun.deltaReal,
       RefRun.deltaReal ^ ((Midfall.Yul.blsR - 1) / 2 ^ 32) == 1,
       RefRun.deltaReal ^ ((Midfall.Yul.blsR - 1) / 2 ^ 32 / 3) == 1)
