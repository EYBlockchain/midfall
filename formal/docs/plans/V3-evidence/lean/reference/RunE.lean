import RunLib
set_option autoImplicit false
/-! More falsifiers, and the acceptance check as a computation. -/

-- (E) one bit of one evaluation flipped (byte 1008 = low byte of the 4th scalar read after x)
#eval RefRun.run "E. both repairs, proof byte 1008 flipped" RefRun.csCanon true false RefRun.deltaReal (RefRun.flipByte 1008)

-- (F) one bit of the LAST byte flipped (inside pi, the last G1 read): the point no longer decodes
#eval RefRun.run "F. both repairs, proof byte 2639 flipped" RefRun.csCanon true false RefRun.deltaReal (RefRun.flipByte 2639)

-- (G) DualMSM.check runs in the VM at the constructed pairing. The Filecoin trapdoor is unknown, so
--     at an arbitrary s the honest proof must be REJECTED; with the true s it would be accepted.
#eval RefRun.run "G. both repairs, final check at a wrong trapdoor s=5" RefRun.csCanon true false RefRun.deltaReal id (some 5)
