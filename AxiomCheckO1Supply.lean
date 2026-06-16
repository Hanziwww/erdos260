import Erdos260.O1SupplyAtlas

open Erdos260.O1SupplyAtlas

-- Section A: cumulative spatial displacement (AQ.4)
#print axioms cumGap_succ
#print axioms cumGap_eq_sum

-- Section B: affine phase charts + injectivity (AQ.5)
#print axioms fineRelabel_injOn
#print axioms fineRelabel_image_card

-- Section C: successor translation + per-edge measure-preserving bijection (AQ.6, lem:r-cycle-map)
#print axioms shiftSucc_fineRelabel
#print axioms shiftSucc_cumGap
#print axioms affineSucc_bijOn
#print axioms affineSucc_card_eq
#print axioms affineSucc_measure_preserving

-- Section D: equal phase masses + complete-lap balance (AL.6 / R.1b / AL.7)
#print axioms affine_atlas_balance
#print axioms o1_affine_atlas_capstone

-- Section E: lap-displacement bound (AL.4a) + aggregate o(X|I_j|) (AL.4b/AL.4c)
#print axioms lapDisplacement_le
#print axioms incompleteLap_aggregate
#print axioms incompleteLap_exposure_aggregate
#print axioms incompleteLap_count_le_div
