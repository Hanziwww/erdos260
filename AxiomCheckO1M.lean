import Erdos260.O1MeasurePreservation

open Erdos260.O1MeasurePreservation

-- Section A: discrete measure preservation under a bijection (two-sided)
#print axioms measurePreserving_card_of_bij
#print axioms measurePreserving_sum_of_bij
#print axioms image_card_eq_of_injOn
#print axioms image_sum_eq_of_injOn
#print axioms bijOn_finset_card_eq
#print axioms bijOn_finset_sum_eq

-- Section B: the cyclic transition is a measure-preserving bijection (App R target)
#print axioms cycleMap_bijOn
#print axioms cycleMap_card_eq
#print axioms cycleMap_measure_preserving
#print axioms cycleEquiv

-- Section C: affine-relabelling bijectivity kernel
#print axioms affineEquiv
#print axioms affineMap_bijective
#print axioms intTranslation_bijective
#print axioms affineZMod_bijective
#print axioms affineZMod_image_card
#print axioms startShift_bijOn
#print axioms startShift_card_eq
#print axioms startShift_measure_preserving

-- Section D: cycle-saturation ⇒ equal phase mass ⇒ exact complete-lap balance
#print axioms phaseMass_const_of_succ_eq
#print axioms cycle_saturation_balance
#print axioms cycle_charts_balance
