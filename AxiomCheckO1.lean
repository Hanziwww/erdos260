import Erdos260.O1FineFibreBalance

open Erdos260.O1FineFibreBalance

-- Section A: complete-lap phase-mass identity + R.2' valid bound
#print axioms Mtot_uniform
#print axioms exitMass_uniform
#print axioms completeLap_phase_mass_identity
#print axioms fineFibre_exitMass_valid_bound

-- Section B: the spaced-share NON-COVERING guard (Hotspot 1)
#print axioms spacedShare_not_covering_of_pos
#print axioms spacedShare_not_covering
#print axioms spacedShare_separation
#print axioms spacedShare_ratio_strict
#print axioms spacedShare_concrete_witness

-- Section C: fine-fibre injectivity (Hotspot 2)
#print axioms startTranslation_injective
#print axioms fineRelabel_injective
#print axioms fineFibre_card_le_ambient
#print axioms fineFibre_phaseMass_eq
#print axioms recurrent_component_has_cycle

-- Section D: incomplete-lap bounded boundary (Hotspot 3b)
#print axioms incompleteLap_count_le_div
#print axioms incompleteLap_mass_le
#print axioms incompleteLap_exposureWeighted_le
#print axioms fineFibre_balance_with_boundary
