import Erdos260.O4ClassOneFidelity

open Erdos260.O4ClassOneFidelity

-- Hotspot 1: H.5 transfer-mass fidelity (Appendix AS)
#print axioms transferOp_basisVec
#print axioms offNeutralMass_basisVec
#print axioms h5Charge_eq_indicator
#print axioms h5CutKernel_eq_indicator
#print axioms h5Charge_eq_cutKernel
#print axioms h5Charge_eq_w1
#print axioms h5Charge_neutral
#print axioms h5Charge_floor
#print axioms h5Charge_nonneg

-- Hotspot 2: cocycle / midpoint table on G₁ = ZMod 6 (Appendix Y, via decide)
#print axioms h5Charge_zmod6
#print axioms h5Charge_eq_cutKernel_zmod6
#print axioms cocycle_additivity_zmod6
#print axioms nonzero_child_zmod6
#print axioms midpoint_table_zmod6

-- Hotspot 3: excess ⇒ nonzero row ⇒ formal atom ⇒ void (Appendices AO + AN + Y + AA)
#print axioms o4_excess_voids
#print axioms o4_class1_cap
