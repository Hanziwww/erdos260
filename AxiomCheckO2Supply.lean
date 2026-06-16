import Erdos260.O2SupplyEmbedding

open Erdos260.O2SupplyEmbedding

-- Section A: constructed start/threshold rectangle has size X·|I_j|
#print axioms shell_card
#print axioms startThresholdRect_card

-- Section B: faithful start/threshold indexing from carry faithfulness (lem:ak-faithful)
#print axioms piSt_injective_via_carry
#print axioms piSt_injOn_via_carry

-- Section C: base-carrier mass bound with constructed rectangle (AK.1)
#print axioms base_carrier_mass_le_rect
#print axioms base_carrier_mass_via_carry

-- Section D: deleted-collar additive remainder (AK.1 / AB.3 o(·))
#print axioms mass_le_rect_plus_collar

-- Section E: summed ambient support with constructed rectangle (AK.3 / AD.2)
#print axioms o2_ambient_support_summed_constructed
#print axioms o2_supply_capstone
