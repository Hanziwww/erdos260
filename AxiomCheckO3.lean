import Erdos260.O3SlopePeriodicFloor

open Erdos260.O3SlopePeriodicFloor

-- Core A: the U.3 one-count floor
#print axioms nonzeroPeriodic_hitCount_ge
-- Core B: §24 distinct-residue slope bound g ≤ 3Q
#print axioms doubling_orbit_card
#print axioms sec24_slope_gap_le_threeQ
-- Core C: the void
#print axioms boundedPeriod_sparse_void
#print axioms boundedPeriod_sparse_void_real
-- Capstone: direct fixed-pin voiding
#print axioms o3_fixedPin_slope_periodic_void
-- Slope-gap uniqueness
#print axioms fixedPin_slope_gap_unique
-- Constant calibration
#print axioms sparseCap_below_sec24_floor
#print axioms rhoDQ_sparse_calibration
-- Fire-budget numerics
#print axioms manuscript_fixed_gap_value
#print axioms fixedPin_fire_budget_instance
#print axioms twoPow19_lt_fireBudget
#print axioms boundedPeriod_within_fireBudget
#print axioms oneThird_gt_seventeen_fireBudget
-- Status inventory
#print axioms o3SlopePeriodicFloorResiduals_nonempty
