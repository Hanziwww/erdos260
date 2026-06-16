import Erdos260.O3PeriodicitySupply

open Erdos260.O3PeriodicitySupply

-- Task 1: eventually periodic from out-degree-1 (the SUPPLY core), with bounds
#print axioms eventuallyPeriodic_of_fintype
#print axioms fixedPin_period_le_card
-- Task 3: nonzero/clean continuation invariance (reuse iterate_periodic_invariant)
#print axioms iterate_lap_invariant
#print axioms cycle_nonzero_persists
#print axioms cycle_block_supply
-- Task 2: SUPPLY → VOID bridge
#print axioms o3_fixedPin_supply_void
#print axioms o3_fixedPin_supply_void_int
-- Task 2: bounded-period instantiations (p ≤ 3Q, p ≤ 2^19 fire budget)
#print axioms fixedPin_period_le_threeQ
#print axioms fixedPin_period_within_fireBudget
-- Assembled capstone: bounded state space ⇒ void
#print axioms o3_fixedPin_supply_void_of_boundedStateSpace
-- Status inventory
#print axioms o3PeriodicitySupplyResiduals_nonempty
