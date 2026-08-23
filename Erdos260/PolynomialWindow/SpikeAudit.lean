import Erdos260.PolynomialWindow.Interior

/-! Audit of the four proof spikes that gate the upper module chain. -/

open Erdos260.PolynomialWindow

#check exists_integralNormalization
#check exists_coprime_denominator_after_prefix
#check leadingCoeff_den_dvd_integerVandermonde
#check polynomial_sampling_finset
#check integralFiber_card_bound_rpow
#check integerSublevelSet_card_bound
#check exists_polynomialGraph_of_integer_samples
#check highFrequency_coalescence
#check windowBlockSourceMap_injective

#print axioms exists_integralNormalization
#print axioms exists_coprime_denominator_after_prefix
#print axioms polynomial_sampling_finset
#print axioms integralFiber_card_bound_rpow
#print axioms integerSublevelSet_card_bound
#print axioms exists_polynomialGraph_of_integer_samples
#print axioms highFrequency_coalescence
#print axioms windowBlockSourceMap_injective
