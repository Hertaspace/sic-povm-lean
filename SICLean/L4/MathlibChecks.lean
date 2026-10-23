import Mathlib

/-!
# Checked Mathlib entry points

This file contains `#check` commands for the Mathlib API used in the project, not new
mathematical claims.
-/

-- Complex integration and parameter dependence.
#check Complex.integral_boundary_rect_eq_zero_of_differentiableOn
#check Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
#check circleIntegral.integral_sub_inv_of_mem_ball
#check circleIntegral.integral_sub_zpow_of_ne
#check hasDerivAt_integral_of_dominated_loc_of_deriv_le
#check hasFDerivAt_integral_of_dominated_of_fderiv_le
#check MeasureTheory.tendsto_integral_filter_of_dominated_convergence
#check MeasureTheory.Integrable.norm
#check integrableOn_exp_mul_Ioi
#check Complex.hasDerivAt_sinh
#check Complex.sinh_mul_I
#check Complex.sin_eq_zero_iff
#check Complex.norm_exp
#check Complex.norm_exp_sub_one_le
#check DifferentiableOn.analyticOnNhd
#check AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
#check MeromorphicAt.mul
#check MeromorphicAt.inv

-- Infinite products, modular normalization, and the already available finite DFT.
#check ModularForm.multipliable_one_sub_pow
#check ModularForm.eta_ne_zero
#check ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
#check jacobiTheta₂_functional_equation
#check hasFDerivAt_jacobiTheta₂
#check ZMod.dft_dft
#check AddChar.expect_eq_zero_iff_ne_zero

-- L3: finite systems, constructible images, and the 2-adic model.
#check PrimeSpectrum.isConstructible_comap_image
#check PrimeSpectrum.isConstructible_range_comap
#check PrimeSpectrum.exists_constructibleSetData_iff
#check PrimeSpectrum.ConstructibleSetData.toSet
#check PrimeSpectrum.ConstructibleSetData.isConstructible_toSet
#check MvPolynomial.zeroLocus_span
#check MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal
#check MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
#check Ideal.mem_radical_iff
#check Polynomial.finite_setOfPred_isRoot
#check minpoly.monic
#check minpoly.aeval
#check Module.finite_iff_krullDimLE_zero
#check Module.finite_of_isArtinianRing
#check algebraicClosure.isAlgClosure
#check mem_algebraicClosure_iff
#check IsAlgClosed.lift
#check PadicAlgCl
#check PadicAlgCl.isNonarchimedean
#check PadicAlgCl.norm_extends
#check PadicAlgCl.valuation_p
#check Padic.norm_p
#check Valuation.comap
#check Valuation.map_sum_lt
#check Valuation.map_sum_eq_of_lt
#check Valuation.map_inv
#check NumberField.RingOfIntegers.instFintypeClassGroup
#check NumberField.classNumber
#check Submodule.finiteQuotientOfFreeOfRankEq
#check Submodule.finiteQuotient_iff

-- L5: existing algebra/Galois tools are distinct from global class-field theory.
#check Field.absoluteGaloisGroup
#check AlgEquiv.liftNormal
#check AlgEquiv.liftNormal_commutes
#check IntermediateField.fixedField
#check IsGalois.fixedField_fixingSubgroup
#check exists_isTranscendenceBasis
#check IsTranscendenceBasis.isAlgebraic
#check AlgebraicIndependent.aevalEquiv
#check MvPolynomial.mapEquiv
#check IsAlgClosed.isAlgClosure_of_transcendence_basis
#check IsAlgClosure.equivOfEquiv
#check IsAlgClosure.equivOfEquiv_algebraMap
#check NumberField.IsTotallyReal.complexEmbedding_isReal
#check NumberField.ComplexEmbedding.IsConj.comp
#check AbsoluteValue.denseRange_algebraMap_pi
#check NumberField.AdeleRing
#check NumberField.Set.HasDirichletDensity
#check IsDecompositionField
#check IsInertiaField
#check IsFractionRing.stabilizerQuotientInertiaEquiv
#check FiniteField.Extension.frob
#check IsCyclotomicExtension.autEquivPow
#check Complex.norm_eq_one_of_pow_eq_one
#check eq_or_eq_neg_of_sq_eq_sq
#check Complex.mul_conj
#check Complex.sq_norm
