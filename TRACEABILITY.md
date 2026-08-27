# Manuscript-to-Lean traceability

This table maps the manuscript's mathematical statements to their checked Lean
counterparts.
Names without a namespace prefix are in the namespace indicated by the nearest
fully qualified name.

| Manuscript item | Checked Lean declaration(s) | Status |
|---|---|---|
| Equation (1), centered-weight norm identity | `SharpSerfling.FinitePopulation.sum_sq_centeredWeight_eq_rho` | complete |
| `ρ_N(w) = 0` iff `w° = 0` | `SharpSerfling.FinitePopulation.rho_eq_zero_iff_centeredWeight_eq_zero` | complete |
| Equation (2), exact finite-population variance | `SharpSerfling.FinitePopulation.statistic_variance_eq_rho_mul_populationVariance` | complete |
| Theorem 1, weighted finite-population MGF | `SharpSerfling.FinitePopulation.finitePopulation_mgf` | complete |
| optimality clause of Theorem 1 | `SharpSerfling.FinitePopulation.finitePopulation_sharp_constant` | complete |
| Corollary 1, equal-weight MGF | `SharpSerfling.FinitePopulation.serfling_mgf` | complete |
| Corollary 1, upper/lower/two-sided tails | `serfling_tail`, `serfling_lower_tail`, `serfling_twoSided_tail` | complete |
| Corollary 2 under standard equality in distribution | `weighted_exchangeable_mgf_centeredNorm_inLaw`, `weighted_exchangeable_tail_inLaw` | complete |
| Corollary 2, `w° = 0` | `exchangeable_contrast_eq_zero_of_centeredWeight_eq_zero` | complete |
| uniform-permutation law used in Corollary 2 | `isExchangeableInLaw_uniformPermutation` | complete |
| optimality clause of Corollary 2 in literal `C_N^⋆` normalization | `exchangeableInLaw_Cstar_sharp_constant` | complete |
| displayed even/odd expansion of `C_N^⋆` | `SharpSerfling.exchangeableConstant_even_expansion`, `exchangeableConstant_odd_expansion` | complete |
| limit `N(C_N^⋆ - 1) → 1` | `SharpSerfling.tendsto_nat_mul_exchangeableConstant_sub_one` | complete |
| Theorem 2, sharp hypergeometric MGF | `SharpSerfling.Hypergeometric.sharp_mgf`, `sharpMGFStatement` | complete |
| displayed exact hypergeometric variance | `SharpSerfling.Hypergeometric.actualVariance_eq_variance` | complete |
| variational definition (9) and Proposition 1 | `variationalValues`, `kappaStar`, `kappaStar_eq_kappa` | complete |
| odd-`N` attainment in Proposition 1 | `kappaStar_odd_attained` | complete |
| fixed-slice even-`N` small-tilt limit in Proposition 1 | `tendsto_normalizedLogMgf_even_central` | complete |
| Proposition 2, two-level extremizer | `SharpSerfling.FinitePopulation.exists_twoLevel_sliceMgf_maximizer` | complete |
| centered consequence of Proposition 2 | `SharpSerfling.FinitePopulation.sliceLogMgf_le` | complete |
| three-coordinate sphere step in Proposition 2 | `SharpSerfling.Analysis.threePoint_globalMax_has_duplicate` | complete |
| Hermite sign/repeated-Rolle steps | `hermite_weighted_deriv_pos`, `exists_iteratedDeriv_five_eq_zero_of_three_double_roots` | complete |
| binary slice/permutation identity | `SharpSerfling.FinitePopulation.mgf_binary_eq_sliceMgf` | complete |
| canonical two-level/hypergeometric identity | `SharpSerfling.FinitePopulation.sliceMgf_canonicalTwoLevel` | complete |
| Lemma 1, complement identities | `SharpSerfling.Hypergeometric.mgf_successComplement`, `mgf_sampleComplement` | complete |
| Lemma 1, dimension-reducing derivative identity | `SharpSerfling.Hypergeometric.deriv_mgf_recursion` | complete |
| Proposition 3, coefficient-one bound | `SharpSerfling.Hypergeometric.log_mgf_le_universal` | complete |
| Lemma 2, binary reduction | `SharpSerfling.FinitePopulation.binaryReduction`, `binaryRangeReduction` | complete |
| Lemma 3, odd-`κ` bounds | `SharpSerfling.Hypergeometric.kappa_odd_lower`, `kappa_odd_upper` | complete |
| Lemma 4, proxy-gap bounds | `oddGamma_ge_alpha_sq_div_six`, `oddGamma_ge_alpha_sq_add_u_div_twelve`, `oddGamma_ge_alpha_sq_add_u_div_seven`, `oddGamma_le_one_sixth` | complete |
| Lemma 5, central deficit | `SharpSerfling.Hypergeometric.centralDeficit_bounds` | complete |
| sharp Bernoulli/Kearns--Saul base | `onePhi_le_exact`, `mgf_one_le_oddProxy` | complete |
| Lemma 6, central `m = 2` slice | `log_mgf_lowerNearest_two_le_exact`, `mgf_lowerNearest_two_le_oddProxy` | complete |
| noncentral pointwise derivative comparison | `oddNoncentralEnvelope`, `deriv_mgf_le_oddProxy_of_reduced_noncentral`, `mgf_le_oddProxy_noncentral_of_reduced` | complete |
| negative-tilt nearest-balanced slice | `mgf_le_oddProxy_upperNearest_of_reduced` | complete |
| Lemma 7 and the `Q(β)` transformation | `SharpSerfling.Analysis.singleCrossing_integral_nonneg`, `hardCentralQ_endpoint_eq_singleCrossing`, `hardCentralQ_endpoint_nonneg` | complete |
| Lemma 8, hard-central parameters | `SharpSerfling.Hypergeometric.centralParameters` and its component bounds | complete |
| completed odd induction | `SharpSerfling.Hypergeometric.odd_mgf_le` | complete |
| Appendix C polynomial certificates | `SharpSerfling.Certificates.P0_nonneg`, `P12_nonneg`, `P7_nonneg` and endpoint identities | complete |
