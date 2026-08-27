# Manuscript-to-Lean traceability

This audit targets the 27-page manuscript `Sharp_Serfling (49).pdf`, SHA-256
`1b4f0ddc2acd2fb8ed93cac9011f2f816d5938996181d30ce022fc970cc138cd`.
It uses the numbering in that file. All rows below are kernel-checked and the
status is complete.

## Main statements and displayed consequences

| Manuscript item | Checked Lean declaration(s) | Status |
|---|---|---|
| Definition of `ρ_N(w)` and equal-weight identity | `SharpSerfling.rho`, `SharpSerfling.rho_equalWeights` | complete |
| Exact variance `Var(T_w) = ρ_N(w) σ_N²` | `SharpSerfling.FinitePopulation.statistic_variance_eq_rho_mul_populationVariance` | complete |
| Theorem 1, weighted finite-population MGF (2) | `SharpSerfling.FinitePopulation.finitePopulation_mgf` | complete |
| Theorem 1, smallest uniform multiplier | `SharpSerfling.FinitePopulation.finitePopulation_sharp_constant` | complete |
| Odd `N` strict improvement `κ_N < 1` and general `κ_N ≤ 1` | `SharpSerfling.Hypergeometric.kappa_odd_lt_one`, `kappa_le_one` | complete |
| Corollary 1, equal-weight MGF (3) | `SharpSerfling.FinitePopulation.serfling_mgf` | complete |
| Corollary 1, upper tail (4) | `SharpSerfling.FinitePopulation.serfling_tail` | complete |
| Corollary 1, lower and two-sided tails | `serfling_lower_tail`, `serfling_twoSided_tail` | complete |
| Three finite-population corrections | `SharpSerfling.FinitePopulation.serfling_correction_chain` | complete |
| Exact binary sample-mean/hypergeometric bridge | `SharpSerfling.FinitePopulation.sampleMeanMgf_markedIndicator` | complete |
| Corollary 1 sharpness for each fixed `n` when `N` is even | `SharpSerfling.FinitePopulation.serfling_fixed_even_sharp` | complete |
| Corollary 1 smallest coefficient uniform over `n` | `SharpSerfling.FinitePopulation.serfling_uniform_sharp_constant` | complete |
| Odd `N` uniform optimum attained at `n = 1` | `SharpSerfling.FinitePopulation.serfling_uniform_odd_witness` | complete |
| Centered zero-padding identity (5) | `SharpSerfling.FinitePopulation.sum_sq_centeredWeight_eq_rho` | complete |
| `ρ_N(w) = 0` iff `w° = 0` | `SharpSerfling.FinitePopulation.rho_eq_zero_iff_centeredWeight_eq_zero` | complete |
| Corollary 2 MGF (6), standard equality-in-law exchangeability | `SharpSerfling.FinitePopulation.weighted_exchangeable_mgf_centeredNorm_inLaw` | complete |
| Corollary 2 tail (7) | `SharpSerfling.FinitePopulation.weighted_exchangeable_tail_inLaw` | complete |
| Corollary 2 zero contrast | `exchangeable_contrast_eq_zero_of_centeredWeight_eq_zero` | complete |
| Corollary 2 smallest `C_N^⋆` | `SharpSerfling.FinitePopulation.exchangeableInLaw_Cstar_sharp_constant` | complete |
| Uniform-permutation witness used for optimality | `isExchangeableInLaw_uniformPermutation` | complete |
| Even/odd expansions of `C_N^⋆` | `SharpSerfling.exchangeableConstant_even_expansion`, `exchangeableConstant_odd_expansion` | complete |
| Limit `N(C_N^⋆ - 1) → 1` | `SharpSerfling.tendsto_nat_mul_exchangeableConstant_sub_one` | complete |
| Theorem 2, parity-sharp hypergeometric MGF (8) | `SharpSerfling.Hypergeometric.sharp_mgf`, `sharpMGFStatement` | complete |
| Exact hypergeometric variance below (8) | `SharpSerfling.Hypergeometric.actualVariance_eq_variance` | complete |
| Variational definition (9) | `SharpSerfling.Hypergeometric.variationalValues`, `kappaStar` | complete |
| Proposition 1, `κ_N^⋆ = κ_N` | `SharpSerfling.Hypergeometric.kappaStar_eq_kappa` | complete |
| Proposition 1, odd attainment | `SharpSerfling.Hypergeometric.kappaStar_odd_attained` | complete |
| Proposition 1, fixed-`m` even small-tilt limit | `SharpSerfling.Hypergeometric.tendsto_normalizedLogMgf_even_central` | complete |

## Reduction and hypergeometric proof

The manuscript cites the binary/two-level reduction from Lee and Kim (2026).
The formal development is stronger at this point: it verifies the reduction
internally instead of taking the cited result as an assumption.

| Manuscript role | Checked Lean declaration(s) | Status |
|---|---|---|
| Affine normalization and binary endpoint reduction | `SharpSerfling.FinitePopulation.statistic_affine`, `binaryReduction`, `binaryRangeReduction` | complete |
| Permutation orbit equals uniform fixed-cardinality slice | `finiteAverage_sample_orbit`, `mgf_binary_eq_sliceMgf` | complete |
| Existence of a centered fixed-radius maximizer | `exists_sliceMgf_maximizer` | complete |
| Three-coordinate repeated-value obstruction | `SharpSerfling.Analysis.exists_iteratedDeriv_five_eq_zero_of_three_double_roots`, `hermite_weighted_deriv_pos`, `threePoint_globalMax_has_duplicate` | complete |
| Internally verified Lee--Kim two-level maximizer reduction | `SharpSerfling.FinitePopulation.exists_twoLevel_sliceMgf_maximizer` | complete |
| Two-level slice equals centered hypergeometric MGF | `sliceMgf_canonicalTwoLevel` | complete |
| Sharp centered-slice consequence | `sliceLogMgf_le` | complete |
| Lemma 1, Stein/binomial representation | `SharpSerfling.Hypergeometric.binomialAverage_stein`, `mgf_eq_binomialMgf` | complete |
| Lemma 1, derivative recursion (10) | `SharpSerfling.Hypergeometric.deriv_mgf_recursion` | complete |
| Lemma 1, complement identities (11)--(12) | `mgf_successComplement`, `mgf_sampleComplement` | complete |
| Proposition 2, coefficient-one MGF bound (15) | `SharpSerfling.Hypergeometric.mgf_le_universal`, `log_mgf_le_universal` | complete |
| Even branch sharpness at the origin | `SharpSerfling.Hypergeometric.tendsto_normalizedLogMgf_even_central` | complete |
| Sharp Bernoulli/Kearns--Saul base | `SharpSerfling.Hypergeometric.onePhi_le_exact`, `mgf_one_le_oddProxy` | complete |
| Noncentral pointwise derivative comparison | `oddNoncentralEnvelope`, `deriv_mgf_le_oddProxy_of_reduced_noncentral`, `mgf_le_oddProxy_noncentral_of_reduced` | complete |
| Negative-tilt nearest-balanced slice | `mgf_le_oddProxy_upperNearest_of_reduced` | complete |
| Completed odd induction and Theorem 2 assembly | `odd_mgf_le`, `sharp_mgf` | complete |

## Appendix B lemmas and Appendix C certificates

| Manuscript item | Checked Lean declaration(s) | Status |
|---|---|---|
| Lemma 2, odd `κ_N` bounds (24) | `SharpSerfling.Hypergeometric.kappa_odd_lower`, `kappa_odd_upper` | complete |
| Lemma 3, `γ` bounds (25)--(28) | `oddGamma_ge_alpha_sq_div_six`, `oddGamma_le_one_sixth`, `oddGamma_ge_alpha_sq_add_u_div_twelve`, `oddGamma_ge_alpha_sq_add_u_div_seven` | complete |
| Lemma 4, `ℓ_N` bounds (29) | `SharpSerfling.Hypergeometric.centralDeficit_bounds` | complete |
| Lemma 5, central `m = 2` bound (30) | `SharpSerfling.Hypergeometric.log_mgf_lowerNearest_two_le_exact` | complete |
| Lemma 5, equality at `t = L_{N,2}` | `SharpSerfling.Hypergeometric.log_mgf_lowerNearest_two_eq_exact_at_increment` | complete |
| Lemma 5, comparison with the odd target proxy | `SharpSerfling.Hypergeometric.centralTwo_scale_le_oddProxy`, `mgf_lowerNearest_two_le_oddProxy` | complete |
| Lemma 6, deterministic signed-area comparison (31)--(32) | `SharpSerfling.Analysis.singleCrossing_integral_nonneg` | complete |
| Lemma 7, hard-central conditions (33) | `SharpSerfling.Hypergeometric.centralParameters` and its component bounds | complete |
| `Q(β)` endpoint transformation used with Lemma 6 | `hardCentralQ_endpoint_eq_singleCrossing`, `hardCentralQ_endpoint_nonneg` | complete |
| Appendix C polynomial expansions and positivity | `SharpSerfling.Certificates.P0_nonneg`, `P12_nonneg`, `P7_nonneg` and endpoint identities | complete |

## Verification boundary

- `lake build` checks the complete dependency graph.
- `AxiomAudit.lean` prints the assumptions of the headline results.
- `FullAxiomAudit.lean` automatically inspects every declaration whose name
  begins with `SharpSerfling`; it fails on any dependency outside `propext`,
  `Classical.choice`, and `Quot.sound`.
- CI rejects `sorry`, `admit`, project-defined `axiom`, `unsafe`,
  `implemented_by`, and `opaque` in project Lean sources.
