# Manuscript-to-Lean traceability

This map follows the current 28-page draft identified in
[MANUSCRIPT.md](MANUSCRIPT.md). The mathematical description is the stable
identifier; theorem and equation numbers are those of the 2026-09-01 snapshot.
Every listed declaration is kernel-checked.

All abbreviated declaration names below inherit either the
`SharpSerfling.FinitePopulation` or `SharpSerfling.Hypergeometric` namespace
shown in the table.

## Section 1: motivation and exact sampling variance

| Manuscript item | Checked Lean declaration(s) | Status |
|---|---|---|
| Exact sample-mean variance, equation (1) | `FinitePopulation.statistic_variance_eq_rho_mul_populationVariance`, `SharpSerfling.rho_equalWeights` | complete |
| Exact finite-population correction, equation (2) | `SharpSerfling.rho_equalWeights`, `FinitePopulation.serfling_correction_chain` | complete |

## Section 2: main results

| Manuscript item | Checked Lean declaration(s) | Status |
|---|---|---|
| Definition of \(\rho_N(w)\) | `SharpSerfling.rho` | complete |
| Exact weighted variance \(\operatorname{Var}(T_w)=\rho_N(w)\sigma_N^2\) | `FinitePopulation.statistic_variance_eq_rho_mul_populationVariance` | complete |
| Theorem 1, weighted finite-population MGF, equation (3) | `FinitePopulation.finitePopulation_mgf` | complete |
| Theorem 1, smallest uniform multiplier | `FinitePopulation.finitePopulation_sharp_constant` | complete |
| Odd \(N\) strict improvement \(\kappa_N<1\), and \(\kappa_N\le1\) | `Hypergeometric.kappa_odd_lt_one`, `kappa_le_one` | complete |
| Corollary 1, equal-weight MGF, equation (4) | `FinitePopulation.serfling_mgf` | complete |
| Corollary 1, upper tail, equation (5) | `FinitePopulation.serfling_tail` | complete |
| Corollary 1, lower and two-sided tails | `FinitePopulation.serfling_lower_tail`, `serfling_twoSided_tail` | complete |
| Three finite-population corrections | `FinitePopulation.serfling_correction_chain` | complete |
| Corollary 1, fixed-\(n\) even sharpness | `FinitePopulation.serfling_fixed_even_sharp` | complete |
| Corollary 1, smallest coefficient uniform over \(n\) | `FinitePopulation.serfling_uniform_sharp_constant` | complete |
| Odd \(N\) uniform optimum attained at \(n=1\) | `FinitePopulation.serfling_uniform_odd_witness` | complete |
| Centered zero-padding identity, equation (6) | `FinitePopulation.sum_sq_centeredWeight_eq_rho` | complete |
| \(\rho_N(w)=0\) iff \(w^\circ=0\) | `FinitePopulation.rho_eq_zero_iff_centeredWeight_eq_zero` | complete |
| Corollary 2, exchangeable MGF, equation (7) | `FinitePopulation.weighted_exchangeable_mgf_centeredNorm_inLaw` | complete |
| Corollary 2, exchangeable tail, equation (8) | `FinitePopulation.weighted_exchangeable_tail_inLaw` | complete |
| Corollary 2, zero contrast | `FinitePopulation.exchangeable_contrast_eq_zero_of_centeredWeight_eq_zero` | complete |
| Corollary 2, smallest \(C_N^\star\) | `FinitePopulation.exchangeableInLaw_Cstar_sharp_constant` | complete |
| Uniform-permutation witness for optimality | `FinitePopulation.isExchangeableInLaw_uniformPermutation` | complete |
| Even/odd expansions of \(C_N^\star\) | `SharpSerfling.exchangeableConstant_even_expansion`, `exchangeableConstant_odd_expansion` | complete |
| \(N(C_N^\star-1)\to1\) | `SharpSerfling.tendsto_nat_mul_exchangeableConstant_sub_one` | complete |
| Theorem 2, centered hypergeometric MGF, equation (9) | `Hypergeometric.sharp_mgf`, `sharpMGFStatement` | complete |
| Exact hypergeometric variance | `Hypergeometric.actualVariance_eq_variance` | complete |
| Variational definition, equation (10) | `Hypergeometric.variationalValues`, `kappaStar` | complete |
| Proposition 1, \(\kappa_N^\star=\kappa_N\) | `Hypergeometric.kappaStar_eq_kappa` | complete |
| Proposition 1, odd attainment | `Hypergeometric.kappaStar_odd_attained` | complete |
| Proposition 1, fixed-\(m\) even small-tilt limit | `Hypergeometric.tendsto_normalizedLogMgf_even_central` | complete |

## Section 3: reduction to centered hypergeometric MGFs

The manuscript invokes the binary and two-level reductions from Lee--Kim
(2026). The repository proves those ingredients internally, so they are not
axioms or unverified interfaces here.

| Manuscript role | Checked Lean declaration(s) | Status |
|---|---|---|
| Affine normalization and binary endpoint reduction | `FinitePopulation.statistic_affine`, `binaryReduction`, `binaryRangeReduction` | complete |
| Permutation orbit equals a uniform fixed-cardinality slice | `FinitePopulation.finiteAverage_sample_orbit`, `mgf_binary_eq_sliceMgf` | complete |
| Existence of a centered fixed-radius maximizer | `FinitePopulation.exists_sliceMgf_maximizer` | complete |
| Three-coordinate repeated-value obstruction | `Analysis.exists_iteratedDeriv_five_eq_zero_of_three_double_roots`, `hermite_weighted_deriv_pos`, `threePoint_globalMax_has_duplicate` | complete |
| Internal two-level maximizer reduction | `FinitePopulation.exists_twoLevel_sliceMgf_maximizer` | complete |
| Two-level slice equals a centered hypergeometric MGF | `FinitePopulation.sliceMgf_canonicalTwoLevel` | complete |
| Lemma 1, reduction and normalization, equations (11)--(12) | `FinitePopulation.sliceLogMgf_le`, `sum_sq_centeredWeight_eq_rho` | complete |

## Section 4: uniform centered-hypergeometric bound

| Manuscript item | Checked Lean declaration(s) | Status |
|---|---|---|
| Lemma 2, Stein/binomial representation | `Hypergeometric.binomialAverage_stein`, `mgf_eq_binomialMgf` | complete |
| Lemma 2, derivative recursion, equation (13) | `Hypergeometric.deriv_mgf_recursion` | complete |
| Lemma 2, complement identities, equations (14)--(15) | `Hypergeometric.mgf_successComplement`, `mgf_sampleComplement` | complete |
| Stein and weighted/binomial reductions, equations (16)--(17) | `Hypergeometric.binomialAverage_stein`, `binomialAverage_weighted_reduction_real` | complete |
| Hyperbolic-sine estimate, equation (18) | `Hypergeometric.sinh_le_mul_exp_sq_div_six`, `two_sinh_div_le_exp_sq_div_twentyFour` | complete |
| Proposition 2, coefficient-one MGF bound, equation (19) | `Hypergeometric.mgf_le_universal`, `log_mgf_le_universal` | complete |
| Even branch sharpness at the origin | `Hypergeometric.tendsto_normalizedLogMgf_even_central` | complete |

## Section 5: smallest uniform MGF constant

| Manuscript role | Checked Lean declaration(s) | Status |
|---|---|---|
| Sharp Bernoulli/Kearns--Saul base | `Hypergeometric.onePhi_le_exact`, `mgf_one_le_oddProxy` | complete |
| Central two-draw base and exact distinguished-tilt equality | `Hypergeometric.log_mgf_lowerNearest_two_le_exact`, `log_mgf_lowerNearest_two_eq_exact_at_increment` | complete |
| Comparison of the central two-draw scale with the odd target | `Hypergeometric.centralTwo_scale_le_oddProxy`, `mgf_lowerNearest_two_le_oddProxy` | complete |
| Noncentral pointwise derivative comparison | `Hypergeometric.oddNoncentralEnvelope`, `deriv_mgf_le_oddProxy_of_reduced_noncentral`, `mgf_le_oddProxy_noncentral_of_reduced` | complete |
| Negative-tilt nearest-balanced slice | `Hypergeometric.mgf_le_oddProxy_upperNearest_of_reduced` | complete |
| Signed-area reduction for the hard central case | `Analysis.singleCrossing_integral_nonneg`, `Hypergeometric.hardCentralQ_endpoint_nonneg` | complete |
| Completed odd induction and Theorem 2 assembly | `Hypergeometric.odd_mgf_le`, `sharp_mgf` | complete |
| Validity and minimality uniformly over all slices | `Hypergeometric.sharp_constant` | complete |

## Appendices B and C: analytic lemmas and certificates

| Manuscript item | Checked Lean declaration(s) | Status |
|---|---|---|
| Lemma 3, odd \(\kappa_N\) bounds, equation (28) | `Hypergeometric.kappa_odd_lower`, `kappa_odd_upper` | complete |
| Lemma 4, \(\gamma\) bounds, equations (29)--(32) | `oddGamma_ge_alpha_sq_div_six`, `oddGamma_le_one_sixth`, `oddGamma_ge_alpha_sq_add_u_div_twelve`, `oddGamma_ge_alpha_sq_add_u_div_seven` | complete |
| Lemma 5, central-deficit bounds, equation (33) | `Hypergeometric.centralDeficit_bounds` | complete |
| Lemma 6, central \(m=2\) bound, equation (34) | `Hypergeometric.log_mgf_lowerNearest_two_le_exact` | complete |
| Lemma 7, signed-area comparison, equations (35)--(36) | `Analysis.singleCrossing_integral_nonneg` | complete |
| Lemma 8, hard-central conditions, equation (37) | `Hypergeometric.centralParameters` and its component bounds | complete |
| Appendix C polynomial expansions and positivity | `Certificates.P0_nonneg`, `P12_nonneg`, `P7_nonneg` and endpoint identities | complete |

## Verification boundary

- `lake build` checks the complete dependency graph.
- `AxiomAudit.lean` prints the assumptions of the headline results.
- `FullAxiomAudit.lean` checks every declaration whose name begins with
  `SharpSerfling` and rejects dependencies outside `propext`,
  `Classical.choice`, and `Quot.sound`.
- CI rejects `sorry`, `admit`, project-defined `axiom`, `unsafe`,
  `implemented_by`, and `opaque` in project Lean sources.
