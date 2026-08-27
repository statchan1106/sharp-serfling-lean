# Paper-to-Lean declaration audit

All declarations below are in the `SharpSerfling` namespace. Unqualified names
inherit the namespace shown in the first column.

## Main results

| Mathematical result | Lean declaration | Status |
|---|---|---|
| Weighted finite-population MGF | `FinitePopulation.finitePopulation_mgf` | complete |
| Optimality of the finite-population coefficient | `FinitePopulation.finitePopulation_sharp_constant` | complete |
| Serfling MGF | `FinitePopulation.serfling_mgf` | complete |
| Upper, lower, and two-sided Serfling tails | `FinitePopulation.serfling_tail`, `serfling_lower_tail`, `serfling_twoSided_tail` | complete |
| Exchangeable MGF under equality in law | `FinitePopulation.weighted_exchangeable_mgf_centeredNorm_inLaw` | complete |
| Exchangeable Chernoff tail | `FinitePopulation.weighted_exchangeable_tail_inLaw` | complete |
| Optimal exchangeable coefficient \(C_N^\star\) | `FinitePopulation.exchangeableInLaw_Cstar_sharp_constant` | complete |
| Sharp centered-hypergeometric MGF | `Hypergeometric.sharp_mgf`, `sharpMGFStatement` | complete |
| Variational evaluation \(\kappa_N^\star=\kappa_N\) | `Hypergeometric.kappaStar_eq_kappa` | complete |

## Structural reduction

| Mathematical role | Lean declaration | Status |
|---|---|---|
| Binary endpoint reduction | `FinitePopulation.binaryReduction`, `binaryRangeReduction` | complete |
| Permutation-orbit averaging | `FinitePopulation.finiteAverage_sample_orbit` | complete |
| Binary permutation MGF = slice MGF | `FinitePopulation.mgf_binary_eq_sliceMgf` | complete |
| Two-level slice = hypergeometric MGF | `FinitePopulation.sliceMgf_canonicalTwoLevel` | complete |
| Existence of a two-level maximizer | `FinitePopulation.exists_twoLevel_sliceMgf_maximizer` | complete |
| Sharp centered-slice inequality | `FinitePopulation.sliceLogMgf_le` | complete |

## Hypergeometric analysis

| Mathematical role | Lean declaration | Status |
|---|---|---|
| Success and sample complement symmetries | `Hypergeometric.mgf_successComplement`, `mgf_sampleComplement` | complete |
| Dimension-reducing derivative recursion | `Hypergeometric.deriv_mgf_recursion` | complete |
| Universal coefficient-one bound | `Hypergeometric.log_mgf_le_universal` | complete |
| Sharp Bernoulli base | `Hypergeometric.mgf_one_le_oddProxy` | complete |
| Central two-draw base | `Hypergeometric.mgf_lowerNearest_two_le_oddProxy` | complete |
| Noncentral derivative envelope | `Hypergeometric.oddNoncentralEnvelope` | complete |
| Signed-area comparison | `Analysis.singleCrossing_integral_nonneg` | complete |
| Hard-central parameter verification | `Hypergeometric.centralParameters` | complete |
| Complete odd-population induction | `Hypergeometric.odd_mgf_le` | complete |
| Uniform coefficient validity and minimality | `Hypergeometric.sharp_constant` | complete |

## Exact identities and asymptotics

| Mathematical role | Lean declaration | Status |
|---|---|---|
| Centered-weight norm identity | `FinitePopulation.sum_sq_centeredWeight_eq_rho` | complete |
| Exact weighted variance identity | `FinitePopulation.statistic_variance_eq_rho_mul_populationVariance` | complete |
| Zero-\(\rho_N\) characterization | `FinitePopulation.rho_eq_zero_iff_centeredWeight_eq_zero` | complete |
| Exact hypergeometric variance | `Hypergeometric.actualVariance_eq_variance` | complete |
| Odd optimum attained | `Hypergeometric.kappaStar_odd_attained` | complete |
| Even small-tilt optimum | `Hypergeometric.tendsto_normalizedLogMgf_even_central` | complete |
| Even/odd expansions of \(C_N^\star\) | `exchangeableConstant_even_expansion`, `exchangeableConstant_odd_expansion` | complete |
| \(N(C_N^\star-1)\to1\) | `tendsto_nat_mul_exchangeableConstant_sub_one` | complete |

## Trust boundary

`AxiomAudit.lean` prints the axioms of every exported result. Project sources
contain no `sorry`, `admit`, project-defined `axiom`, `unsafe`,
`implemented_by`, or `opaque` declaration. The expected kernel report contains
only `propext`, `Classical.choice`, and `Quot.sound`.
