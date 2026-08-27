# Formalization status

## Acceptance criteria

- `lake build` succeeds from a clean checkout.
- No `sorry`, `admit`, project-defined `axiom`, `unsafe`, `implemented_by`, or
  `opaque` declaration occurs in project sources.
- The final theorem has the manuscript's quantifier order and hypotheses.
- Kernel axiom audits report only ordinary mathlib foundations.
- Degenerate cases (`K = 0`, `K = N`, `m = 0`, `m = N`, zero centered
  coefficient vector) are explicit.

## Milestones

- M0: pinned Lean 4/mathlib project and kernel/source audit.
- M1: finite-average and centered-hypergeometric definitions.
- M2: combinatorial identities, symmetries, and MGF derivative recursion.
- M3: universal variance-scale hypergeometric bound.
- M4: sharp Bernoulli bound and odd-population analytic estimates.
- M5: sharp hypergeometric theorem and parity optimality.
- M6: binary-population and two-level coefficient reductions.
- M7: weighted finite-population theorem and corollaries.

## Completed

- M0: Lean 4.32.1 and mathlib v4.32.1 are pinned; build and audit entry points exist.
- M1: explicit finite averages, uniform permutation MGF, fixed-cardinality subset model,
  centered hypergeometric MGF, exact sample-space cardinality, positivity, and all
  deterministic edge cases.
- M2: both complement symmetries, the exact combinatorial fiber formula,
  hypergeometric Stein identity, weighted reduction, and the full
  dimension-reducing MGF derivative recursion.
- M3: the coefficient-one variance-scale hypergeometric MGF bound, including
  the finite Hoeffding base case, simultaneous strong induction, derivative
  integration, success complementation, and sample complementation.
- Appendix certificates: all three manuscript polynomials `P₀`, `P₁₂`, and `P₇`,
  their exact endpoint factorizations, concavity reductions, and interval
  nonnegativity proofs.
- Weighted preliminaries: positivity of `κ_N`, nonnegativity of `ρ_N`, and the
  exact equal-weight finite-population correction.
- M4 analytic core: odd-`κ` upper/lower estimates, all proxy-gap bounds,
  central-deficit bounds, the pointwise noncentral envelope, its exact connection
  to the MGF recursion (including integration from zero), the negative-tilt
  nearest-balanced slice, and the signed-area single-crossing lemma with its
  integration identity and Taylor remainder estimates.  The exact
  `x = βz` transformation from the accumulated hard-central derivative
  difference to that signed-area integral is also complete.  The complete
  central-parameter verification is now kernel-checked as well: the crossing
  size reduction, root ordering, quantitative endpoint gaps, exponential
  control, and final signed-area certificate all close without placeholders.
- M4 sharp bases and assembly: the central `m = 2` three-point law, its optimal
  quadratic proxy and proxy comparison, a self-contained Kearns--Saul proof for
  `m = 1`, and the full odd-population induction are kernel-checked.  Combining
  this with the universal even branch gives the complete parity-sharp
  hypergeometric MGF theorem `sharp_mgf` and its manuscript-shaped wrapper
  `sharpMGFStatement`.
- M5: parity optimality is kernel-checked.  For odd populations the proof uses
  the explicit nonzero equality witness in the Bernoulli slice; for even
  populations it computes the second derivative at the origin and derives the
  necessary coefficient from the second-derivative test.  Thus
  `sharp_constant` proves both validity and minimality of `κ_N` uniformly over
  all nontrivial hypergeometric slices.
- M6 binary-population reduction: the permutation MGF is proved convex in the
  full population vector, the interval cube is represented as the convex hull
  of its endpoint vertices, and the maximum principle yields both the unit-cube
  `binaryReduction` and arbitrary-range `binaryRangeReduction` without sign
  restrictions on the weights.
- M6 exact finite bridges: permutation-orbit averaging, zero-padding and exact
  centering of the weight vector, the binary-population MGF/subset-slice MGF
  identity, and the canonical two-level slice/hypergeometric MGF identity are
  kernel-checked.  The centered fixed-radius slice is compact, its MGF is
  continuous, and an extremizer exists.
- M6 three-coordinate analytic core: the repeated-Rolle theorem, quintic
  Hermite interpolation sign lemma, and the strict three-coordinate sphere
  maximum lemma are kernel-checked.  The proof explicitly constructs the
  constraint-preserving circle, verifies both constraint identities, derives
  first- and second-order conditions, and rules out three distinct coordinates.
- M6 global two-level reduction: the slice numerator is identified with an
  elementary symmetric function, expanded exactly after isolating any three
  coordinates, and all boundary degrees `K = 1`, `K = 2`, and `K ≥ 3` are
  handled.  Consequently a global slice-MGF maximizer has at most two distinct
  coordinate values; this internally verifies the Lee--Kim structural reduction
  cited in Section 3 of manuscript (49).
- M7 main weighted MGF theorem: every two-valued centered maximizer is
  identified, up to coordinate permutation, with a canonical two-level vector;
  the sharp hypergeometric estimate therefore bounds every centered slice.
  Affine population rescaling, binary reduction, the exact binary-slice bridge,
  and the centered-weight norm identity then give the manuscript's full
  `thm:finite-population` as `finitePopulation_mgf`, including constant
  populations and the empty/full binary slices.
- M7 equal-weight MGF specialization: the equal-weight statistic is proved
  exactly equal to the without-replacement sample-mean deviation, and
  `serfling_mgf` has the manuscript's sharp finite-population coefficient.
- M7 Serfling tails: exponential Markov is proved directly on the finite
  permutation space, the optimizing tilt is evaluated exactly, and upper,
  lower, and two-sided forms of the manuscript corollary are kernel-checked.
- M7 exchangeable transfer: exchangeability is formalized as expectation
  invariance under every finite coordinate permutation.  Boundedness gives
  integrability of every exponential statistic, finite permutation averaging
  is interchanged with the Bochner integral, and the weighted exchangeable MGF
  and Chernoff upper tail are proved in the manuscript's
  `Cstar * ‖w°‖²` normalization.  The `w° = 0` contrast is also proved to vanish
  pointwise from an exact centered-weight dot-product identity.
- M7 optimality transfer: marked binary populations and marked indicator
  weights reproduce every centered hypergeometric MGF exactly inside the
  weighted problem.  Conversely, a fixed finite population randomized by a
  uniform permutation is proved exchangeable.  These two embeddings transfer
  hypergeometric minimality to both `finitePopulation_sharp_constant` and
  `exchangeable_sharp_constant`.
- Ancillary identities used explicitly in the manuscript are kernel-checked:
  the exact finite-population variance identity (2), the full hypergeometric
  variance formula including deterministic boundary cases, and the
  characterization `ρ_N(w) = 0 ↔ w° = 0`.
- Proposition 1 is also represented literally as a supremum of the normalized
  log-MGF ratios.  `kappaStar_eq_kappa` evaluates that supremum, the odd branch
  has its stated nonzero equality witness, and the even branch has the stated
  fixed-slice small-tilt limit.
- Corollary 2 is now proved from the standard pushforward-measure definition of
  equality in distribution, not only from an expectation-invariance interface.
  The uniform-permutation construction is exchangeable in this standard sense,
  and `exchangeableInLaw_sharp_constant` proves both validity and minimality.
- The displayed parity-dependent expansions of `C_N^⋆` have explicit
  `O(N⁻³)` remainders, and `N(C_N^⋆ - 1) → 1` is kernel-checked.
- Corollary 1 sharpness is represented at the sample-mean level itself.
  `sampleMeanMgf_markedIndicator` gives the exact hypergeometric witness;
  `serfling_fixed_even_sharp` proves fixed-`n` minimality for even populations;
  `serfling_uniform_sharp_constant` proves uniform-in-`n` minimality; and
  `serfling_uniform_odd_witness` records the odd `n = 1` attainment.
- The comparison of all three finite-population corrections is checked by
  `serfling_correction_chain`. The strict odd inequality `κ_N < 1` is checked
  by `kappa_odd_lt_one`.
- The equality clause in manuscript Lemma 5 at `t = L_{N,2}` is exposed as
  `log_mgf_lowerNearest_two_eq_exact_at_increment`.
- `FullAxiomAudit.lean` audits every declaration in the `SharpSerfling`
  namespace automatically; CI also rejects all trust-bypassing source forms.

## Current milestone

Formalization complete for the 27-page `Sharp_Serfling (49).pdf` (SHA-256
`1b4f0ddc2fb8ed93cac9011f2f816d5938996181d30ce022fc970cc138cd`): all named theorems,
propositions, corollaries, and lemmas, together with the displayed variance,
variational-optimality, degeneracy, and asymptotic claims, are represented by
kernel-checked declarations. Every checked-in declaration is complete.
