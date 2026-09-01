# Paper alignment

This repository accompanies
*A Sharp Variance-Scale Refinement of Serfling's Inequality*.
The paper and the Lean project share the same mathematical destination but use
slightly different proof boundaries.

## Paper structure

| Paper part | Mathematical role | Main Lean location |
|---|---|---|
| Section 1, Introduction | Exact sampling variance, the Serfling question, and contributions | `FinitePopulation/Variance.lean`, `Serfling.lean` |
| Section 2, Main Results | Weighted MGF, equal-weight Serfling bound, exchangeable transfer, and hypergeometric optimization | `FinitePopulation/MainTheorem.lean`, `Serfling.lean`, `ExchangeableLaw.lean`, `Hypergeometric/Variational.lean` |
| Section 3, Reduction to Centered Hypergeometric MGFs | Binary-population and two-level coefficient reduction | `FinitePopulation/BinaryReduction.lean`, `TwoLevelReduction.lean`, `TwoLevelBound.lean` |
| Section 4, A Uniform Bound for Centered Hypergeometric MGFs | Exact recursion and the coefficient-one bound | `Hypergeometric/Recursion.lean`, `Representation.lean`, `Universal.lean` |
| Section 5, The Smallest Uniform MGF Constant | Parity split, odd induction, and sharpness | `Hypergeometric/Odd.lean`, `KearnsSaul.lean`, `SharpInduction.lean`, `Sharpness.lean` |
| Appendix A | Variance identity and proofs of the weighted consequences | `FinitePopulation/Variance.lean`, `MainTheorem.lean`, `Serfling.lean`, `ExchangeableLaw.lean` |
| Appendix B | Odd-case analytic lemmas and the single-crossing argument | `Hypergeometric/CentralTwo.lean`, `Analysis/SingleCrossing.lean`, `Certificates/CentralParameters.lean` |
| Appendix C | Polynomial certificates | `Certificates/Polynomial.lean` |

For a statement-by-statement mapping, see [TRACEABILITY.md](TRACEABILITY.md).

## Paper boundary and Lean boundary

Section 3 of the paper invokes two earlier ingredients from Lee--Kim (2026):
the binary-population reduction from the proof of their Theorem 1 and the
two-level extremal-coefficient reduction from their Proposition 2. The new
paper argument evaluates the centered hypergeometric problem left by this
reduction.

The Lean project closes a larger verification boundary. It proves both
structural reductions internally before checking the new recursion, the sharp
hypergeometric constant, and the transfers back to the weighted
finite-population and exchangeable statements. Consequently, the paper-facing
dependency and the kernel-checked dependency are both explicit and are not
conflated.

## Navigation convention

The documentation uses the paper's displayed theorem, proposition, lemma, and
equation numbers for navigation. Each number is paired with a descriptive
mathematical role and an exact Lean declaration so that the map remains useful
across later typesetting revisions.
