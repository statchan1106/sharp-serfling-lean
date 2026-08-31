# Manuscript alignment

## Publication status

The accompanying paper is currently a preprint in preparation and has not yet
been posted to arXiv. The project therefore does not publish a manuscript link
or bundle a private draft PDF.

Current title:

> *A Sharp Variance-Scale Refinement of Serfling's Inequality*

Current documentation snapshot:

- draft date: 2026-09-01;
- compiled length: 28 pages;
- PDF SHA-256: `93607a9d286a72d179f9bb94549f16291ccb6fe5b666ff6afd8d28883396e0cd`.

The hash identifies the private draft used to update the mapping without
placing that draft in the public repository. Descriptive theorem names in the
tables below are the stable identifiers; displayed numbers may change during
later typesetting revisions.

## Current paper structure

| Manuscript part | Mathematical role | Main Lean location |
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

## Relation to Lee--Kim (2026)

Section 3 of the manuscript invokes two earlier ingredients: the
binary-population reduction from the proof of their Theorem 1 and the two-level
extremal-coefficient reduction from their Proposition 2. The new manuscript
argument begins with the centered hypergeometric analysis that follows this
reduction.

The Lean project deliberately closes a larger verification boundary. It proves
both structural reductions internally before formalizing the new recursion,
the sharp hypergeometric constant, and the transfers back to the weighted
finite-population and exchangeable statements.

## Adding the paper link after arXiv release

Once the paper is public:

1. put the canonical arXiv abstract URL in `docs/assets/site-config.js` as the
   value of `paper`;
2. replace the paper-status badge target and label at the top of `README.md`;
3. replace the publication-status paragraph in this file with the public link
   and arXiv identifier;
4. update the snapshot date and hash only if the public version differs from
   the draft mapped in `TRACEABILITY.md`.

Until then, the empty `paper` value is intentional: the project site renders
“Paper · forthcoming” instead of exposing a broken or private link.
