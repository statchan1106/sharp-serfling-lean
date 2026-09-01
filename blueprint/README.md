# Proof blueprint

This guide follows the mathematical dependency structure of *A Sharp
Variance-Scale Refinement of Serfling's Inequality* and records the Lean
declarations that certify each step. The relationship between the paper and
the larger Lean verification boundary is summarized in
[MANUSCRIPT.md](../MANUSCRIPT.md).

## Destination

For a fixed population $X \in [a,b]^N$, a uniform permutation $\pi$, and
weights $w \in \mathbb R^n$, define

$$
\begin{aligned}
T_w&=\sum_{i=1}^n w_i(X_{\pi(i)}-\bar X_N),\\
\rho_N(w)&=\frac{N\sum_i w_i^2-(\sum_i w_i)^2}{N-1}.
\end{aligned}
$$

The main theorem proves

$$
\log \mathbb E e^{tT_w}
\le
\frac{\kappa_N}{8}\rho_N(w)(b-a)^2t^2.
$$

where

$$
\kappa_N =
\begin{cases}
1, & N \text{ even},\\
\displaystyle\frac{2}{N\log((N+1)/(N-1))}, & N \text{ odd}.
\end{cases}
$$

The Lean entry points are
`SharpSerfling.FinitePopulation.finitePopulation_mgf` and
`SharpSerfling.FinitePopulation.finitePopulation_sharp_constant`.

## Proof boundary

Section 3 invokes two ingredients from
[*A Sharper Hoeffding Bound for Weighted Sums of Exchangeable Random
Variables*](https://arxiv.org/abs/2608.04900): the binary-population reduction
from the proof of Theorem 1 and the two-level extremal-coefficient reduction
from Proposition 2. The present paper then evaluates the centered
hypergeometric problem left by that reduction. The earlier argument is also
available as an [independent Lean project](https://github.com/statchan1106/exchangeable-hoeffding-lean).

This repository checks a larger dependency graph. It proves both imported
structural reductions internally and then checks the new hypergeometric
recursion, sharp constant, and consequences. A reader should therefore
distinguish:

- **earlier Hoeffding-paper dependency:** binary and two-level reductions;
- **new argument in the present paper:** Sections 4--5 and the transfers of the sharp
  constant;
- **Lean verification boundary:** both parts.

## Dependency route

```text
centered weights + affine range normalization
  -> binary endpoint population
  -> fixed-cardinality subset / Hamming slice
  -> two-level slice maximizer
  -> centered hypergeometric MGF
  -> derivative recursion (N,K,m) -> (N-2,K-1,m-1)
  -> universal even branch + sharp odd branch
  -> hypergeometric sharpness
  -> weighted finite-population theorem
  -> Serfling and exchangeable corollaries
```

## 1. Centering and binary reduction

The zero-padded coefficient vector is projected away from the constant
direction. The development proves the exact norm identity

$$
\rho_N(w)=\frac{N}{N-1}\lVert w^\circ\rVert_2^2.
$$

After affine normalization of the population range, convexity moves the maximum
of the permutation MGF from the interval cube to a binary vertex. A binary
population with $K$ ones turns the permutation average into a uniform
$K$-subset average.

Lean certificates:

- `FinitePopulation.sum_sq_centeredWeight_eq_rho`
- `FinitePopulation.statistic_affine`
- `FinitePopulation.binaryRangeReduction`
- `FinitePopulation.finiteAverage_sample_orbit`
- `FinitePopulation.mgf_binary_eq_sliceMgf`

## 2. The two-level extremizer (the cited reduction, proved internally)

The present paper uses the two-level reduction from Proposition 2 of the
earlier Hoeffding paper. The Lean development proves it internally. On the centered
fixed-radius sphere, compactness supplies a slice-MGF maximizer. The slice
numerator is expressed through elementary symmetric polynomials. After
isolating any three coordinates, a constrained-circle argument, a
repeated-Rolle theorem, and a Hermite interpolation sign lemma rule out three
distinct coordinate values at a global maximum.

Lean certificates:

- `FinitePopulation.exists_sliceMgf_maximizer`
- `Analysis.exists_iteratedDeriv_five_eq_zero_of_three_double_roots`
- `Analysis.hermite_weighted_deriv_pos`
- `Analysis.threePoint_globalMax_has_duplicate`
- `FinitePopulation.exists_twoLevel_sliceMgf_maximizer`
- `FinitePopulation.sliceLogMgf_le`

## 3. The hypergeometric bridge

A centered two-level subset sum is exactly a scaled centered hypergeometric
count. For its MGF $G_{N,K,m}$, the key differential identity is

$$
G'_{N,K,m}(t)
=2v_{N,K,m}e^{r_{N,K,m}t}\sinh(t/2)
G_{N-2,K-1,m-1}(t),
$$

with

$$
v_{N,K,m}
=\frac{K(N-K)m(N-m)}{N^2(N-1)}
=\text{Var}(H_{N,K,m}).
$$

The variance prefactor is what preserves $m(N-m)/(N-1)$ through the
induction. This is Lemma 2, equation (13), in the current manuscript.

Lean certificates:

- `FinitePopulation.sliceMgf_canonicalTwoLevel`
- `Hypergeometric.deriv_mgf_recursion`
- `Hypergeometric.mgf_successComplement`
- `Hypergeometric.mgf_sampleComplement`
- `Hypergeometric.actualVariance_eq_variance`
- `Hypergeometric.sinh_le_mul_exp_sq_div_six`
- `Hypergeometric.two_sinh_div_le_exp_sq_div_twentyFour`

## 4. The parity split

For even $N$, the coefficient-one bound is sharp because an exactly balanced
population exists. For odd $N$, the nearest-balanced Bernoulli law identifies
the smaller candidate constant. The remaining induction separates noncentral
slices, where pointwise derivative domination works, from one hard central
slice, where the accumulated derivative difference is controlled by a
single-crossing signed-area comparison.

Lean certificates:

- `Hypergeometric.log_mgf_le_universal`
- `Hypergeometric.mgf_one_le_oddProxy`
- `Hypergeometric.mgf_lowerNearest_two_le_oddProxy`
- `Hypergeometric.log_mgf_lowerNearest_two_eq_exact_at_increment`
- `Hypergeometric.centralTwo_scale_le_oddProxy`
- `Hypergeometric.oddNoncentralEnvelope`
- `Analysis.singleCrossing_integral_nonneg`
- `Hypergeometric.centralParameters`
- `Certificates.P0_nonneg`, `P12_nonneg`, `P7_nonneg`
- `Hypergeometric.odd_mgf_le`
- `Hypergeometric.sharp_mgf`

## 5. Sharpness and consequences

The literal variational constant over all $K,m$, and nonzero tilts is proved
equal to $\kappa_N$. The finite-population result then specializes to the
variance-scale Serfling bound and transfers to bounded exchangeable vectors.

Lean certificates:

- `Hypergeometric.kappaStar_eq_kappa`
- `Hypergeometric.kappaStar_odd_attained`
- `Hypergeometric.tendsto_normalizedLogMgf_even_central`
- `Hypergeometric.sharp_constant`
- `FinitePopulation.serfling_mgf`
- `FinitePopulation.serfling_tail`
- `FinitePopulation.serfling_correction_chain`
- `FinitePopulation.serfling_fixed_even_sharp`
- `FinitePopulation.serfling_uniform_sharp_constant`
- `FinitePopulation.serfling_uniform_odd_witness`
- `FinitePopulation.weighted_exchangeable_mgf_centeredNorm_inLaw`
- `FinitePopulation.exchangeableInLaw_Cstar_sharp_constant`

See [DECLARATIONS.md](DECLARATIONS.md) for the compact result-by-result map and
the [project page](../docs/index.html) for the reader-oriented version.
