# Formalization status

The formalization is complete for the mathematical statements in
*A Sharp Variance-Scale Refinement of Serfling's Inequality*. The paper-level
proof boundary is explained in [MANUSCRIPT.md](MANUSCRIPT.md), and the
statement-by-statement map is in [TRACEABILITY.md](TRACEABILITY.md).

## At a glance

| Layer | Status | Principal endpoint |
|---|---|---|
| Exact variance and weight centering | complete | `FinitePopulation.statistic_variance_eq_rho_mul_populationVariance` |
| Binary-population reduction | complete | `FinitePopulation.binaryRangeReduction` |
| Two-level coefficient reduction | complete | `FinitePopulation.exists_twoLevel_sliceMgf_maximizer` |
| Centered hypergeometric recursion | complete | `Hypergeometric.deriv_mgf_recursion` |
| Universal coefficient-one bound | complete | `Hypergeometric.log_mgf_le_universal` |
| Sharp even/odd hypergeometric bound | complete | `Hypergeometric.sharp_mgf` |
| Variational optimality | complete | `Hypergeometric.kappaStar_eq_kappa`, `sharp_constant` |
| Weighted finite-population theorem | complete | `FinitePopulation.finitePopulation_mgf` |
| Serfling MGF, tails, and sharpness | complete | `FinitePopulation.serfling_mgf`, `serfling_uniform_sharp_constant` |
| Exchangeable transfer and sharpness | complete | `FinitePopulation.weighted_exchangeable_mgf_centeredNorm_inLaw`, `exchangeableInLaw_Cstar_sharp_constant` |
| Even/odd asymptotics | complete | `tendsto_nat_mul_exchangeableConstant_sub_one` |

## Proof coverage

### 1. Finite-population algebra

The project checks zero-padding and centering of the weights, the identity

$$
\rho_N(w)=\frac{N}{N-1}\lVert w^\circ\rVert_2^2,
$$

the exact variance formula

$$
\mathrm{Var}(T_w)=\rho_N(w)\sigma_N^2,
$$

and the equal-weight specialization
$\rho_N(w)=(N-n)/(n(N-1))$. Constant populations, the zero contrast, and
empty/full binary slices are explicit rather than hidden by positivity
assumptions.

### 2. Structural reduction

The paper invokes the binary and two-level reductions from
[*A Sharper Hoeffding Bound for Weighted Sums of Exchangeable Random
Variables*](https://arxiv.org/abs/2608.04900). The Lean verification proves
both internally:

1. convexity reduces an interval-valued population to a binary vertex;
2. permutation averaging is identified with a fixed-cardinality slice;
3. a centered fixed-radius slice MGF has a maximizer;
4. the repeated-Rolle, Hermite-sign, and three-coordinate arguments force a
   maximizer with at most two coordinate values;
5. a canonical two-level slice is exactly a scaled centered hypergeometric MGF.

This is a larger verification boundary than the one used in the paper.

### 3. Hypergeometric analysis

The exact success/sample complement identities, Stein representation, and
dimension-reducing derivative recursion are checked. The elementary estimate

$$
\frac{2\sinh(t/2)}{t}\le e^{t^2/24}
$$

is formalized through `sinh_le_mul_exp_sq_div_six` and
`two_sinh_div_le_exp_sq_div_twentyFour`. These inputs give the universal
coefficient-one bound.

For odd population sizes, the one-draw Kearns--Saul base, the exact central
two-draw calculation, the noncentral derivative comparison, the signed-area
single-crossing argument, and the three polynomial certificates are all
kernel-checked. Together with the even branch, they yield the parity-sharp
theorem `sharp_mgf`.

### 4. Optimality and consequences

The literal variational quantity $\kappa_N^\star$ is evaluated, including
the even small-tilt witness and the odd nonzero equality witness. The result is
then transferred back to:

- arbitrary signed weighted sampling without replacement;
- equal-weight Serfling MGF, upper/lower/two-sided tails, and correction
  comparisons;
- bounded exchangeable contrasts under equality in distribution;
- the best finite-population and exchangeable constants;
- the even/odd asymptotic expansions and
  $N(C_N^\star-1)\to1$.

## Acceptance and trust boundary

The repository is accepted as complete only if all of the following hold:

- `lake build` succeeds from the pinned toolchain;
- `AxiomAudit.lean` checks the headline theorems;
- `FullAxiomAudit.lean` checks every declaration in the `SharpSerfling`
  namespace;
- no project source contains `sorry`, `admit`, a project-defined `axiom`,
  `unsafe`, `implemented_by`, or `opaque`;
- the only reported foundations are `propext`, `Classical.choice`, and
  `Quot.sound`.

Run the complete audit with:

```sh
lake build
lake env lean AxiomAudit.lean
lake env lean FullAxiomAudit.lean
rg -n '\b(sorry|admit)\b|^\s*axiom\b|\b(unsafe|implemented_by|opaque)\b' . \
  --glob '*.lean' --glob '!**/.lake/**'
```
