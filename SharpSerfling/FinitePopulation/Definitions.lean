import SharpSerfling.Basic
import SharpSerfling.FiniteAverage
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.GroupTheory.Perm.Fin

namespace SharpSerfling.FinitePopulation

open scoped BigOperators

/-- Weighted centered statistic associated with a permutation sample. -/
noncomputable def statistic {N n : ℕ} (hn : n ≤ N) (X : Fin N → ℝ) (w : Fin n → ℝ)
    (π : Equiv.Perm (Fin N)) : ℝ :=
  ∑ i, w i * (X (π (Fin.castLE hn i)) - SharpSerfling.populationMean X)

/-- MGF of the weighted statistic under a uniform random permutation. -/
noncomputable def mgf {N n : ℕ} (hn : n ≤ N) (X : Fin N → ℝ) (w : Fin n → ℝ)
    (t : ℝ) : ℝ :=
  SharpSerfling.finiteAverage fun π : Equiv.Perm (Fin N) =>
    Real.exp (t * statistic hn X w π)

theorem mgf_zero {N n : ℕ} (hn : n ≤ N) (X : Fin N → ℝ) (w : Fin n → ℝ) :
    mgf hn X w 0 = 1 := by
  simp [mgf, SharpSerfling.finiteAverage_one]

theorem mgf_pos {N n : ℕ} (hn : n ≤ N) (X : Fin N → ℝ) (w : Fin n → ℝ) (t : ℝ) :
    0 < mgf hn X w t := by
  exact SharpSerfling.finiteAverage_pos _ fun _ => Real.exp_pos _

/-- Exact statement of manuscript Theorem `thm:finite-population`. -/
def WeightedMGFStatement : Prop :=
  ∀ (N n : ℕ), 2 ≤ N → ∀ hn : n ≤ N,
  ∀ (a b : ℝ) (X : Fin N → ℝ),
    (∀ j, a ≤ X j ∧ X j ≤ b) →
  ∀ (w : Fin n → ℝ) (t : ℝ),
    Real.log (mgf hn X w t) ≤
      SharpSerfling.kappa N / 8 * SharpSerfling.rho N n w * (b - a) ^ 2 * t ^ 2

end SharpSerfling.FinitePopulation
