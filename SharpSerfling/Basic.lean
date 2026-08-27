import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace SharpSerfling

open scoped BigOperators

/-- The parity-dependent sharp multiplier from the manuscript. -/
noncomputable def kappa (N : ℕ) : ℝ :=
  if Even N then 1
  else 2 / ((N : ℝ) * Real.log (((N : ℝ) + 1) / ((N : ℝ) - 1)))

/-- The exact variance scale of a zero-padded coefficient vector. -/
noncomputable def rho (N n : ℕ) (w : Fin n → ℝ) : ℝ :=
  ((N : ℝ) * ∑ i, (w i) ^ 2 - (∑ i, w i) ^ 2) / ((N : ℝ) - 1)

/-- The sample-size part of the quadratic hypergeometric proxy. -/
noncomputable def hypergeomScale (N m : ℕ) : ℝ :=
  (m : ℝ) * ((N : ℝ) - (m : ℝ)) / (8 * ((N : ℝ) - 1))

/-- The centered mean of a finite real population. -/
noncomputable def populationMean {N : ℕ} (X : Fin N → ℝ) : ℝ :=
  (∑ j, X j) / (N : ℝ)

theorem kappa_of_even {N : ℕ} (hN : Even N) : kappa N = 1 := by
  simp [kappa, hN]

theorem kappa_of_not_even {N : ℕ} (hN : ¬ Even N) :
    kappa N = 2 / ((N : ℝ) * Real.log (((N : ℝ) + 1) / ((N : ℝ) - 1))) := by
  simp [kappa, hN]

theorem hypergeomScale_symm (N m : ℕ) (hm : m ≤ N) :
    hypergeomScale N (N - m) = hypergeomScale N m := by
  simp only [hypergeomScale, Nat.cast_sub hm]
  ring

theorem kappa_pos {N : ℕ} (hN : 2 ≤ N) : 0 < kappa N := by
  rw [kappa]
  split_ifs with heven
  · norm_num
  · have hNm1 : 0 < (N : ℝ) - 1 := by
      have hcast : (1 : ℝ) < (N : ℝ) := by
        exact_mod_cast (show 1 < N by exact lt_of_lt_of_le (by norm_num) hN)
      linarith
    have hratio : 1 < ((N : ℝ) + 1) / ((N : ℝ) - 1) := by
      rw [one_lt_div hNm1]
      linarith
    have hlog : 0 < Real.log (((N : ℝ) + 1) / ((N : ℝ) - 1)) :=
      Real.log_pos hratio
    positivity

/-- Under equal weights, `rho` is exactly the finite-population correction. -/
theorem rho_equalWeights {N n : ℕ} (hn : 0 < n) (hN : 1 < N) :
    rho N n (fun _ => (1 : ℝ) / n) =
      ((N : ℝ) - (n : ℝ)) / ((n : ℝ) * ((N : ℝ) - 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hN0 : (N : ℝ) - 1 ≠ 0 := by
    have hcast : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    linarith
  simp only [rho, div_pow]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_pow]
  field_simp

theorem rho_nonneg {N n : ℕ} (hN : 2 ≤ N) (hn : n ≤ N) (w : Fin n → ℝ) :
    0 ≤ rho N n w := by
  have hcs : (∑ i, w i) ^ 2 ≤ (n : ℝ) * ∑ i, (w i) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w))
  have hsquares : 0 ≤ ∑ i, (w i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hncast : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
  have hnum : 0 ≤ (N : ℝ) * ∑ i, (w i) ^ 2 - (∑ i, w i) ^ 2 := by
    nlinarith
  have hden : 0 < (N : ℝ) - 1 := by
    have : (1 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 1 < N by omega)
    linarith
  exact div_nonneg hnum hden.le

end SharpSerfling
