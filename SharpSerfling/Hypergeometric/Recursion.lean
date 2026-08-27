import SharpSerfling.Hypergeometric.Algebraic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace SharpSerfling.Hypergeometric

open scoped BigOperators
open Finset Finset.Nat

/-- The centred hypergeometric MGF in binomial-coefficient form. -/
noncomputable def binomialMgf (N K m : ℕ) (t : ℝ) : ℝ :=
  binomialAverage N K m fun i ↦ Real.exp (t * ((i : ℝ) - center N K m))

theorem binomialMgf_zero {N K m : ℕ} (hK : K ≤ N) (hm : m ≤ N) :
    binomialMgf N K m 0 = 1 := by
  rw [binomialMgf]
  simpa using binomialAverage_one (m := m) hK hm

/-- Termwise differentiation of the binomial-coefficient MGF. -/
theorem hasDerivAt_binomialMgf (N K m : ℕ) (t : ℝ) :
    HasDerivAt (binomialMgf N K m)
      (binomialAverage N K m fun i ↦
        ((i : ℝ) - center N K m) *
          Real.exp (t * ((i : ℝ) - center N K m))) t := by
  have hterm (ij : ℕ × ℕ) :
      HasDerivAt
        (fun u : ℝ ↦ (hypergeomWeight N K ij : ℝ) *
          Real.exp (u * ((ij.1 : ℝ) - center N K m)))
        ((hypergeomWeight N K ij : ℝ) *
          (((ij.1 : ℝ) - center N K m) *
            Real.exp (t * ((ij.1 : ℝ) - center N K m)))) t := by
    simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
      (hasDerivAt_exp_smul_const' ((ij.1 : ℝ) - center N K m) t).const_mul
        (hypergeomWeight N K ij : ℝ)
  unfold binomialMgf binomialAverage binomialSum
  convert ((HasDerivAt.fun_sum fun ij (_ : ij ∈ antidiagonal m) ↦ hterm ij).const_mul
    (N.choose m : ℝ)⁻¹) using 1 <;> ring

theorem deriv_binomialMgf (N K m : ℕ) (t : ℝ) :
    deriv (binomialMgf N K m) t =
      binomialAverage N K m fun i ↦
        ((i : ℝ) - center N K m) *
          Real.exp (t * ((i : ℝ) - center N K m)) :=
  (hasDerivAt_binomialMgf N K m t).deriv

/-- Moving between the original and reduced centering constants only introduces a
constant exponential factor. -/
theorem binomialAverage_center_shift (N K m : ℕ) (t : ℝ) :
    binomialAverage (N - 2) (K - 1) (m - 1) (fun i ↦
        Real.exp (t * ((i : ℝ) - center N K m))) =
      Real.exp (t * (center (N - 2) (K - 1) (m - 1) - center N K m)) *
        binomialMgf (N - 2) (K - 1) (m - 1) t := by
  rw [binomialMgf]
  calc
    binomialAverage (N - 2) (K - 1) (m - 1) (fun i ↦
        Real.exp (t * ((i : ℝ) - center N K m))) =
      binomialAverage (N - 2) (K - 1) (m - 1) (fun i ↦
        Real.exp (t * (center (N - 2) (K - 1) (m - 1) - center N K m)) *
          Real.exp (t * ((i : ℝ) - center (N - 2) (K - 1) (m - 1)))) := by
        apply congrArg
        funext i
        rw [← Real.exp_add]
        congr 1
        ring
    _ = _ := binomialAverage_smul _ _ _ _ _

/-- The shift of centering constants plus `1/2` is the manuscript's recursion tilt. -/
theorem centerShift_add_half_eq_recursionTilt {N K m : ℕ}
    (hN : 3 ≤ N) (hK0 : 0 < K) (hm0 : 0 < m) :
    center (N - 2) (K - 1) (m - 1) - center N K m + 1 / 2 =
      recursionTilt N K m := by
  have h2N : 2 ≤ N := by omega
  have h1K : 1 ≤ K := hK0
  have h1m : 1 ≤ m := hm0
  rw [center, center, recursionTilt, Nat.cast_sub h2N, Nat.cast_sub h1K,
    Nat.cast_sub h1m]
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hN2r : (N : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    linarith
  field_simp [hNr, hN2r]
  ring

theorem exp_sub_one_eq_two_exp_sinh (t : ℝ) :
    Real.exp t - 1 = 2 * Real.exp (t / 2) * Real.sinh (t / 2) := by
  rw [Real.sinh_eq, show t = t / 2 + t / 2 by ring, Real.exp_add, Real.exp_neg]
  have hexp : Real.exp (t / 2) ≠ 0 := Real.exp_ne_zero _
  field_simp [hexp]
  ring

/-- The Stein identity followed by weighted reduction, before rewriting the constant
exponential factor as the manuscript's tilt. -/
theorem deriv_binomialMgf_reduced {N K m : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (hm0 : 0 < m) (hmN : m < N) (t : ℝ) :
    deriv (binomialMgf N K m) t =
      (N : ℝ)⁻¹ * (Real.exp t - 1) *
        ((K : ℝ) * (N - K : ℕ) * (m : ℝ) * (N - m : ℕ) /
          ((N : ℝ) * (N - 1 : ℕ))) *
        Real.exp (t * (center (N - 2) (K - 1) (m - 1) - center N K m)) *
        binomialMgf (N - 2) (K - 1) (m - 1) t := by
  let f : ℕ → ℝ := fun i ↦ Real.exp (t * ((i : ℝ) - center N K m))
  have hdiff :
      binomialAverage N K m (fun i ↦
          ((K : ℝ) - i) * ((m : ℝ) - i) * (f (i + 1) - f i)) =
        (Real.exp t - 1) * binomialAverage N K m (fun i ↦
          ((K : ℝ) - i) * ((m : ℝ) - i) * f i) := by
    calc
      _ = binomialAverage N K m (fun i ↦ (Real.exp t - 1) *
          (((K : ℝ) - i) * ((m : ℝ) - i) * f i)) := by
        apply congrArg
        funext i
        dsimp [f]
        rw [show t * (((i + 1 : ℕ) : ℝ) - center N K m) =
            t + t * ((i : ℝ) - center N K m) by push_cast; ring,
          Real.exp_add]
        ring
      _ = _ := binomialAverage_smul _ _ _ _ _
  rw [deriv_binomialMgf, binomialAverage_stein hK0 hKN hm0 f, hdiff,
    binomialAverage_weighted_reduction_real hK0 hKN hm0 hmN f,
    binomialAverage_center_shift]
  ring

private theorem inv_mul_weightedFactor_eq_variance {N K m : ℕ}
    (hN : 3 ≤ N) (hKN : K < N) (hmN : m < N) :
    (N : ℝ)⁻¹ *
        ((K : ℝ) * (N - K : ℕ) * (m : ℝ) * (N - m : ℕ) /
          ((N : ℝ) * (N - 1 : ℕ))) =
      variance N K m := by
  have hKle : K ≤ N := Nat.le_of_lt hKN
  have hmle : m ≤ N := Nat.le_of_lt hmN
  have h1N : 1 ≤ N := by omega
  unfold variance
  rw [Nat.cast_sub hKle, Nat.cast_sub hmle, Nat.cast_sub h1N]
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hNgt : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hN1r : (N : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hNr, hN1r]
  ring

/-- Manuscript dimension-reducing differential identity for the binomial presentation
of the centred hypergeometric MGF. -/
theorem deriv_binomialMgf_recursion {N K m : ℕ}
    (hN : 3 ≤ N) (hK0 : 0 < K) (hKN : K < N)
    (hm0 : 0 < m) (hmN : m < N) (t : ℝ) :
    deriv (binomialMgf N K m) t =
      2 * variance N K m * Real.exp (recursionTilt N K m * t) *
        Real.sinh (t / 2) * binomialMgf (N - 2) (K - 1) (m - 1) t := by
  rw [deriv_binomialMgf_reduced hK0 hKN hm0 hmN t,
    exp_sub_one_eq_two_exp_sinh]
  have hvar := inv_mul_weightedFactor_eq_variance (N := N) (K := K) (m := m)
    hN hKN hmN
  have hshift := centerShift_add_half_eq_recursionTilt (N := N) (K := K) (m := m)
    hN hK0 hm0
  have hexp :
      Real.exp (t / 2) *
          Real.exp (t * (center (N - 2) (K - 1) (m - 1) - center N K m)) =
        Real.exp (recursionTilt N K m * t) := by
    rw [← Real.exp_add]
    congr 1
    rw [← hshift]
    ring
  calc
    (N : ℝ)⁻¹ * (2 * Real.exp (t / 2) * Real.sinh (t / 2)) *
          ((K : ℝ) * (N - K : ℕ) * (m : ℝ) * (N - m : ℕ) /
            ((N : ℝ) * (N - 1 : ℕ))) *
          Real.exp (t * (center (N - 2) (K - 1) (m - 1) - center N K m)) *
          binomialMgf (N - 2) (K - 1) (m - 1) t =
        2 * ((N : ℝ)⁻¹ *
          ((K : ℝ) * (N - K : ℕ) * (m : ℝ) * (N - m : ℕ) /
            ((N : ℝ) * (N - 1 : ℕ)))) *
          (Real.exp (t / 2) *
            Real.exp (t * (center (N - 2) (K - 1) (m - 1) - center N K m))) *
          Real.sinh (t / 2) * binomialMgf (N - 2) (K - 1) (m - 1) t := by ring
    _ = _ := by rw [hvar, hexp]

end SharpSerfling.Hypergeometric
