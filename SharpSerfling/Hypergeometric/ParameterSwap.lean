import SharpSerfling.Hypergeometric.Representation

namespace SharpSerfling.Hypergeometric

open scoped BigOperators
open Finset Finset.Nat

/-- Choosing two disjoint labelled groups is symmetric in their labels. -/
theorem choose_cross (n a b : ℕ) :
    n.choose a * (n - a).choose b = n.choose b * (n - b).choose a := by
  calc
    n.choose a * (n - a).choose b =
        n.choose (a + b) * (a + b).choose a := by
      rw [Nat.choose_mul (Nat.le_add_right a b)]
      congr 2 <;> omega
    _ = n.choose (a + b) * (a + b).choose b := by
      rw [Nat.choose_symm_add]
    _ = n.choose b * (n - b).choose a := by
      rw [Nat.choose_mul (Nat.le_add_left b a), Nat.add_comm]
      congr 2 <;> omega

/-- The unnormalised intersection-count coefficients agree after swapping the
two subset sizes. -/
theorem hypergeom_coefficient_swap {N K m i : ℕ} (hK : K ≤ N) (hm : m ≤ N)
    (hiK : i ≤ K) (him : i ≤ m) :
    N.choose K * (K.choose i * (N - K).choose (m - i)) =
      N.choose m * (m.choose i * (N - m).choose (K - i)) := by
  have hNKi : N - i - (K - i) = N - K := by omega
  have hNmi : N - i - (m - i) = N - m := by omega
  calc
    N.choose K * (K.choose i * (N - K).choose (m - i)) =
        (N.choose K * K.choose i) * (N - K).choose (m - i) := by ring
    _ = (N.choose i * (N - i).choose (K - i)) *
          (N - K).choose (m - i) := by rw [Nat.choose_mul hiK]
    _ = N.choose i *
          ((N - i).choose (K - i) * (N - i - (K - i)).choose (m - i)) := by
      rw [hNKi]
      ring
    _ = N.choose i *
          ((N - i).choose (m - i) * (N - i - (m - i)).choose (K - i)) := by
      rw [choose_cross]
    _ = (N.choose i * (N - i).choose (m - i)) *
          (N - m).choose (K - i) := by
      rw [hNmi]
      simp [mul_assoc]
    _ = (N.choose m * m.choose i) * (N - m).choose (K - i) := by
      rw [Nat.choose_mul him]
    _ = N.choose m * (m.choose i * (N - m).choose (K - i)) := by
      simp [mul_assoc]

theorem binomialSum_eq_sum_range {N K m : ℕ} (f : ℕ → ℝ) :
    binomialSum N K m f =
      ∑ i ∈ Finset.range (m + 1),
        (K.choose i * (N - K).choose (m - i) : ℕ) * f i := by
  rw [binomialSum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

/-- Terms past `min K m` vanish, so both parameter orders use the same count
index set. -/
theorem binomialSum_eq_sum_range_min {N K m : ℕ} (f : ℕ → ℝ) :
    binomialSum N K m f =
      ∑ i ∈ Finset.range (min K m + 1),
        (K.choose i * (N - K).choose (m - i) : ℕ) * f i := by
  rw [binomialSum_eq_sum_range]
  by_cases hKm : K ≤ m
  · rw [Nat.min_eq_left hKm]
    conv_lhs =>
      rw [show m + 1 = (K + 1) + (m - K) by omega, Finset.sum_range_add]
    have htail :
        (∑ j ∈ Finset.range (m - K),
          (K.choose (K + 1 + j) * (N - K).choose (m - (K + 1 + j)) : ℕ) *
            f (K + 1 + j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      norm_num
    rw [htail, add_zero]
  · have hmK : m ≤ K := Nat.le_of_not_ge hKm
    rw [Nat.min_eq_right hmK]

/-- Centering is symmetric in the success and sample parameters. -/
theorem center_swap (N K m : ℕ) : center N K m = center N m K := by
  unfold center
  ring

/-- Hypergeometric MGFs are invariant under swapping the number of marked
objects and the sample size. -/
theorem mgf_parameterSwap {N K m : ℕ} (hK : K ≤ N) (hm : m ≤ N) (t : ℝ) :
    mgf N K m t = mgf N m K t := by
  rw [mgf_eq_binomialMgf hK, mgf_eq_binomialMgf hm]
  unfold binomialMgf binomialAverage
  rw [binomialSum_eq_sum_range_min, binomialSum_eq_sum_range_min]
  rw [center_swap N K m]
  rw [Nat.min_comm m K]
  have hchooseK : (N.choose K : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hK
  have hchooseM : (N.choose m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hm
  apply mul_left_cancel₀ hchooseK
  apply mul_left_cancel₀ hchooseM
  field_simp [hchooseK, hchooseM]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiMin : i < min K m + 1 := Finset.mem_range.mp hi
  have hiK : i ≤ K := by omega
  have him : i ≤ m := by omega
  have hcoeff :
      (N.choose K : ℝ) *
          ((K.choose i : ℝ) * ((N - K).choose (m - i) : ℝ)) =
        (N.choose m : ℝ) *
          ((m.choose i : ℝ) * ((N - m).choose (K - i) : ℝ)) := by
    exact_mod_cast hypergeom_coefficient_swap hK hm hiK him
  calc
    (N.choose K : ℝ) *
        ((K.choose i * (N - K).choose (m - i) : ℕ) *
          Real.exp (t * ((i : ℝ) - center N m K))) =
      ((N.choose K : ℝ) *
          ((K.choose i : ℝ) * ((N - K).choose (m - i) : ℝ))) *
        Real.exp (t * ((i : ℝ) - center N m K)) := by
          push_cast
          ring
    _ = ((N.choose m : ℝ) *
          ((m.choose i : ℝ) * ((N - m).choose (K - i) : ℝ))) *
        Real.exp (t * ((i : ℝ) - center N m K)) := by rw [hcoeff]
    _ = (N.choose m : ℝ) *
        ((m.choose i * (N - m).choose (K - i) : ℕ) *
          Real.exp (t * ((i : ℝ) - center N m K))) := by
          push_cast
          ring

end SharpSerfling.Hypergeometric
