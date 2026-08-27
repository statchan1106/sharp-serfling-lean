import SharpSerfling.Hypergeometric.Definitions
import Mathlib.Data.Nat.Choose.Vandermonde

namespace SharpSerfling.Hypergeometric

open scoped BigOperators
open Finset Finset.Nat

/-- The unnormalised hypergeometric weight attached to a decomposition `m = i + j`:
`i` marked objects and `j` unmarked objects. -/
def hypergeomWeight (N K : ℕ) (ij : ℕ × ℕ) : ℕ :=
  K.choose ij.1 * (N - K).choose ij.2

/-- The binomial-coefficient presentation of an unnormalised hypergeometric expectation. -/
noncomputable def binomialSum (N K m : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ ij ∈ antidiagonal m, (hypergeomWeight N K ij : ℝ) * f ij.1

/-- The binomial-coefficient presentation of a hypergeometric expectation. -/
noncomputable def binomialAverage (N K m : ℕ) (f : ℕ → ℝ) : ℝ :=
  (N.choose m : ℝ)⁻¹ * binomialSum N K m f

theorem sum_hypergeomWeight {N K m : ℕ} (hK : K ≤ N) :
    ∑ ij ∈ antidiagonal m, hypergeomWeight N K ij = N.choose m := by
  rw [show N = K + (N - K) by omega, Nat.add_choose_eq]
  simp [hypergeomWeight]

theorem binomialSum_one {N K m : ℕ} (hK : K ≤ N) :
    binomialSum N K m (fun _ ↦ 1) = (N.choose m : ℝ) := by
  rw [binomialSum]
  simp only [mul_one, ← Nat.cast_sum]
  exact_mod_cast sum_hypergeomWeight (m := m) hK

theorem binomialAverage_one {N K m : ℕ} (hK : K ≤ N) (hm : m ≤ N) :
    binomialAverage N K m (fun _ ↦ 1) = 1 := by
  rw [binomialAverage, binomialSum_one hK]
  exact inv_mul_cancel₀ (by exact_mod_cast Nat.choose_ne_zero hm)

theorem binomialSum_add (N K m : ℕ) (f g : ℕ → ℝ) :
    binomialSum N K m (fun i ↦ f i + g i) =
      binomialSum N K m f + binomialSum N K m g := by
  simp [binomialSum, mul_add, sum_add_distrib]

theorem binomialSum_smul (N K m : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    binomialSum N K m (fun i ↦ c * f i) = c * binomialSum N K m f := by
  simp [binomialSum, mul_assoc, mul_comm, Finset.mul_sum]

theorem binomialAverage_smul (N K m : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    binomialAverage N K m (fun i ↦ c * f i) = c * binomialAverage N K m f := by
  rw [binomialAverage, binomialAverage, binomialSum_smul]
  ring

private theorem choose_mul_remaining {n : ℕ} (hn : 0 < n) (k : ℕ) :
    n.choose k * (n - k) = n * (n - 1).choose k := by
  simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))] using
    (Nat.choose_mul_succ_eq (n - 1) k).symm.trans (Nat.mul_comm _ _)

private theorem choose_succ_mul {n : ℕ} (hn : 0 < n) (k : ℕ) :
    n.choose (k + 1) * (k + 1) = n * (n - 1).choose k := by
  simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))] using
    (Nat.add_one_mul_choose_eq (n - 1) k).symm

/-- Unnormalised form of the manuscript's weighted reduction.  The second coordinate
of an antidiagonal pair is the number of sampled failures. -/
theorem binomialWeightedSum_reduction {N K q : ℕ} (hK0 : 0 < K) (hKN : K < N)
    (g : ℕ → ℝ) :
    (∑ ij ∈ antidiagonal (q + 1),
        (hypergeomWeight N K ij : ℝ) * (K - ij.1) * ij.2 * g ij.1) =
      (K : ℝ) * (N - K : ℕ) * binomialSum (N - 2) (K - 1) q g := by
  rw [Finset.Nat.sum_antidiagonal_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
  rw [binomialSum]
  rw [mul_assoc, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hNK0 : 0 < N - K := Nat.sub_pos_of_lt hKN
  have hred : N - 2 - (K - 1) = N - K - 1 := by omega
  rw [hypergeomWeight, hypergeomWeight, hred]
  by_cases hiK : ij.1 ≤ K
  · rw [← Nat.cast_sub hiK]
    norm_cast
    have hnat :
        K.choose ij.1 * (N - K).choose (ij.2 + 1) * (K - ij.1) * (ij.2 + 1) =
          K * (N - K) * ((K - 1).choose ij.1 * (N - K - 1).choose ij.2) := by
      calc
        _ = (K.choose ij.1 * (K - ij.1)) *
              ((N - K).choose (ij.2 + 1) * (ij.2 + 1)) := by ring
        _ = (K * (K - 1).choose ij.1) *
              ((N - K) * (N - K - 1).choose ij.2) := by
                rw [choose_mul_remaining hK0, choose_succ_mul hNK0]
        _ = _ := by ring
    rw [hnat]
    push_cast
    ring
  · have hKi : K < ij.1 := Nat.lt_of_not_ge hiK
    have hpred : K - 1 < ij.1 := by omega
    simp [Nat.choose_eq_zero_of_lt hKi, Nat.choose_eq_zero_of_lt hpred]

/-- The same reduced sum obtained by shifting the marked coordinate instead of the
unmarked coordinate.  This is the detailed-balance partner of
`binomialWeightedSum_reduction`. -/
theorem binomialReverseWeightedSum_reduction {N K q : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (f : ℕ → ℝ) :
    (∑ ij ∈ antidiagonal (q + 1),
        (hypergeomWeight N K ij : ℝ) * ij.1 *
          ((N - K : ℕ) - ij.2) * f ij.1) =
      (K : ℝ) * (N - K : ℕ) *
        binomialSum (N - 2) (K - 1) q (fun i ↦ f (i + 1)) := by
  rw [Finset.Nat.sum_antidiagonal_succ]
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
  rw [binomialSum]
  rw [mul_assoc, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hNK0 : 0 < N - K := Nat.sub_pos_of_lt hKN
  have hred : N - 2 - (K - 1) = N - K - 1 := by omega
  rw [hypergeomWeight, hypergeomWeight, hred]
  by_cases hjNK : ij.2 ≤ N - K
  · rw [← Nat.cast_sub hjNK]
    norm_cast
    have hnat :
        K.choose (ij.1 + 1) * (N - K).choose ij.2 * (ij.1 + 1) *
            (N - K - ij.2) =
          K * (N - K) * ((K - 1).choose ij.1 * (N - K - 1).choose ij.2) := by
      calc
        _ = (K.choose (ij.1 + 1) * (ij.1 + 1)) *
              ((N - K).choose ij.2 * (N - K - ij.2)) := by ring
        _ = (K * (K - 1).choose ij.1) *
              ((N - K) * (N - K - 1).choose ij.2) := by
                rw [choose_succ_mul hK0, choose_mul_remaining hNK0]
        _ = _ := by ring
    rw [hnat]
    push_cast
    ring
  · have hNKi : N - K < ij.2 := Nat.lt_of_not_ge hjNK
    have hpred : N - K - 1 < ij.2 := by omega
    simp [Nat.choose_eq_zero_of_lt hNKi, Nat.choose_eq_zero_of_lt hpred]

/-- Detailed balance for adjacent hypergeometric counts. -/
theorem binomialStein_shift {N K m : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (hm0 : 0 < m) (f : ℕ → ℝ) :
    (∑ ij ∈ antidiagonal m,
        (hypergeomWeight N K ij : ℝ) * ((K : ℝ) - ij.1) * ij.2 * f (ij.1 + 1)) =
      ∑ ij ∈ antidiagonal m,
        (hypergeomWeight N K ij : ℝ) * ij.1 *
          ((N - K : ℕ) - ij.2) * f ij.1 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm0)
  simpa [Nat.succ_eq_add_one] using
    (binomialWeightedSum_reduction (q := q) hK0 hKN (fun i ↦ f (i + 1))).trans
      (binomialReverseWeightedSum_reduction (q := q) hK0 hKN f).symm

/-- Unnormalised hypergeometric Stein identity. -/
theorem binomialStein_raw {N K m : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (hm0 : 0 < m) (f : ℕ → ℝ) :
    (∑ ij ∈ antidiagonal m, (hypergeomWeight N K ij : ℝ) *
        ((N : ℝ) * ij.1 - (K : ℝ) * m) * f ij.1) =
      ∑ ij ∈ antidiagonal m, (hypergeomWeight N K ij : ℝ) *
        ((K : ℝ) - ij.1) * ((m : ℝ) - ij.1) *
          (f (ij.1 + 1) - f ij.1) := by
  symm
  calc
    (∑ ij ∈ antidiagonal m, (hypergeomWeight N K ij : ℝ) *
        ((K : ℝ) - ij.1) * ((m : ℝ) - ij.1) *
          (f (ij.1 + 1) - f ij.1)) =
        (∑ ij ∈ antidiagonal m, (hypergeomWeight N K ij : ℝ) *
          ((K : ℝ) - ij.1) * ij.2 * f (ij.1 + 1)) -
        (∑ ij ∈ antidiagonal m, (hypergeomWeight N K ij : ℝ) *
          ((K : ℝ) - ij.1) * ij.2 * f ij.1) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro ij hij
      have hijsum : ij.1 + ij.2 = m := Finset.mem_antidiagonal.mp hij
      have hijsumR : (ij.1 : ℝ) + (ij.2 : ℝ) = (m : ℝ) := by exact_mod_cast hijsum
      have hmj : (m : ℝ) - (ij.1 : ℝ) = (ij.2 : ℝ) := by linarith
      rw [hmj]
      ring
    _ = (∑ ij ∈ antidiagonal m, (hypergeomWeight N K ij : ℝ) * ij.1 *
          ((N - K : ℕ) - ij.2) * f ij.1) -
        (∑ ij ∈ antidiagonal m, (hypergeomWeight N K ij : ℝ) *
          ((K : ℝ) - ij.1) * ij.2 * f ij.1) := by
      rw [binomialStein_shift hK0 hKN hm0 f]
    _ = ∑ ij ∈ antidiagonal m, (hypergeomWeight N K ij : ℝ) *
        ((N : ℝ) * ij.1 - (K : ℝ) * m) * f ij.1 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro ij hij
      have hijsum : ij.1 + ij.2 = m := Finset.mem_antidiagonal.mp hij
      have hijsumR : (ij.1 : ℝ) + (ij.2 : ℝ) = (m : ℝ) := by exact_mod_cast hijsum
      have hNKcast : ((N - K : ℕ) : ℝ) = (N : ℝ) - (K : ℝ) := by
        exact_mod_cast Nat.cast_sub (Nat.le_of_lt hKN)
      rw [hNKcast, ← hijsumR]
      ring

/-- Normalised Stein identity in the exact centred form used to differentiate the MGF. -/
theorem binomialAverage_stein {N K m : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (hm0 : 0 < m) (f : ℕ → ℝ) :
    binomialAverage N K m (fun i ↦ ((i : ℝ) - center N K m) * f i) =
      (N : ℝ)⁻¹ * binomialAverage N K m (fun i ↦
        ((K : ℝ) - i) * ((m : ℝ) - i) * (f (i + 1) - f i)) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (hK0.trans hKN)
  have hcentered :
      (∑ ij ∈ antidiagonal m, (hypergeomWeight N K ij : ℝ) *
          (((ij.1 : ℝ) - center N K m) * f ij.1)) =
        (N : ℝ)⁻¹ *
          ∑ ij ∈ antidiagonal m, (hypergeomWeight N K ij : ℝ) *
            ((N : ℝ) * ij.1 - (K : ℝ) * m) * f ij.1 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    unfold center
    field_simp [hN]
  have hweighted :
      (∑ ij ∈ antidiagonal m, (hypergeomWeight N K ij : ℝ) *
          ((K : ℝ) - ij.1) * ((m : ℝ) - ij.1) *
            (f (ij.1 + 1) - f ij.1)) =
        ∑ ij ∈ antidiagonal m, (hypergeomWeight N K ij : ℝ) *
          (((K : ℝ) - ij.1) * ((m : ℝ) - ij.1) *
            (f (ij.1 + 1) - f ij.1)) := by
    apply Finset.sum_congr rfl
    intro ij hij
    ring
  rw [binomialAverage, binomialAverage, binomialSum, binomialSum, hcentered,
    binomialStein_raw hK0 hKN hm0 f, hweighted]
  ring

private theorem choose_reduction_cross {N m : ℕ} (hm0 : 0 < m) (hmN : m < N) :
    N.choose m * m * (N - m) =
      N * (N - 1) * (N - 2).choose (m - 1) := by
  have hN0 : 0 < N := hm0.trans hmN
  have hN1 : 0 < N - 1 := by omega
  have hfirst : N.choose m * m = N * (N - 1).choose (m - 1) := by
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hN0)),
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm0))] using
      (Nat.add_one_mul_choose_eq (N - 1) (m - 1)).symm
  have hsecond : (N - 1).choose (m - 1) * (N - m) =
      (N - 1) * (N - 2).choose (m - 1) := by
    have hs₁ : N - 1 - (m - 1) = N - m := by omega
    have hs₂ : N - 1 - 1 = N - 2 := by omega
    simpa [hs₁, hs₂] using choose_mul_remaining hN1 (m - 1)
  calc
    N.choose m * m * (N - m) =
        (N * (N - 1).choose (m - 1)) * (N - m) := by rw [hfirst]
    _ = N * ((N - 1).choose (m - 1) * (N - m)) := by ring
    _ = N * ((N - 1) * (N - 2).choose (m - 1)) := by rw [hsecond]
    _ = N * (N - 1) * (N - 2).choose (m - 1) := by ring

/-- Ratio of the two normalising binomial coefficients occurring in the reduction. -/
theorem choose_reduction_ratio {N m : ℕ} (hm0 : 0 < m) (hmN : m < N) :
    ((N - 2).choose (m - 1) : ℝ) / (N.choose m : ℝ) =
      (m : ℝ) * (N - m : ℕ) / ((N : ℝ) * (N - 1 : ℕ)) := by
  have hmNle : m ≤ N := Nat.le_of_lt hmN
  have hchoose : (N.choose m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hmNle
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hm0.trans hmN))
  have hN1 : (N - 1 : ℕ) ≠ 0 := by omega
  have hN1r : (N - 1 : ℕ) ≠ (0 : ℝ) := by exact_mod_cast hN1
  field_simp [hchoose, hN, hN1r]
  exact_mod_cast (show (N - 2).choose (m - 1) * N * (N - 1) =
      N.choose m * m * (N - m) by
    calc
      _ = N * (N - 1) * (N - 2).choose (m - 1) := by ring
      _ = _ := (choose_reduction_cross hm0 hmN).symm)

/-- Normalised weighted reduction, with exactly the coefficient appearing in the
hypergeometric Stein identity from the manuscript. -/
theorem binomialAverage_weighted_reduction {N K m : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (hm0 : 0 < m) (hmN : m < N)
    (g : ℕ → ℝ) :
    binomialAverage N K m (fun i ↦
        ((K - i : ℕ) : ℝ) * ((m - i : ℕ) : ℝ) * g i) =
      ((K : ℝ) * (N - K : ℕ) * (m : ℝ) * (N - m : ℕ) /
          ((N : ℝ) * (N - 1 : ℕ))) *
        binomialAverage (N - 2) (K - 1) (m - 1) g := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm0)
  have hsum :
      binomialSum N K (q + 1) (fun i ↦
          ((K - i : ℕ) : ℝ) * ((q + 1 - i : ℕ) : ℝ) * g i) =
        ∑ ij ∈ antidiagonal (q + 1),
          (hypergeomWeight N K ij : ℝ) * (K - ij.1) * ij.2 * g ij.1 := by
    rw [binomialSum]
    apply Finset.sum_congr rfl
    intro ij hij
    have hijsum : ij.1 + ij.2 = q + 1 := Finset.mem_antidiagonal.mp hij
    have hsub : q + 1 - ij.1 = ij.2 := by omega
    rw [hsub]
    by_cases hiK : ij.1 ≤ K
    · rw [Nat.cast_sub hiK]
      ring
    · have hKi : K < ij.1 := Nat.lt_of_not_ge hiK
      simp [hypergeomWeight, Nat.choose_eq_zero_of_lt hKi]
  have hraw := binomialWeightedSum_reduction (N := N) (K := K) (q := q) hK0 hKN g
  have hsmallLe : q ≤ N - 2 := by omega
  have hlargeLe : q + 1 ≤ N := Nat.le_of_lt hmN
  have hsmall : ((N - 2).choose q : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hsmallLe
  have hlarge : (N.choose (q + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hlargeLe
  have hratio := choose_reduction_ratio (N := N) (m := q + 1) (by omega) hmN
  have hratio' : ((N - 2).choose q : ℝ) / (N.choose (q + 1) : ℝ) =
      (q + 1 : ℝ) * (N - (q + 1) : ℕ) /
        ((N : ℝ) * (N - 1 : ℕ)) := by
    simpa using hratio
  have hinv : (N.choose (q + 1) : ℝ)⁻¹ =
      ((q + 1 : ℝ) * (N - (q + 1) : ℕ) /
          ((N : ℝ) * (N - 1 : ℕ))) * ((N - 2).choose q : ℝ)⁻¹ := by
    calc
      _ = (((N - 2).choose q : ℝ) / (N.choose (q + 1) : ℝ)) *
          ((N - 2).choose q : ℝ)⁻¹ := by field_simp
      _ = _ := by rw [hratio']
  rw [binomialAverage, binomialAverage, hsum, hraw, hinv]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  ring

/-- Real-subtraction form of the weighted reduction.  This is the form used by the
Stein identity and MGF recursion. -/
theorem binomialAverage_weighted_reduction_real {N K m : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (hm0 : 0 < m) (hmN : m < N)
    (g : ℕ → ℝ) :
    binomialAverage N K m (fun i ↦
        ((K : ℝ) - i) * ((m : ℝ) - i) * g i) =
      ((K : ℝ) * (N - K : ℕ) * (m : ℝ) * (N - m : ℕ) /
          ((N : ℝ) * (N - 1 : ℕ))) *
        binomialAverage (N - 2) (K - 1) (m - 1) g := by
  have heq :
      binomialAverage N K m (fun i ↦
          ((K : ℝ) - i) * ((m : ℝ) - i) * g i) =
        binomialAverage N K m (fun i ↦
          ((K - i : ℕ) : ℝ) * ((m - i : ℕ) : ℝ) * g i) := by
    rw [binomialAverage, binomialAverage, binomialSum, binomialSum]
    congr 1
    apply Finset.sum_congr rfl
    intro ij hij
    have hijsum : ij.1 + ij.2 = m := Finset.mem_antidiagonal.mp hij
    have him : ij.1 ≤ m := by omega
    rw [Nat.cast_sub him]
    by_cases hiK : ij.1 ≤ K
    · rw [Nat.cast_sub hiK]
    · have hKi : K < ij.1 := Nat.lt_of_not_ge hiK
      simp [hypergeomWeight, Nat.choose_eq_zero_of_lt hKi]
  rw [heq]
  exact binomialAverage_weighted_reduction hK0 hKN hm0 hmN g

end SharpSerfling.Hypergeometric
