import SharpSerfling.Hypergeometric.Representation

namespace SharpSerfling.Hypergeometric

open scoped BigOperators

/-- The variance of the centered hypergeometric count on the actual uniform
fixed-cardinality sample space.  This is deliberately separate from the
closed-form expression `variance`, so their equality is a theorem rather
than a definition. -/
noncomputable def actualVariance (N K m : ℕ) : ℝ :=
  SharpSerfling.finiteAverage (fun s : Sample N m ↦
    ((count K s : ℝ) - center N K m) ^ 2)

/-- The centered hypergeometric count has the advertised closed-form
variance for all nontrivial sample sizes and numbers of marked items. -/
theorem actualVariance_eq_variance_of_interior {N K m : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (hm0 : 0 < m) (hmN : m < N) :
    actualVariance N K m = variance N K m := by
  have hstein := binomialAverage_stein hK0 hKN hm0
    (fun i ↦ (i : ℝ) - center N K m)
  have hreduce := binomialAverage_weighted_reduction_real
    hK0 hKN hm0 hmN (fun _ ↦ (1 : ℝ))
  have hsmallK : K - 1 ≤ N - 2 := by omega
  have hsmallm : m - 1 ≤ N - 2 := by omega
  have hone : binomialAverage (N - 2) (K - 1) (m - 1)
      (fun _ ↦ (1 : ℝ)) = 1 :=
    binomialAverage_one hsmallK hsmallm
  have havg : actualVariance N K m =
      binomialAverage N K m
        (fun i ↦ ((i : ℝ) - center N K m) ^ 2) := by
    simpa [actualVariance] using
      (finiteAverage_count_eq_binomialAverage (N := N) (K := K) (m := m)
        (Nat.le_of_lt hKN) (fun i ↦ ((i : ℝ) - center N K m) ^ 2))
  rw [havg]
  rw [show (fun i : ℕ ↦ ((i : ℝ) - center N K m) ^ 2) =
      fun i : ℕ ↦ ((i : ℝ) - center N K m) *
        ((i : ℝ) - center N K m) by
        funext i
        ring]
  rw [hstein]
  simp only [Nat.cast_add, Nat.cast_one]
  have hdiff :
      (fun i : ℕ ↦
        ((K : ℝ) - (i : ℝ)) * ((m : ℝ) - (i : ℝ)) *
          ((i : ℝ) + 1 - center N K m -
            ((i : ℝ) - center N K m))) =
      fun i : ℕ ↦ ((K : ℝ) - (i : ℝ)) * ((m : ℝ) - (i : ℝ)) * 1 := by
    funext i
    push_cast
    ring
  rw [hdiff, hreduce, hone, mul_one]
  unfold variance
  rw [Nat.cast_sub (Nat.le_of_lt hKN), Nat.cast_sub (Nat.le_of_lt hmN)]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hK0.trans hKN))
  have hNm1Nat : N - 1 ≠ 0 := by omega
  have hNm1R : ((N - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hNm1Nat
  rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  field_simp [hNR, hNm1R]

/-- Zero marked items give a deterministic zero count, hence zero actual
variance and the same value as the closed formula. -/
theorem actualVariance_zeroSuccesses {N m : ℕ} (hm : m ≤ N) :
    actualVariance N 0 m = variance N 0 m := by
  letI : Nonempty (Sample N m) := sample_nonempty hm
  simp [actualVariance, count, marked, center, variance,
    SharpSerfling.finiteAverage_zero]

/-- All population items marked give a deterministic count, hence zero
actual variance and the same value as the closed formula. -/
theorem actualVariance_allSuccesses {N m : ℕ} (hN : 0 < N) (hm : m ≤ N) :
    actualVariance N N m = variance N N m := by
  letI : Nonempty (Sample N m) := sample_nonempty hm
  have hcenter : center N N m = (m : ℝ) := by
    unfold center
    have hNR : (N : ℝ) ≠ 0 := by positivity
    field_simp [hNR]
  have hcount (s : Sample N m) : count N s = m := by
    change (s.1 ∩ marked N N).card = m
    rw [show marked N N = Finset.univ by ext i; simp [marked]]
    simp [s.property]
  simp [actualVariance, hcount, hcenter, variance,
    SharpSerfling.finiteAverage_zero]

/-- Closed hypergeometric variance formula on the complete parameter range
used by the manuscript (`1 ≤ m ≤ N-1`, `0 ≤ K ≤ N`). -/
theorem actualVariance_eq_variance {N K m : ℕ} (hN : 2 ≤ N)
    (hK : K ≤ N) (hm0 : 1 ≤ m) (hmN : m ≤ N - 1) :
    actualVariance N K m = variance N K m := by
  by_cases hKzero : K = 0
  · subst K
    exact actualVariance_zeroSuccesses (by omega)
  by_cases hKall : K = N
  · subst K
    exact actualVariance_allSuccesses (by omega) (by omega)
  exact actualVariance_eq_variance_of_interior (by omega) (by omega) (by omega) (by omega)

end SharpSerfling.Hypergeometric
