import SharpSerfling.FinitePopulation.OrbitAverage

namespace SharpSerfling.FinitePopulation

open scoped BigOperators

/-- Extend a coefficient vector by zero from the first `n` positions to all
`N` population positions. -/
noncomputable def zeroPad {N n : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) : Fin N → ℝ :=
  Function.extend (Fin.castLE hn) w 0

@[simp] theorem zeroPad_castLE {N n : ℕ} (hn : n ≤ N) (w : Fin n → ℝ)
    (i : Fin n) :
    zeroPad hn w (Fin.castLE hn i) = w i := by
  exact (Fin.castLE_injective hn).extend_apply w 0 i

/-- A finite sum is unchanged by extension by zero along `Fin.castLE`. -/
theorem sum_zeroPad {N n : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) :
    ∑ j, zeroPad hn w j = ∑ i, w i := by
  classical
  let e : Fin n ↪ Fin N := Fin.castLEEmb hn
  have hsmall :
      (∑ j ∈ (Finset.univ : Finset (Fin n)).map e, zeroPad hn w j) =
        ∑ j : Fin N, zeroPad hn w j := by
    apply Finset.sum_subset
    · simp
    · intro j hj hjnot
      unfold zeroPad
      apply Function.extend_apply'
      simpa [e] using hjnot
  calc
    ∑ j : Fin N, zeroPad hn w j =
        ∑ j ∈ (Finset.univ : Finset (Fin n)).map e, zeroPad hn w j := hsmall.symm
    _ = ∑ i : Fin n, zeroPad hn w (e i) := by rw [Finset.sum_map]
    _ = ∑ i : Fin n, w i := by simp [e]

theorem sum_sq_zeroPad {N n : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) :
    ∑ j, (zeroPad hn w j) ^ 2 = ∑ i, (w i) ^ 2 := by
  classical
  let e : Fin n ↪ Fin N := Fin.castLEEmb hn
  have hsmall :
      (∑ j ∈ (Finset.univ : Finset (Fin n)).map e, (zeroPad hn w j) ^ 2) =
        ∑ j : Fin N, (zeroPad hn w j) ^ 2 := by
    apply Finset.sum_subset
    · simp
    · intro j hj hjnot
      have hz : zeroPad hn w j = 0 := by
        unfold zeroPad
        apply Function.extend_apply'
        simpa [e] using hjnot
      simp [hz]
  calc
    ∑ j : Fin N, (zeroPad hn w j) ^ 2 =
        ∑ j ∈ (Finset.univ : Finset (Fin n)).map e, (zeroPad hn w j) ^ 2 := hsmall.symm
    _ = ∑ i : Fin n, (zeroPad hn w (e i)) ^ 2 := by rw [Finset.sum_map]
    _ = ∑ i : Fin n, (w i) ^ 2 := by simp [e]

/-- Center the zero-padded coefficient vector over all `N` positions. -/
noncomputable def centeredWeight {N n : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) :
    Fin N → ℝ :=
  fun j ↦ zeroPad hn w j - (∑ i, w i) / (N : ℝ)

theorem sum_centeredWeight {N n : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (w : Fin n → ℝ) :
    ∑ j, centeredWeight hn w j = 0 := by
  unfold centeredWeight
  rw [Finset.sum_sub_distrib, sum_zeroPad]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hNR]
  ring

/-- Exact squared norm of the centered zero-padded weights. -/
theorem sum_sq_centeredWeight {N n : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (w : Fin n → ℝ) :
    ∑ j, (centeredWeight hn w j) ^ 2 =
      ((N : ℝ) * ∑ i, (w i) ^ 2 - (∑ i, w i) ^ 2) / (N : ℝ) := by
  unfold centeredWeight
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_sq_zeroPad]
  have hcross :
      (∑ x : Fin N, 2 * zeroPad hn w x * ((∑ i, w i) / (N : ℝ))) =
        2 * ((∑ i, w i) / (N : ℝ)) * ∑ x : Fin N, zeroPad hn w x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hcross, sum_zeroPad]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hNR]
  ring

/-- The norm identity in the manuscript's `rho` normalization. -/
theorem sum_sq_centeredWeight_eq_rho {N n : ℕ} (hN : 2 ≤ N) (hn : n ≤ N)
    (w : Fin n → ℝ) :
    ∑ j, (centeredWeight hn w j) ^ 2 =
      ((N : ℝ) - 1) / (N : ℝ) * SharpSerfling.rho N n w := by
  rw [sum_sq_centeredWeight (by omega) hn]
  unfold SharpSerfling.rho
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  field_simp [hNR, hNm1]

end SharpSerfling.FinitePopulation
