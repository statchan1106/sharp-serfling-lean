import SharpSerfling.FinitePopulation.WeightCentering

namespace SharpSerfling.FinitePopulation

open scoped BigOperators Pointwise

open SharpSerfling.Hypergeometric

/-- Positions at which a population takes the value one. -/
noncomputable def successSet {N : ℕ} (v : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun j ↦ v j = 1

/-- Number of ones in a population. -/
noncomputable def successCount {N : ℕ} (v : Fin N → ℝ) : ℕ :=
  (successSet v).card

/-- The set of ones, bundled as a fixed-cardinality sample. -/
noncomputable def successSample {N : ℕ} (v : Fin N → ℝ) : Sample N (successCount v) :=
  ⟨successSet v, rfl⟩

@[simp] theorem mem_successSet {N : ℕ} (v : Fin N → ℝ) (j : Fin N) :
    j ∈ successSet v ↔ v j = 1 := by
  simp [successSet]

theorem successCount_le {N : ℕ} (v : Fin N → ℝ) : successCount v ≤ N := by
  unfold successCount
  calc
    (successSet v).card ≤ (Finset.univ : Finset (Fin N)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = N := by simp

/-- Multiplying a zero extension by an arbitrary function can be performed
before the extension. -/
theorem zeroPad_mul {N n : ℕ} (hn : n ≤ N) (w : Fin n → ℝ)
    (f : Fin N → ℝ) (j : Fin N) :
    zeroPad hn w j * f j =
      zeroPad hn (fun i ↦ w i * f (Fin.castLE hn i)) j := by
  classical
  by_cases h : ∃ i : Fin n, Fin.castLE hn i = j
  · obtain ⟨i, rfl⟩ := h
    simp
  · unfold zeroPad
    rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
    simp

/-- Sum of zero-padded coefficients over a subset, expressed back in the
original coefficient coordinates. -/
theorem sum_zeroPad_subset {N n : ℕ} (hn : n ≤ N) (w : Fin n → ℝ)
    (s : Finset (Fin N)) :
    ∑ j ∈ s, zeroPad hn w j =
      ∑ i, w i * (if Fin.castLE hn i ∈ s then 1 else 0) := by
  classical
  rw [← Fintype.sum_extend_by_zero s (zeroPad hn w)]
  have hpoint (j : Fin N) :
      (if j ∈ s then zeroPad hn w j else 0) =
        zeroPad hn w j * (if j ∈ s then 1 else 0) := by
    by_cases hj : j ∈ s <;> simp [hj]
  rw [show (∑ j : Fin N, if j ∈ s then zeroPad hn w j else 0) =
      ∑ j : Fin N, zeroPad hn w j * (if j ∈ s then 1 else 0) by
    apply Finset.sum_congr rfl
    intro j hj
    exact hpoint j]
  rw [show (∑ j : Fin N, zeroPad hn w j * (if j ∈ s then 1 else 0)) =
      ∑ j : Fin N,
        zeroPad hn (fun i ↦ w i * (if Fin.castLE hn i ∈ s then 1 else 0)) j by
    apply Finset.sum_congr rfl
    intro j hj
    exact zeroPad_mul hn w (fun j ↦ if j ∈ s then 1 else 0) j]
  rw [sum_zeroPad]

/-- A binary population sums to its number of ones. -/
theorem sum_binary_eq_successCount {N : ℕ} (v : Fin N → ℝ)
    (hv : ∀ j, v j = 0 ∨ v j = 1) :
    ∑ j, v j = successCount v := by
  classical
  unfold successCount successSet
  calc
    ∑ j, v j = ∑ j, if v j = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rcases hv j with hj0 | hj1
      · simp [hj0]
      · simp [hj1]
    _ = ((Finset.univ.filter fun j ↦ v j = 1).card : ℝ) := by simp

/-- Pulling the set of successes back by a permutation detects precisely the
sample positions whose permuted population value is one. -/
theorem mem_inv_smul_successSample {N : ℕ} (v : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (j : Fin N) :
    j ∈ ((π⁻¹ • successSample v : Sample N (successCount v))).1 ↔
      v (π j) = 1 := by
  change j ∈ (π⁻¹ • successSet v : Finset (Fin N)) ↔ _
  constructor
  · intro hj
    obtain ⟨y, hy, heq⟩ := Finset.mem_smul_finset.mp hj
    have hyj : y = π j := by
      have h := congrArg π heq
      simpa using h
    simpa [hyj] using (mem_successSet v y).mp hy
  · intro hj
    apply Finset.mem_smul_finset.mpr
    refine ⟨π j, (mem_successSet v _).mpr hj, ?_⟩
    simp

/-- For a binary population, the weighted centered permutation statistic is
exactly a subset sum of the centered zero-padded coefficient vector. -/
theorem statistic_binary_eq_subsetSum {N n : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (v : Fin N → ℝ) (hv : ∀ j, v j = 0 ∨ v j = 1)
    (w : Fin n → ℝ) (π : Equiv.Perm (Fin N)) :
    statistic hn v w π =
      ∑ j ∈ ((π⁻¹ • successSample v : Sample N (successCount v))).1,
        centeredWeight hn w j := by
  classical
  have hmean : SharpSerfling.populationMean v =
      (successCount v : ℝ) / (N : ℝ) := by
    unfold SharpSerfling.populationMean
    rw [sum_binary_eq_successCount v hv]
  have hselected :
      (∑ j ∈ ((π⁻¹ • successSample v : Sample N (successCount v))).1,
          zeroPad hn w j) =
        ∑ i, w i * v (π (Fin.castLE hn i)) := by
    rw [sum_zeroPad_subset]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hs : Fin.castLE hn i ∈
        ((π⁻¹ • successSample v : Sample N (successCount v))).1
    · have h1 := (mem_inv_smul_successSample v π _).mp hs
      rw [if_pos hs, h1]
    · have hn1 : v (π (Fin.castLE hn i)) ≠ 1 := by
        intro h1
        exact hs ((mem_inv_smul_successSample v π _).mpr h1)
      rcases hv (π (Fin.castLE hn i)) with h0 | h1
      · rw [if_neg hs, h0]
      · exact (hn1 h1).elim
  rw [show (∑ j ∈ ((π⁻¹ • successSample v : Sample N (successCount v))).1,
      centeredWeight hn w j) =
      (∑ j ∈ ((π⁻¹ • successSample v : Sample N (successCount v))).1,
        zeroPad hn w j) -
        (successCount v : ℝ) * ((∑ i, w i) / (N : ℝ)) by
    unfold centeredWeight
    rw [Finset.sum_sub_distrib]
    simp [successSample, successCount]]
  rw [hselected]
  unfold statistic
  rw [hmean]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- Exact bridge from the permutation MGF of a binary population to the
Hamming-slice MGF of its centered, zero-padded coefficient vector. -/
theorem mgf_binary_eq_sliceMgf {N n : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (v : Fin N → ℝ) (hv : ∀ j, v j = 0 ∨ v j = 1)
    (w : Fin n → ℝ) (t : ℝ) :
    mgf hn v w t =
      sliceMgf N (successCount v) (fun j ↦ t * centeredWeight hn w j) := by
  let s₀ : Sample N (successCount v) := successSample v
  let f : Sample N (successCount v) → ℝ := fun s ↦
    Real.exp (∑ j ∈ s.1, t * centeredWeight hn w j)
  have hK : successCount v ≤ N := successCount_le v
  calc
    mgf hn v w t = SharpSerfling.finiteAverage (fun π : Equiv.Perm (Fin N) ↦
        f (π⁻¹ • s₀)) := by
      unfold mgf
      apply congrArg SharpSerfling.finiteAverage
      funext π
      unfold f s₀
      rw [statistic_binary_eq_subsetSum hN hn v hv w π, Finset.mul_sum]
    _ = SharpSerfling.finiteAverage (fun π : Equiv.Perm (Fin N) ↦ f (π • s₀)) := by
      exact SharpSerfling.finiteAverage_inv
        (fun π : Equiv.Perm (Fin N) ↦ f (π • s₀))
    _ = SharpSerfling.finiteAverage f := finiteAverage_sample_orbit hK s₀ f
    _ = sliceMgf N (successCount v) (fun j ↦ t * centeredWeight hn w j) := by
      unfold sliceMgf f
      rfl

end SharpSerfling.FinitePopulation
