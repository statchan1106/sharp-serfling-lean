import SharpSerfling.FinitePopulation.ElementarySymmetric

namespace SharpSerfling.FinitePopulation

open scoped BigOperators
open SharpSerfling.Hypergeometric
open SharpSerfling.Analysis

/-- A global slice-MGF maximizer on a fixed-sum, fixed-square section cannot
take three distinct values at three distinct coordinates.  This is the global
lifting step from the three-coordinate lemma. -/
theorem sliceMgf_globalMax_triple_duplicate {N K : ℕ}
    (hK0 : 1 ≤ K) (hKN : K ≤ N - 1) {y : Fin N → ℝ}
    (hmax : ∀ x : Fin N → ℝ,
      (∑ l, x l) = ∑ l, y l → sqNorm x = sqNorm y →
      sliceMgf N K x ≤ sliceMgf N K y)
    {i j k : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    y i = y j ∨ y i = y k ∨ y j = y k := by
  let M : Multiset ℝ :=
    (remainingIndices i j k).val.map (fun l ↦ Real.exp (y l))
  have hself := replaceThree_self y hij hik hjk
  have hsumY : (∑ l, y l) =
      y i + y j + y k + ∑ l ∈ remainingIndices i j k, y l := by
    rw [← sum_replaceThree y hij hik hjk (y i) (y j) (y k)]
    rw [hself]
  have hsqY : sqNorm y =
      (y i) ^ 2 + (y j) ^ 2 + (y k) ^ 2 +
        ∑ l ∈ remainingIndices i j k, (y l) ^ 2 := by
    unfold sqNorm
    rw [← sum_sq_replaceThree y hij hik hjk (y i) (y j) (y k)]
    rw [hself]
  have hKleN : K ≤ N := by omega
  have hsample : Nonempty (Sample N K) := sample_nonempty hKleN
  have hcardNat : 0 < Fintype.card (Sample N K) := Fintype.card_pos_iff.mpr hsample
  have hcard : (0 : ℝ) < Fintype.card (Sample N K) := by exact_mod_cast hcardNat
  have hnumMax (u v z : ℝ)
      (hs : u + v + z = y i + y j + y k)
      (hq : u ^ 2 + v ^ 2 + z ^ 2 =
        (y i) ^ 2 + (y j) ^ 2 + (y k) ^ 2) :
      sliceNumerator N K (replaceThree y i j k u v z) ≤ sliceNumerator N K y := by
    have hsum : (∑ l, replaceThree y i j k u v z l) = ∑ l, y l := by
      rw [sum_replaceThree y hij hik hjk]
      rw [hs]
      exact hsumY.symm
    have hsq : sqNorm (replaceThree y i j k u v z) = sqNorm y := by
      unfold sqNorm
      rw [sum_sq_replaceThree y hij hik hjk]
      rw [hq]
      exact hsqY.symm
    have hm := hmax (replaceThree y i j k u v z) hsum hsq
    rw [sliceMgf_eq_sliceNumerator_div, sliceMgf_eq_sliceNumerator_div] at hm
    exact (div_le_div_iff_of_pos_right hcard).mp hm
  have hMnonneg : ∀ x ∈ M, 0 ≤ x := by
    intro x hx
    dsimp [M] at hx
    simp only [Multiset.mem_map] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    exact (Real.exp_pos (y l)).le
  have hMpos : ∀ x ∈ M, 0 < x := by
    intro x hx
    dsimp [M] at hx
    simp only [Multiset.mem_map] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    exact Real.exp_pos (y l)
  by_cases hK1 : K = 1
  · subst K
    apply threePoint_globalMax_has_duplicate (A := 1) (B := 0)
      (by norm_num) (by norm_num) (by norm_num)
    intro u v z hs hq
    have hn := hnumMax u v z hs hq
    have hvar := sliceNumerator_replaceThree_one y hij hik hjk u v z
    have horig : sliceNumerator N 1 y =
        M.esymm 1 + (Real.exp (y i) + Real.exp (y j) + Real.exp (y k)) := by
      calc
        _ = sliceNumerator N 1 (replaceThree y i j k (y i) (y j) (y k)) := by
          rw [hself]
        _ = _ := by simpa [M] using
          sliceNumerator_replaceThree_one y hij hik hjk (y i) (y j) (y k)
    rw [hvar, horig] at hn
    have hMeq :
        ((remainingIndices i j k).val.map (fun l ↦ Real.exp (y l))).esymm 1 =
          M.esymm 1 := rfl
    rw [hMeq] at hn
    unfold expPair
    nlinarith
  by_cases hK2 : K = 2
  · subst K
    have hC1 : 0 ≤ M.esymm 1 := Multiset.esymm_nonneg hMnonneg
    let s := y i + y j + y k
    apply threePoint_globalMax_has_duplicate (A := M.esymm 1) (B := Real.exp s)
      hC1 (Real.exp_pos s).le
      (add_pos_of_nonneg_of_pos hC1 (Real.exp_pos s))
    intro u v z hs hq
    have hn := hnumMax u v z hs hq
    have hvar := sliceNumerator_replaceThree_two y hij hik hjk u v z
    have horig : sliceNumerator N 2 y =
        M.esymm 2 + (Real.exp (y i) + Real.exp (y j) + Real.exp (y k)) * M.esymm 1 +
          (Real.exp (y i + y j) + Real.exp (y i + y k) + Real.exp (y j + y k)) := by
      calc
        _ = sliceNumerator N 2 (replaceThree y i j k (y i) (y j) (y k)) := by
          rw [hself]
        _ = _ := by simpa [M] using
          sliceNumerator_replaceThree_two y hij hik hjk (y i) (y j) (y k)
    rw [hvar, horig] at hn
    have hpvar := exp_pair_sum_eq_of_sum (s := s) hs
    have hporig := exp_pair_sum_eq_of_sum
      (u := y i) (v := y j) (z := y k) (s := s) rfl
    rw [hpvar, hporig] at hn
    unfold expPair
    nlinarith
  have hK3 : 3 ≤ K := by omega
  have hC1 : 0 ≤ M.esymm (K - 1) := Multiset.esymm_nonneg hMnonneg
  have hC2 : 0 ≤ M.esymm (K - 2) := Multiset.esymm_nonneg hMnonneg
  let s := y i + y j + y k
  let A := M.esymm (K - 1)
  let B := M.esymm (K - 2) * Real.exp s
  have hMcard : M.card = N - 3 := by
    dsimp [M]
    rw [Multiset.card_map]
    exact card_remainingIndices hij hik hjk
  have hABpos : 0 < A + B := by
    by_cases hKsmall : K ≤ N - 2
    · have hC1pos : 0 < M.esymm (K - 1) := by
        apply Multiset.esymm_pos hMpos
        rw [hMcard]
        omega
      exact add_pos_of_pos_of_nonneg hC1pos
        (mul_nonneg hC2 (Real.exp_pos s).le)
    · have hKeq : K = N - 1 := by omega
      have hC2pos : 0 < M.esymm (K - 2) := by
        apply Multiset.esymm_pos hMpos
        rw [hMcard]
        omega
      exact add_pos_of_nonneg_of_pos hC1
        (mul_pos hC2pos (Real.exp_pos s))
  apply threePoint_globalMax_has_duplicate (A := A) (B := B)
    hC1 (mul_nonneg hC2 (Real.exp_pos s).le) hABpos
  intro u v z hs hq
  have hn := hnumMax u v z hs hq
  have hvar := sliceNumerator_replaceThree_of_three_le hK3 y hij hik hjk u v z
  have horig : sliceNumerator N K y =
      M.esymm K + (Real.exp (y i) + Real.exp (y j) + Real.exp (y k)) * M.esymm (K - 1) +
        (Real.exp (y i + y j) + Real.exp (y i + y k) + Real.exp (y j + y k)) *
          M.esymm (K - 2) + Real.exp (y i + y j + y k) * M.esymm (K - 3) := by
    calc
      _ = sliceNumerator N K (replaceThree y i j k (y i) (y j) (y k)) := by
        rw [hself]
      _ = _ := by
        simpa [M] using sliceNumerator_replaceThree_of_three_le hK3 y
          hij hik hjk (y i) (y j) (y k)
  rw [hvar, horig] at hn
  have hpvar := exp_pair_sum_eq_of_sum (s := s) hs
  have hporig := exp_pair_sum_eq_of_sum
    (u := y i) (v := y j) (z := y k) (s := s) rfl
  rw [hpvar, hporig] at hn
  have hexpvar : Real.exp (u + v + z) = Real.exp s := by rw [hs]
  have hexporig : Real.exp (y i + y j + y k) = Real.exp s := rfl
  rw [hexpvar, hexporig] at hn
  dsimp [A, B]
  unfold expPair
  nlinarith

/-- A vector has at most two distinct coordinate values. -/
def HasAtMostTwoValues {N : ℕ} (y : Fin N → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ i, y i = a ∨ y i = b

theorem hasAtMostTwoValues_of_triple_duplicate {N : ℕ} (hN : 0 < N)
    {y : Fin N → ℝ}
    (htriple : ∀ {i j k : Fin N}, i ≠ j → i ≠ k → j ≠ k →
      y i = y j ∨ y i = y k ∨ y j = y k) :
    HasAtMostTwoValues y := by
  let i₀ : Fin N := ⟨0, hN⟩
  by_cases hall : ∀ j, y j = y i₀
  · exact ⟨y i₀, y i₀, fun j ↦ Or.inl (hall j)⟩
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    refine ⟨y i₀, y j, fun k ↦ ?_⟩
    by_cases hk0 : y k = y i₀
    · exact Or.inl hk0
    right
    by_contra hkj
    have hi0j : i₀ ≠ j := by
      intro h
      subst j
      exact hj rfl
    have hi0k : i₀ ≠ k := by
      intro h
      subst k
      exact hk0 rfl
    have hjk : j ≠ k := by
      intro h
      subst k
      exact hkj rfl
    rcases htriple hi0j hi0k hjk with h | h | h
    · exact hj h.symm
    · exact hk0 h.symm
    · exact hkj h.symm

/-- Proposition 2 (two-level extremizer), in an exact nonempty-section form:
the slice MGF has a global maximizer with at most two coordinate values on
every nonempty centered fixed-radius sphere. -/
theorem exists_twoLevel_sliceMgf_maximizer {N K : ℕ} (hN : 2 ≤ N)
    (hK0 : 1 ≤ K) (hKN : K ≤ N - 1) {rSq : ℝ} (hr : 0 ≤ rSq)
    {y : Fin N → ℝ} (hy : y ∈ centeredSphere N rSq) :
    ∃ z ∈ centeredSphere N rSq,
      (∀ x ∈ centeredSphere N rSq, sliceMgf N K x ≤ sliceMgf N K z) ∧
      HasAtMostTwoValues z := by
  obtain ⟨z, hz, hmax⟩ := exists_sliceMgf_maximizer hr hy
  refine ⟨z, hz, hmax, ?_⟩
  apply hasAtMostTwoValues_of_triple_duplicate (by omega)
  intro i j k hij hik hjk
  apply sliceMgf_globalMax_triple_duplicate hK0 hKN
    (y := z) (i := i) (j := j) (k := k) (hij := hij) (hik := hik) (hjk := hjk)
  intro x hsum hsq
  apply hmax x
  constructor
  · rw [hsum, hz.1]
  · exact hsq.trans hz.2

end SharpSerfling.FinitePopulation
