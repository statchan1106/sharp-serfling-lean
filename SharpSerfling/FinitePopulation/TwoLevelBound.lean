import SharpSerfling.FinitePopulation.TwoLevelReduction

namespace SharpSerfling.FinitePopulation

open scoped BigOperators
open SharpSerfling.Hypergeometric

theorem sqNorm_nonneg {N : ℕ} (y : Fin N → ℝ) : 0 ≤ sqNorm y := by
  unfold sqNorm
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (y i)

theorem sliceMgf_pos {N K : ℕ} (hK : K ≤ N) (y : Fin N → ℝ) :
    0 < sliceMgf N K y := by
  letI : Nonempty (Sample N K) := sample_nonempty hK
  unfold sliceMgf
  exact SharpSerfling.finiteAverage_pos _ fun _ ↦ Real.exp_pos _

theorem sliceMgf_eq_of_exp_multiset_eq {N K : ℕ} {x y : Fin N → ℝ}
    (h : (Finset.univ : Finset (Fin N)).val.map (fun i ↦ Real.exp (x i)) =
      (Finset.univ : Finset (Fin N)).val.map (fun i ↦ Real.exp (y i))) :
    sliceMgf N K x = sliceMgf N K y := by
  rw [sliceMgf_eq_sliceNumerator_div, sliceMgf_eq_sliceNumerator_div]
  congr 1
  unfold sliceNumerator
  rw [sum_sample_exp_eq_esymm, sum_sample_exp_eq_esymm, h]

/-- Multiset classification of a finite vector taking at most two values. -/
theorem multiset_eq_replicates_of_two_values {N : ℕ} {y : Fin N → ℝ} {a b : ℝ}
    (hy : ∀ i, y i = a ∨ y i = b) :
    let m := ((Finset.univ : Finset (Fin N)).val.filter (fun i ↦ y i = a)).card
    (Finset.univ : Finset (Fin N)).val.map y =
      Multiset.replicate m a + Multiset.replicate (N - m) b := by
  let S : Multiset (Fin N) := (Finset.univ : Finset (Fin N)).val
  let Sa := S.filter (fun i ↦ y i = a)
  let Sb := S.filter (fun i ↦ ¬y i = a)
  let m := Sa.card
  have hpart : Sa + Sb = S := Multiset.filter_add_not _ _
  have hmapa : Sa.map y = Multiset.replicate m a := by
    calc
      Sa.map y = Sa.map (fun _ ↦ a) := by
        apply Multiset.map_congr rfl
        intro i hi
        exact Multiset.mem_filter.mp hi |>.2
      _ = _ := Multiset.map_const' _ _
  have hmapb : Sb.map y = Multiset.replicate Sb.card b := by
    calc
      Sb.map y = Sb.map (fun _ ↦ b) := by
        apply Multiset.map_congr rfl
        intro i hi
        have hne : ¬y i = a := Multiset.mem_filter.mp hi |>.2
        exact (hy i).resolve_left hne
      _ = _ := Multiset.map_const' _ _
  have hcardS : S.card = N := by simp [S]
  have hcard : Sb.card = N - m := by
    have := congrArg Multiset.card hpart
    simp only [Multiset.card_add] at this
    dsimp [m]
    omega
  dsimp
  change S.map y = Multiset.replicate m a + Multiset.replicate (N - m) b
  rw [← hpart, Multiset.map_add, hmapa, hmapb, hcard]

/-- Exact sum formula for a vector taking two values. -/
theorem sum_eq_of_two_values {N : ℕ} {y : Fin N → ℝ} {a b : ℝ}
    (hy : ∀ i, y i = a ∨ y i = b) :
    let m := ((Finset.univ : Finset (Fin N)).val.filter (fun i ↦ y i = a)).card
    (∑ i, y i) = (m : ℝ) * a + ((N - m : ℕ) : ℝ) * b := by
  let m := ((Finset.univ : Finset (Fin N)).val.filter (fun i ↦ y i = a)).card
  have hm := multiset_eq_replicates_of_two_values hy
  dsimp at hm
  change ((Finset.univ : Finset (Fin N)).val.map y).sum = _
  rw [hm]
  simp

theorem two_values_centered_formula {N : ℕ} (hN : 0 < N)
    {y : Fin N → ℝ} {a b : ℝ} (hy : ∀ i, y i = a ∨ y i = b)
    (hcenter : ∑ i, y i = 0) :
    let m := ((Finset.univ : Finset (Fin N)).val.filter (fun i ↦ y i = a)).card
    a = (((N : ℝ) - (m : ℝ)) / (N : ℝ)) * (a - b) ∧
      b = (-(m : ℝ) / (N : ℝ)) * (a - b) := by
  let m := ((Finset.univ : Finset (Fin N)).val.filter (fun i ↦ y i = a)).card
  have hmle : m ≤ N := by
    dsimp [m]
    calc
      _ ≤ (Finset.univ : Finset (Fin N)).val.card :=
        Multiset.card_le_card (Multiset.filter_le _ _)
      _ = N := by simp
  have hsum := sum_eq_of_two_values hy
  dsimp at hsum
  rw [hcenter] at hsum
  rw [Nat.cast_sub hmle] at hsum
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  constructor <;> field_simp [hNR] <;> linarith

theorem multiset_canonicalTwoLevel {N m : ℕ} (hm : m ≤ N) (d : ℝ) :
    (Finset.univ : Finset (Fin N)).val.map (canonicalTwoLevel N m d) =
      Multiset.replicate m ((((N : ℝ) - (m : ℝ)) / (N : ℝ)) * d) +
        Multiset.replicate (N - m) ((-(m : ℝ) / (N : ℝ)) * d) := by
  let S : Multiset (Fin N) := (Finset.univ : Finset (Fin N)).val
  let Sa := S.filter (fun i ↦ i ∈ marked N m)
  let Sb := S.filter (fun i ↦ i ∉ marked N m)
  have hpart : Sa + Sb = S := Multiset.filter_add_not _ _
  have hSa : Sa = (marked N m).val := by
    change Multiset.filter (fun i ↦ i ∈ marked N m)
        (Finset.univ : Finset (Fin N)).val = (marked N m).val
    rw [← Finset.filter_val]
    congr 1
    ext i
    simp
  have hmapa : Sa.map (canonicalTwoLevel N m d) =
      Multiset.replicate m ((((N : ℝ) - (m : ℝ)) / (N : ℝ)) * d) := by
    calc
      _ = Sa.map (fun _ ↦ (((N : ℝ) - (m : ℝ)) / (N : ℝ)) * d) := by
        apply Multiset.map_congr rfl
        intro i hi
        have him : i ∈ marked N m := Multiset.mem_filter.mp hi |>.2
        simp [canonicalTwoLevel, him]
      _ = Multiset.replicate Sa.card _ := Multiset.map_const' _ _
      _ = _ := by
        rw [hSa]
        change Multiset.replicate (marked N m).card _ = _
        rw [card_marked hm]
  have hcardSb : Sb.card = N - m := by
    have hc := congrArg Multiset.card hpart
    simp only [Multiset.card_add] at hc
    have hcardS : S.card = N := by simp [S]
    have hcardSa : Sa.card = m := by
      rw [hSa]
      change (marked N m).card = m
      exact card_marked hm
    omega
  have hmapb : Sb.map (canonicalTwoLevel N m d) =
      Multiset.replicate (N - m) ((-(m : ℝ) / (N : ℝ)) * d) := by
    calc
      _ = Sb.map (fun _ ↦ (-(m : ℝ) / (N : ℝ)) * d) := by
        apply Multiset.map_congr rfl
        intro i hi
        have him : i ∉ marked N m := Multiset.mem_filter.mp hi |>.2
        simp [canonicalTwoLevel, him]
      _ = Multiset.replicate Sb.card _ := Multiset.map_const' _ _
      _ = _ := by rw [hcardSb]
  change S.map (canonicalTwoLevel N m d) = _
  rw [← hpart, Multiset.map_add, hmapa, hmapb]

theorem sqNorm_eq_of_multiset_eq {N : ℕ} {x y : Fin N → ℝ}
    (h : (Finset.univ : Finset (Fin N)).val.map x =
      (Finset.univ : Finset (Fin N)).val.map y) :
    sqNorm x = sqNorm y := by
  have hh := congrArg (Multiset.map fun u : ℝ ↦ u ^ 2) h
  have hs := congrArg Multiset.sum hh
  simpa only [sqNorm, Finset.sum_eq_multiset_sum, Multiset.map_map,
    Function.comp_apply] using hs

theorem sliceMgf_zero_vector {N K : ℕ} (hK : K ≤ N) :
    sliceMgf N K (fun _ ↦ 0) = 1 := by
  letI : Nonempty (Sample N K) := sample_nonempty hK
  unfold sliceMgf
  simp [SharpSerfling.finiteAverage_one]

/-- The sharp norm-scaled bound for every centered vector taking at most two
coordinate values. -/
theorem sliceLogMgf_two_values_le {N K : ℕ} (hN : 2 ≤ N) (hK : K ≤ N)
    {y : Fin N → ℝ} (hcenter : ∑ i, y i = 0) (htwo : HasAtMostTwoValues y) :
    sliceLogMgf N K y ≤
      SharpSerfling.kappa N * (N : ℝ) / (8 * ((N : ℝ) - 1)) * sqNorm y := by
  obtain ⟨a, b, hy⟩ := htwo
  let m := ((Finset.univ : Finset (Fin N)).val.filter (fun i ↦ y i = a)).card
  let d := a - b
  have hmle : m ≤ N := by
    dsimp [m]
    calc
      _ ≤ (Finset.univ : Finset (Fin N)).val.card :=
        Multiset.card_le_card (Multiset.filter_le _ _)
      _ = N := by simp
  have hform := two_values_centered_formula (by omega) hy hcenter
  change a = (((N : ℝ) - (m : ℝ)) / (N : ℝ)) * (a - b) ∧
    b = (-(m : ℝ) / (N : ℝ)) * (a - b) at hform
  have hymulti := multiset_eq_replicates_of_two_values hy
  change (Finset.univ : Finset (Fin N)).val.map y =
    Multiset.replicate m a + Multiset.replicate (N - m) b at hymulti
  have hcmulti := multiset_canonicalTwoLevel hmle d
  have hmulti : (Finset.univ : Finset (Fin N)).val.map y =
      (Finset.univ : Finset (Fin N)).val.map (canonicalTwoLevel N m d) := by
    rw [hymulti, hcmulti, ← hform.1, ← hform.2]
  have hexpmulti : (Finset.univ : Finset (Fin N)).val.map
      (fun i ↦ Real.exp (y i)) =
      (Finset.univ : Finset (Fin N)).val.map
        (fun i ↦ Real.exp (canonicalTwoLevel N m d i)) := by
    have := congrArg (Multiset.map Real.exp) hmulti
    simpa only [Multiset.map_map, Function.comp_apply] using this
  have hmgf : sliceMgf N K y = sliceMgf N K (canonicalTwoLevel N m d) :=
    sliceMgf_eq_of_exp_multiset_eq hexpmulti
  have hnorm : sqNorm y = sqNorm (canonicalTwoLevel N m d) :=
    sqNorm_eq_of_multiset_eq hmulti
  by_cases hm0 : m = 0
  · have hb0 : b = 0 := by
      rw [hm0] at hform
      norm_num at hform
      exact hform.2
    have hy0 : y = fun _ ↦ 0 := by
      funext i
      rcases hy i with hai | hbi
      · have him : i ∈ (Finset.univ : Finset (Fin N)).val.filter (fun j ↦ y j = a) := by
          simp [hai]
        have hcardpos : 0 < m := by
          dsimp [m]
          exact Multiset.card_pos.mpr (fun hz ↦ by simpa [hz] using him)
        omega
      · rw [hbi, hb0]
    rw [hy0, sliceLogMgf, sliceMgf_zero_vector hK]
    simp [sqNorm]
  by_cases hmN : m = N
  · have ha0 : a = 0 := by
      rw [hmN] at hform
      norm_num at hform
      simpa using hform.1
    have hy0 : y = fun _ ↦ 0 := by
      funext i
      have him : i ∈ (Finset.univ : Finset (Fin N)).val.filter (fun j ↦ y j = a) := by
        have heq :
            (Finset.univ : Finset (Fin N)).val.filter (fun j ↦ y j = a) =
              (Finset.univ : Finset (Fin N)).val := by
          apply Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _)
          simpa [m] using hmN.ge
        rw [heq]
        simp
      have := Multiset.mem_filter.mp him |>.2
      rw [this, ha0]
    rw [hy0, sliceLogMgf, sliceMgf_zero_vector hK]
    simp [sqNorm]
  have hm1 : 1 ≤ m := by omega
  have hmNm1 : m ≤ N - 1 := by omega
  rw [sliceLogMgf, hmgf, hnorm]
  exact sliceLogMgf_canonicalTwoLevel_le hN hK hm1 hmNm1 d

/-- The sharp norm-scaled slice bound for an arbitrary centered vector on a
nontrivial Hamming slice.  Proposition 2 supplies a two-level global
maximizer; `sliceLogMgf_two_values_le` controls that maximizer. -/
theorem sliceLogMgf_le_of_nontrivial {N K : ℕ} (hN : 2 ≤ N)
    (hK0 : 1 ≤ K) (hKN : K ≤ N - 1) {y : Fin N → ℝ}
    (hcenter : ∑ i, y i = 0) :
    sliceLogMgf N K y ≤
      SharpSerfling.kappa N * (N : ℝ) / (8 * ((N : ℝ) - 1)) * sqNorm y := by
  have hK : K ≤ N := by omega
  obtain ⟨z, hz, hmax, htwo⟩ :=
    exists_twoLevel_sliceMgf_maximizer hN hK0 hKN (sqNorm_nonneg y)
      (y := y) ⟨hcenter, rfl⟩
  have hmgf : sliceMgf N K y ≤ sliceMgf N K z :=
    hmax y ⟨hcenter, rfl⟩
  have hlog : sliceLogMgf N K y ≤ sliceLogMgf N K z := by
    unfold sliceLogMgf
    exact Real.log_le_log (sliceMgf_pos hK y) hmgf
  calc
    sliceLogMgf N K y ≤ sliceLogMgf N K z := hlog
    _ ≤ SharpSerfling.kappa N * (N : ℝ) / (8 * ((N : ℝ) - 1)) * sqNorm z :=
      sliceLogMgf_two_values_le hN hK hz.1 htwo
    _ = SharpSerfling.kappa N * (N : ℝ) / (8 * ((N : ℝ) - 1)) * sqNorm y := by
      rw [hz.2]

theorem sliceMgf_zero_sample (N : ℕ) (y : Fin N → ℝ) :
    sliceMgf N 0 y = 1 := by
  letI : Nonempty (Sample N 0) := sample_nonempty (Nat.zero_le N)
  unfold sliceMgf
  rw [show (fun s : Sample N 0 ↦ Real.exp (∑ i ∈ s.1, y i)) =
      fun _ ↦ 1 by
    funext s
    have hs : s.1 = ∅ := Finset.card_eq_zero.mp s.property
    simp [hs]]
  exact SharpSerfling.finiteAverage_one

theorem sliceMgf_full_sample {N : ℕ} (y : Fin N → ℝ)
    (hcenter : ∑ i, y i = 0) : sliceMgf N N y = 1 := by
  letI : Nonempty (Sample N N) := sample_nonempty le_rfl
  unfold sliceMgf
  rw [show (fun s : Sample N N ↦ Real.exp (∑ i ∈ s.1, y i)) =
      fun _ ↦ 1 by
    funext s
    have hs : s.1 = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using s.property
    simp [hs, hcenter]]
  exact SharpSerfling.finiteAverage_one

/-- The sharp slice inequality, including the empty and full slices. -/
theorem sliceLogMgf_le {N K : ℕ} (hN : 2 ≤ N) (hK : K ≤ N)
    {y : Fin N → ℝ} (hcenter : ∑ i, y i = 0) :
    sliceLogMgf N K y ≤
      SharpSerfling.kappa N * (N : ℝ) / (8 * ((N : ℝ) - 1)) * sqNorm y := by
  have hcoef : 0 ≤
      SharpSerfling.kappa N * (N : ℝ) / (8 * ((N : ℝ) - 1)) := by
    have hk := (SharpSerfling.kappa_pos hN).le
    have hNR : (0 : ℝ) ≤ N := by positivity
    have hden : (0 : ℝ) < 8 * ((N : ℝ) - 1) := by
      have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
      positivity
    exact div_nonneg (mul_nonneg hk hNR) hden.le
  by_cases hK0 : K = 0
  · subst K
    rw [sliceLogMgf, sliceMgf_zero_sample]
    simpa using mul_nonneg hcoef (sqNorm_nonneg y)
  have hKpos : 1 ≤ K := by omega
  by_cases hKN : K = N
  · subst K
    rw [sliceLogMgf, sliceMgf_full_sample y hcenter]
    simpa using mul_nonneg hcoef (sqNorm_nonneg y)
  exact sliceLogMgf_le_of_nontrivial hN hKpos (by omega) hcenter

end SharpSerfling.FinitePopulation
