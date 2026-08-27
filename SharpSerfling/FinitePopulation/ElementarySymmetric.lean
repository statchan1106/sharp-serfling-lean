import SharpSerfling.FinitePopulation.TwoLevel
import SharpSerfling.Analysis.ThreePoint
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

namespace SharpSerfling.FinitePopulation

open scoped BigOperators
open SharpSerfling.Hypergeometric

/-- Summing over the subtype of fixed-cardinality samples is the same as
summing over the corresponding finite powerset. -/
theorem sum_sample_eq_powersetCard {N K : ℕ} (F : Finset (Fin N) → ℝ) :
    (∑ s : Sample N K, F s.1) =
      ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard K, F s := by
  symm
  apply Finset.sum_subtype
  intro s
  simp [Set.powersetCard]

/-- The numerator of the slice MGF is an elementary symmetric function of
the exponentiated coordinates. -/
theorem sum_sample_exp_eq_esymm {N K : ℕ} (y : Fin N → ℝ) :
    (∑ s : Sample N K, Real.exp (∑ i ∈ s.1, y i)) =
      ((Finset.univ : Finset (Fin N)).val.map (fun i ↦ Real.exp (y i))).esymm K := by
  calc
    _ = ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard K,
        Real.exp (∑ i ∈ s, y i) :=
      sum_sample_eq_powersetCard _
    _ = ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard K,
        ∏ i ∈ s, Real.exp (y i) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [← Real.exp_sum]
    _ = _ := (Finset.esymm_map_val (fun i ↦ Real.exp (y i)) Finset.univ K).symm

/-- Pascal recurrence for elementary symmetric functions of a multiset. -/
theorem Multiset.esymm_cons_succ (a : ℝ) (s : Multiset ℝ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add]
  congr 1
  simp only [Multiset.map_map, Function.comp_apply, Multiset.prod_cons]
  exact Multiset.sum_map_mul_left

/-- Elementary-symmetric expansion after adjoining three variables. -/
theorem Multiset.esymm_three_cons (a b c : ℝ) (s : Multiset ℝ) (n : ℕ) :
    (a ::ₘ b ::ₘ c ::ₘ s).esymm (n + 3) =
      s.esymm (n + 3) + (a + b + c) * s.esymm (n + 2) +
        (a * b + a * c + b * c) * s.esymm (n + 1) +
        (a * b * c) * s.esymm n := by
  rw [show n + 3 = (n + 2) + 1 by omega,
    Multiset.esymm_cons_succ]
  rw [show n + 2 = (n + 1) + 1 by omega,
    Multiset.esymm_cons_succ]
  rw [show n + 1 = n + 1 by rfl, Multiset.esymm_cons_succ]
  rw [show n + 2 = (n + 1) + 1 by omega,
    Multiset.esymm_cons_succ]
  rw [show n + 1 = n + 1 by rfl, Multiset.esymm_cons_succ]
  rw [show n + 1 = n + 1 by rfl, Multiset.esymm_cons_succ]
  rw [Multiset.esymm_cons_succ c s n]
  ring

theorem Multiset.esymm_three_cons_one (a b c : ℝ) (s : Multiset ℝ) :
    (a ::ₘ b ::ₘ c ::ₘ s).esymm 1 = s.esymm 1 + (a + b + c) := by
  rw [show 1 = 0 + 1 by omega, Multiset.esymm_cons_succ,
    Multiset.esymm_cons_succ, Multiset.esymm_cons_succ]
  simp [Multiset.esymm]
  ring

theorem Multiset.esymm_three_cons_two (a b c : ℝ) (s : Multiset ℝ) :
    (a ::ₘ b ::ₘ c ::ₘ s).esymm 2 =
      s.esymm 2 + (a + b + c) * s.esymm 1 + (a * b + a * c + b * c) := by
  rw [show 2 = 1 + 1 by omega, Multiset.esymm_cons_succ,
    Multiset.esymm_cons_succ, Multiset.esymm_cons_succ]
  rw [show 1 = 0 + 1 by omega, Multiset.esymm_cons_succ,
    Multiset.esymm_cons_succ]
  rw [Multiset.esymm_cons_succ c s 0]
  simp [Multiset.esymm]
  ring

/-- Coordinates left after deleting three pairwise-distinct indices. -/
def remainingIndices {N : ℕ} (i j k : Fin N) : Finset (Fin N) :=
  (((Finset.univ : Finset (Fin N)).erase i).erase j).erase k

theorem univ_eq_insert_three_remaining {N : ℕ} {i j k : Fin N}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (Finset.univ : Finset (Fin N)) =
      insert i (insert j (insert k (remainingIndices i j k))) := by
  ext x
  simp [remainingIndices]
  tauto

theorem exp_multiset_eq_three_cons_remaining {N : ℕ} (y : Fin N → ℝ)
    {i j k : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (Finset.univ : Finset (Fin N)).val.map (fun l ↦ Real.exp (y l)) =
      Real.exp (y i) ::ₘ Real.exp (y j) ::ₘ Real.exp (y k) ::ₘ
        (remainingIndices i j k).val.map (fun l ↦ Real.exp (y l)) := by
  rw [univ_eq_insert_three_remaining hij hik hjk]
  have hkR : k ∉ (remainingIndices i j k).val := by
    change k ∉ remainingIndices i j k
    simp [remainingIndices]
  have hjR : j ∉ (remainingIndices i j k).val := by
    change j ∉ remainingIndices i j k
    simp [remainingIndices]
  have hiR : i ∉ (remainingIndices i j k).val := by
    change i ∉ remainingIndices i j k
    simp [remainingIndices]
  have hjKR : j ∉ k ::ₘ (remainingIndices i j k).val := by
    simp [hjk, hjR]
  have hiJKR : i ∉ j ::ₘ k ::ₘ (remainingIndices i j k).val := by
    simp [hij, hik, hiR]
  change Multiset.map (fun l ↦ Real.exp (y l))
      (Multiset.ndinsert i (Multiset.ndinsert j
        (Multiset.ndinsert k (remainingIndices i j k).val))) = _
  rw [Multiset.ndinsert_of_notMem hkR, Multiset.ndinsert_of_notMem hjKR,
    Multiset.ndinsert_of_notMem hiJKR]
  simp

theorem Multiset.esymm_nonneg {s : Multiset ℝ} {n : ℕ}
    (hs : ∀ x ∈ s, 0 ≤ x) : 0 ≤ s.esymm n := by
  unfold Multiset.esymm
  apply Multiset.sum_nonneg
  intro p hp
  simp only [Multiset.mem_map] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  apply Multiset.prod_nonneg
  intro x hx
  exact hs x (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hx)

theorem Multiset.esymm_pos {s : Multiset ℝ} {n : ℕ}
    (hs : ∀ x ∈ s, 0 < x) (hn : n ≤ s.card) : 0 < s.esymm n := by
  have hcard : 0 < (s.powersetCard n).card := by
    rw [Multiset.card_powersetCard]
    exact Nat.choose_pos hn
  have hne : s.powersetCard n ≠ 0 := Multiset.card_pos.mp hcard
  obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero hne
  have htpos : 0 < t.prod := by
    apply Multiset.prod_pos
    intro x hx
    exact hs x (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hx)
  have hall : ∀ p ∈ (s.powersetCard n).map Multiset.prod, 0 ≤ p := by
    intro p hp
    simp only [Multiset.mem_map] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    exact (Multiset.prod_pos (fun x hx ↦
      hs x (Multiset.mem_of_le (Multiset.mem_powersetCard.mp hu).1 hx))).le
  have htmem : t.prod ∈ (s.powersetCard n).map Multiset.prod := by
    exact Multiset.mem_map.mpr ⟨t, ht, rfl⟩
  exact lt_of_lt_of_le htpos (Multiset.single_le_sum hall _ htmem)

theorem card_remainingIndices {N : ℕ} {i j k : Fin N}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (remainingIndices i j k).card = N - 3 := by
  unfold remainingIndices
  have hi : i ∈ (Finset.univ : Finset (Fin N)) := by simp
  have hj : j ∈ (Finset.univ : Finset (Fin N)).erase i := by simp [hij.symm]
  have hk : k ∈ ((Finset.univ : Finset (Fin N)).erase i).erase j := by
    simp [hik.symm, hjk.symm]
  rw [Finset.card_erase_of_mem hk, Finset.card_erase_of_mem hj,
    Finset.card_erase_of_mem hi]
  simp
  omega

/-- Replace three selected coordinates and leave every other coordinate fixed. -/
def replaceThree {N : ℕ} (y : Fin N → ℝ) (i j k : Fin N)
    (u v z : ℝ) (l : Fin N) : ℝ :=
  if l = i then u else if l = j then v else if l = k then z else y l

theorem replaceThree_apply_first {N : ℕ} (y : Fin N → ℝ) {i j k : Fin N}
    (u v z : ℝ) : replaceThree y i j k u v z i = u := by
  simp [replaceThree]

theorem replaceThree_apply_second {N : ℕ} (y : Fin N → ℝ) {i j k : Fin N}
    (hij : i ≠ j) (u v z : ℝ) : replaceThree y i j k u v z j = v := by
  simp [replaceThree, hij.symm]

theorem replaceThree_apply_third {N : ℕ} (y : Fin N → ℝ) {i j k : Fin N}
    (hik : i ≠ k) (hjk : j ≠ k) (u v z : ℝ) :
    replaceThree y i j k u v z k = z := by
  simp [replaceThree, hik.symm, hjk.symm]

theorem replaceThree_apply_remaining {N : ℕ} (y : Fin N → ℝ) {i j k l : Fin N}
    (hl : l ∈ remainingIndices i j k) (u v z : ℝ) :
    replaceThree y i j k u v z l = y l := by
  have hli : l ≠ i := by
    intro h
    subst l
    simpa [remainingIndices] using hl
  have hlj : l ≠ j := by
    intro h
    subst l
    simpa [remainingIndices] using hl
  have hlk : l ≠ k := by
    intro h
    subst l
    simpa [remainingIndices] using hl
  simp [replaceThree, hli, hlj, hlk]

theorem replaceThree_self {N : ℕ} (y : Fin N → ℝ) {i j k : Fin N}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    replaceThree y i j k (y i) (y j) (y k) = y := by
  funext l
  by_cases hli : l = i
  · subst l
    simp [replaceThree]
  by_cases hlj : l = j
  · subst l
    simp [replaceThree, hij.symm]
  by_cases hlk : l = k
  · subst l
    simp [replaceThree, hik.symm, hjk.symm]
  simp [replaceThree, hli, hlj, hlk]

theorem sum_replaceThree {N : ℕ} (y : Fin N → ℝ) {i j k : Fin N}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v z : ℝ) :
    ∑ l, replaceThree y i j k u v z l =
      u + v + z + ∑ l ∈ remainingIndices i j k, y l := by
  have hrem : (∑ l ∈ remainingIndices i j k, replaceThree y i j k u v z l) =
      ∑ l ∈ remainingIndices i j k, y l := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [replaceThree_apply_remaining y hl]
  change ∑ l ∈ (Finset.univ : Finset (Fin N)), replaceThree y i j k u v z l = _
  rw [univ_eq_insert_three_remaining hij hik hjk]
  simp [replaceThree_apply_first, replaceThree_apply_second, replaceThree_apply_third,
    remainingIndices, hij, hik, hjk]
  change (∑ l ∈ (((Finset.univ : Finset (Fin N)).erase i).erase j).erase k,
      replaceThree y i j k u v z l) =
    ∑ l ∈ (((Finset.univ : Finset (Fin N)).erase i).erase j).erase k, y l at hrem
  rw [hrem]
  ring

theorem sum_sq_replaceThree {N : ℕ} (y : Fin N → ℝ) {i j k : Fin N}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v z : ℝ) :
    ∑ l, (replaceThree y i j k u v z l) ^ 2 =
      u ^ 2 + v ^ 2 + z ^ 2 + ∑ l ∈ remainingIndices i j k, (y l) ^ 2 := by
  have hrem : (∑ l ∈ remainingIndices i j k,
      (replaceThree y i j k u v z l) ^ 2) =
      ∑ l ∈ remainingIndices i j k, (y l) ^ 2 := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [replaceThree_apply_remaining y hl]
  change ∑ l ∈ (Finset.univ : Finset (Fin N)),
      (replaceThree y i j k u v z l) ^ 2 = _
  rw [univ_eq_insert_three_remaining hij hik hjk]
  simp [replaceThree_apply_first, replaceThree_apply_second, replaceThree_apply_third,
    remainingIndices, hij, hik, hjk]
  change (∑ l ∈ (((Finset.univ : Finset (Fin N)).erase i).erase j).erase k,
      (replaceThree y i j k u v z l) ^ 2) =
    ∑ l ∈ (((Finset.univ : Finset (Fin N)).erase i).erase j).erase k,
      (y l) ^ 2 at hrem
  rw [hrem]
  ring

theorem exp_multiset_replaceThree {N : ℕ} (y : Fin N → ℝ) {i j k : Fin N}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v z : ℝ) :
    (Finset.univ : Finset (Fin N)).val.map
        (fun l ↦ Real.exp (replaceThree y i j k u v z l)) =
      Real.exp u ::ₘ Real.exp v ::ₘ Real.exp z ::ₘ
        (remainingIndices i j k).val.map (fun l ↦ Real.exp (y l)) := by
  rw [exp_multiset_eq_three_cons_remaining
    (replaceThree y i j k u v z) hij hik hjk]
  rw [replaceThree_apply_first, replaceThree_apply_second y hij,
    replaceThree_apply_third y hik hjk]
  congr 3
  apply Multiset.map_congr rfl
  intro l hl
  rw [replaceThree_apply_remaining y (by exact hl)]

/-- Unnormalized elementary-symmetric numerator of the slice MGF. -/
noncomputable def sliceNumerator (N K : ℕ) (y : Fin N → ℝ) : ℝ :=
  ∑ s : Sample N K, Real.exp (∑ l ∈ s.1, y l)

theorem sliceMgf_eq_sliceNumerator_div (N K : ℕ) (y : Fin N → ℝ) :
    sliceMgf N K y = sliceNumerator N K y / Fintype.card (Sample N K) := by
  rfl

theorem sliceNumerator_replaceThree_one {N : ℕ} (y : Fin N → ℝ)
    {i j k : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u v z : ℝ) :
    sliceNumerator N 1 (replaceThree y i j k u v z) =
      ((remainingIndices i j k).val.map (fun l ↦ Real.exp (y l))).esymm 1 +
        (Real.exp u + Real.exp v + Real.exp z) := by
  unfold sliceNumerator
  rw [sum_sample_exp_eq_esymm, exp_multiset_replaceThree y hij hik hjk]
  exact Multiset.esymm_three_cons_one _ _ _ _

theorem sliceNumerator_replaceThree_two {N : ℕ} (y : Fin N → ℝ)
    {i j k : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u v z : ℝ) :
    sliceNumerator N 2 (replaceThree y i j k u v z) =
      ((remainingIndices i j k).val.map (fun l ↦ Real.exp (y l))).esymm 2 +
        (Real.exp u + Real.exp v + Real.exp z) *
          ((remainingIndices i j k).val.map (fun l ↦ Real.exp (y l))).esymm 1 +
        (Real.exp (u + v) + Real.exp (u + z) + Real.exp (v + z)) := by
  unfold sliceNumerator
  rw [sum_sample_exp_eq_esymm, exp_multiset_replaceThree y hij hik hjk]
  rw [Multiset.esymm_three_cons_two]
  rw [Real.exp_add, Real.exp_add, Real.exp_add]

theorem sliceNumerator_replaceThree_of_three_le {N K : ℕ} (hK3 : 3 ≤ K)
    (y : Fin N → ℝ) {i j k : Fin N}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v z : ℝ) :
    sliceNumerator N K (replaceThree y i j k u v z) =
      ((remainingIndices i j k).val.map (fun l ↦ Real.exp (y l))).esymm K +
        (Real.exp u + Real.exp v + Real.exp z) *
          ((remainingIndices i j k).val.map (fun l ↦ Real.exp (y l))).esymm (K - 1) +
        (Real.exp (u + v) + Real.exp (u + z) + Real.exp (v + z)) *
          ((remainingIndices i j k).val.map (fun l ↦ Real.exp (y l))).esymm (K - 2) +
        Real.exp (u + v + z) *
          ((remainingIndices i j k).val.map (fun l ↦ Real.exp (y l))).esymm (K - 3) := by
  unfold sliceNumerator
  rw [sum_sample_exp_eq_esymm, exp_multiset_replaceThree y hij hik hjk]
  have hthree := Multiset.esymm_three_cons (Real.exp u) (Real.exp v) (Real.exp z)
    ((remainingIndices i j k).val.map (fun l ↦ Real.exp (y l))) (K - 3)
  rw [show K - 3 + 3 = K by omega,
    show K - 3 + 2 = K - 1 by omega,
    show K - 3 + 1 = K - 2 by omega] at hthree
  rw [Real.exp_add, Real.exp_add, Real.exp_add]
  rw [show Real.exp (u + v + z) = Real.exp u * Real.exp v * Real.exp z by
    rw [Real.exp_add, Real.exp_add]]
  linear_combination hthree

theorem exp_pair_sum_eq_of_sum {u v z s : ℝ} (hs : u + v + z = s) :
    Real.exp (u + v) + Real.exp (u + z) + Real.exp (v + z) =
      Real.exp s * (Real.exp (-u) + Real.exp (-v) + Real.exp (-z)) := by
  have huv : Real.exp (u + v) = Real.exp s * Real.exp (-z) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  have huz : Real.exp (u + z) = Real.exp s * Real.exp (-v) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  have hvz : Real.exp (v + z) = Real.exp s * Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  rw [huv, huz, hvz]
  ring

end SharpSerfling.FinitePopulation
