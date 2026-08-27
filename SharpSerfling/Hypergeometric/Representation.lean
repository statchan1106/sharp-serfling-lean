import SharpSerfling.Hypergeometric.Recursion
import Mathlib.Data.Fintype.Prod

namespace SharpSerfling.Hypergeometric

open scoped BigOperators
open Finset Finset.Nat

/-- Count successes and failures in a size-`m` sample. -/
def sampleIndex {N m : ℕ} (K : ℕ) (s : Sample N m) : ℕ × ℕ :=
  (count K s, m - count K s)

theorem sampleIndex_mem_antidiagonal {N K m : ℕ} (s : Sample N m) :
    sampleIndex K s ∈ antidiagonal m := by
  rw [Finset.mem_antidiagonal]
  simp [sampleIndex, Nat.add_sub_of_le (count_le_sample s)]

/-- Samples with a prescribed count split uniquely into their marked and unmarked parts. -/
noncomputable def countFiberEquiv {N K m : ℕ} (hK : K ≤ N) (ij : ℕ × ℕ)
    (hij : ij ∈ antidiagonal m) :
    {s : Sample N m // count K s = ij.1} ≃
      ↑((marked N K).powersetCard ij.1) ×
        ↑(((Finset.univ : Finset (Fin N)) \ marked N K).powersetCard ij.2) := by
  classical
  let A := marked N K
  let B := (Finset.univ : Finset (Fin N)) \ A
  have hijsum : ij.1 + ij.2 = m := Finset.mem_antidiagonal.mp hij
  let toFun : {s : Sample N m // count K s = ij.1} →
      ↑(A.powersetCard ij.1) × ↑(B.powersetCard ij.2) := fun s ↦
    (⟨s.1.1 ∩ A, by
        rw [Finset.mem_powersetCard]
        constructor
        · exact Finset.inter_subset_right
        · simpa [A, count] using s.property⟩,
      ⟨s.1.1 \ A, by
        rw [Finset.mem_powersetCard]
        constructor
        · intro x hx
          simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact (Finset.mem_sdiff.mp hx).2
        · rw [Finset.card_sdiff, Finset.inter_comm, s.1.property]
          have hc : (s.1.1 ∩ A).card = ij.1 := by simpa [A, count] using s.property
          rw [hc]
          omega⟩)
  let invFun : ↑(A.powersetCard ij.1) × ↑(B.powersetCard ij.2) →
      {s : Sample N m // count K s = ij.1} := fun p ↦ by
    have ha := Finset.mem_powersetCard.mp p.1.property
    have hb := Finset.mem_powersetCard.mp p.2.property
    have hd : Disjoint p.1.1 p.2.1 := by
      rw [Finset.disjoint_left]
      intro x hxa hxb
      have hxA : x ∈ A := ha.1 hxa
      have hxB : x ∈ B := hb.1 hxb
      exact (Finset.mem_sdiff.mp hxB).2 hxA
    have hcard : (p.1.1 ∪ p.2.1).card = m := by
      rw [Finset.card_union_of_disjoint hd, ha.2, hb.2, hijsum]
    refine ⟨⟨p.1.1 ∪ p.2.1, hcard⟩, ?_⟩
    change ((p.1.1 ∪ p.2.1) ∩ A).card = ij.1
    have hinter : (p.1.1 ∪ p.2.1) ∩ A = p.1.1 := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_inter.mp hx with ⟨hxab, hxA⟩
        rcases Finset.mem_union.mp hxab with hxa | hxb
        · exact hxa
        · exact False.elim ((Finset.mem_sdiff.mp (hb.1 hxb)).2 hxA)
      · intro hxa
        exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hxa, ha.1 hxa⟩
    rw [hinter, ha.2]
  refine ⟨toFun, invFun, ?_, ?_⟩
  · intro s
    apply Subtype.ext
    apply Subtype.ext
    change (s.1.1 ∩ A) ∪ (s.1.1 \ A) = s.1.1
    rw [Finset.union_comm, Finset.sdiff_union_inter]
  · intro p
    apply Prod.ext
    · apply Subtype.ext
      have ha := Finset.mem_powersetCard.mp p.1.property
      have hb := Finset.mem_powersetCard.mp p.2.property
      ext x
      constructor
      · intro hx
        rcases Finset.mem_inter.mp hx with ⟨hxab, hxA⟩
        rcases Finset.mem_union.mp hxab with hxa | hxb
        · exact hxa
        · exact False.elim ((Finset.mem_sdiff.mp (hb.1 hxb)).2 hxA)
      · intro hxa
        exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hxa, ha.1 hxa⟩
    · apply Subtype.ext
      have ha := Finset.mem_powersetCard.mp p.1.property
      have hb := Finset.mem_powersetCard.mp p.2.property
      ext x
      constructor
      · intro hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxab, hxA⟩
        rcases Finset.mem_union.mp hxab with hxa | hxb
        · exact False.elim (hxA (ha.1 hxa))
        · exact hxb
      · intro hxb
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hxb,
          (Finset.mem_sdiff.mp (hb.1 hxb)).2⟩

theorem card_countFiber {N K m : ℕ} (hK : K ≤ N) (ij : ℕ × ℕ)
    (hij : ij ∈ antidiagonal m) :
    Fintype.card {s : Sample N m // count K s = ij.1} = hypergeomWeight N K ij := by
  classical
  rw [Fintype.card_congr (countFiberEquiv hK ij hij), Fintype.card_prod]
  rw [Fintype.card_coe, Fintype.card_coe, Finset.card_powersetCard,
    Finset.card_powersetCard]
  simp [hypergeomWeight, Finset.card_sdiff, card_marked hK]

private theorem card_filter_count {N K m i : ℕ} :
    ((Finset.univ : Finset (Sample N m)).filter fun s ↦ count K s = i).card =
      Fintype.card {s : Sample N m // count K s = i} := by
  classical
  let e : ↑((Finset.univ : Finset (Sample N m)).filter fun s ↦ count K s = i) ≃
      {s : Sample N m // count K s = i} := {
    toFun := fun s ↦ ⟨s.1, (Finset.mem_filter.mp s.property).2⟩
    invFun := fun s ↦ ⟨s.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, s.property⟩⟩
    left_inv := fun s ↦ by rfl
    right_inv := fun s ↦ by rfl }
  rw [← Fintype.card_coe]
  exact Fintype.card_congr e

/-- Grouping the uniform subset sum by the number of marked elements yields the
usual binomial-coefficient sum. -/
theorem sum_count_eq_binomialSum {N K m : ℕ} (hK : K ≤ N) (f : ℕ → ℝ) :
    (∑ s : Sample N m, f (count K s)) = binomialSum N K m f := by
  classical
  have hgroup := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Sample N m))) (t := antidiagonal m)
    (g := sampleIndex K) (fun s _ ↦ sampleIndex_mem_antidiagonal s)
    (fun ij : ℕ × ℕ ↦ f ij.1)
  have hgroup' :
      (∑ j ∈ antidiagonal m,
        ∑ i ∈ (Finset.univ : Finset (Sample N m)) with sampleIndex K i = j, f j.1) =
        ∑ s : Sample N m, f (count K s) := by
    simpa [sampleIndex] using hgroup
  rw [binomialSum]
  rw [← hgroup']
  apply Finset.sum_congr rfl
  intro ij hij
  have hijsum : ij.1 + ij.2 = m := Finset.mem_antidiagonal.mp hij
  have hfilter :
      ((Finset.univ : Finset (Sample N m)).filter fun s ↦ sampleIndex K s = ij) =
        (Finset.univ : Finset (Sample N m)).filter fun s ↦ count K s = ij.1 := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hs
      exact congrArg Prod.fst hs
    · intro hs
      apply Prod.ext
      · exact hs
      · simp only [sampleIndex, hs]
        omega
  rw [hfilter, Finset.sum_const, nsmul_eq_mul, card_filter_count,
    card_countFiber hK ij hij]

/-- Uniform subset averages agree with their binomial-coefficient presentation. -/
theorem finiteAverage_count_eq_binomialAverage {N K m : ℕ} (hK : K ≤ N)
    (f : ℕ → ℝ) :
    SharpSerfling.finiteAverage (fun s : Sample N m ↦ f (count K s)) =
      binomialAverage N K m f := by
  unfold SharpSerfling.finiteAverage binomialAverage
  rw [sum_count_eq_binomialSum hK, card_sample]
  ring

/-- The original uniform-subset MGF is exactly the binomial-coefficient MGF. -/
theorem mgf_eq_binomialMgf {N K m : ℕ} (hK : K ≤ N) (t : ℝ) :
    mgf N K m t = binomialMgf N K m t := by
  unfold mgf binomialMgf
  exact finiteAverage_count_eq_binomialAverage (m := m) hK
    (fun i ↦ Real.exp (t * ((i : ℝ) - center N K m)))

/-- Manuscript dimension-reducing differential identity for the original
uniform-subset hypergeometric MGF. -/
theorem deriv_mgf_recursion {N K m : ℕ}
    (hN : 3 ≤ N) (hK0 : 0 < K) (hKN : K < N)
    (hm0 : 0 < m) (hmN : m < N) (t : ℝ) :
    deriv (mgf N K m) t =
      2 * variance N K m * Real.exp (recursionTilt N K m * t) *
        Real.sinh (t / 2) * mgf (N - 2) (K - 1) (m - 1) t := by
  have hKle : K ≤ N := Nat.le_of_lt hKN
  have hKred : K - 1 ≤ N - 2 := by omega
  calc
    deriv (mgf N K m) t = deriv (binomialMgf N K m) t := by
      rw [show mgf N K m = binomialMgf N K m by
        funext u
        exact mgf_eq_binomialMgf hKle u]
    _ = 2 * variance N K m * Real.exp (recursionTilt N K m * t) *
        Real.sinh (t / 2) * binomialMgf (N - 2) (K - 1) (m - 1) t :=
      deriv_binomialMgf_recursion hN hK0 hKN hm0 hmN t
    _ = _ := by rw [← mgf_eq_binomialMgf hKred]

end SharpSerfling.Hypergeometric
