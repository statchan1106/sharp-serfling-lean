import SharpSerfling.FinitePopulation.Definitions
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace SharpSerfling.FinitePopulation

open scoped BigOperators
open Set

/-- The weighted permutation statistic is a linear functional of the population. -/
noncomputable def statisticLinear {N n : ℕ} (hn : n ≤ N) (w : Fin n → ℝ)
    (π : Equiv.Perm (Fin N)) : (Fin N → ℝ) →ₗ[ℝ] ℝ where
  toFun X := statistic hn X w π
  map_add' X Y := by
    unfold statistic SharpSerfling.populationMean
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    conv_rhs => rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  map_smul' c X := by
    unfold statistic SharpSerfling.populationMean
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

@[simp] theorem statisticLinear_apply {N n : ℕ} (hn : n ≤ N) (w : Fin n → ℝ)
    (π : Equiv.Perm (Fin N)) (X : Fin N → ℝ) :
    statisticLinear hn w π X = statistic hn X w π := rfl

/-- For fixed coefficients and tilt, the permutation MGF is convex in the
entire population vector. -/
theorem convex_mgf_population {N n : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) (t : ℝ) :
    ConvexOn ℝ Set.univ (fun X : Fin N → ℝ ↦ mgf hn X w t) := by
  have hterm (π : Equiv.Perm (Fin N)) :
      ConvexOn ℝ Set.univ
        (fun X : Fin N → ℝ ↦ Real.exp (t * statistic hn X w π)) := by
    let L : (Fin N → ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.mulLeft ℝ t).comp (statisticLinear hn w π)
    simpa [L, Function.comp_def] using convexOn_exp.comp_linearMap L
  refine ⟨convex_univ, ?_⟩
  intro X _ Y _ a b ha hb hab
  unfold mgf SharpSerfling.finiteAverage
  have hsum :
      (∑ π : Equiv.Perm (Fin N), Real.exp (t * statistic hn (a • X + b • Y) w π)) ≤
        ∑ π : Equiv.Perm (Fin N),
          (a * Real.exp (t * statistic hn X w π) +
            b * Real.exp (t * statistic hn Y w π)) := by
    apply Finset.sum_le_sum
    intro π _
    simpa [smul_eq_mul] using
      (hterm π).2 (Set.mem_univ X) (Set.mem_univ Y) ha hb hab
  calc
    (∑ π : Equiv.Perm (Fin N), Real.exp (t * statistic hn (a • X + b • Y) w π)) /
          Fintype.card (Equiv.Perm (Fin N)) ≤
        (∑ π : Equiv.Perm (Fin N),
          (a * Real.exp (t * statistic hn X w π) +
            b * Real.exp (t * statistic hn Y w π))) /
          Fintype.card (Equiv.Perm (Fin N)) :=
      div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
    _ = a • ((∑ π : Equiv.Perm (Fin N), Real.exp (t * statistic hn X w π)) /
          Fintype.card (Equiv.Perm (Fin N))) +
        b • ((∑ π : Equiv.Perm (Fin N), Real.exp (t * statistic hn Y w π)) /
          Fintype.card (Equiv.Perm (Fin N))) := by
      simp only [Finset.sum_add_distrib, smul_eq_mul]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring

/-- Every point of the real unit cube belongs to the convex hull of its
binary vertices. -/
theorem mem_convexHull_binary_of_mem_unitCube {N : ℕ} {X : Fin N → ℝ}
    (hX : X ∈ Set.Icc (0 : Fin N → ℝ) 1) :
    X ∈ convexHull ℝ (Set.univ.pi fun _ : Fin N ↦ ({0, 1} : Set ℝ)) := by
  apply mem_convexHull_pi
  intro i _
  rw [convexHull_pair, segment_eq_uIcc, uIcc_of_le zero_le_one]
  exact ⟨hX.1 i, hX.2 i⟩

/-- The corresponding convex-hull fact for an arbitrary scalar interval. -/
theorem mem_convexHull_endpoints_of_mem_Icc {N : ℕ} {a b : ℝ} (hab : a ≤ b)
    {X : Fin N → ℝ} (hX : X ∈ Set.Icc (fun _ ↦ a) (fun _ ↦ b)) :
    X ∈ convexHull ℝ (Set.univ.pi fun _ : Fin N ↦ ({a, b} : Set ℝ)) := by
  apply mem_convexHull_pi
  intro i _
  rw [convexHull_pair, segment_eq_uIcc, uIcc_of_le hab]
  exact ⟨hX.1 i, hX.2 i⟩

/-- Manuscript Lemma `lem:binary-reduction`, in its pointwise maximum
principle form: every bounded population is dominated by a binary vertex for
the same fixed coefficient vector and tilt. -/
theorem binaryReduction {N n : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) (t : ℝ)
    (X : Fin N → ℝ) (hX : ∀ j, 0 ≤ X j ∧ X j ≤ 1) :
    ∃ v : Fin N → ℝ, (∀ j, v j = 0 ∨ v j = 1) ∧ mgf hn X w t ≤ mgf hn v w t := by
  have hcube : X ∈ Set.Icc (0 : Fin N → ℝ) 1 :=
    ⟨fun j ↦ (hX j).1, fun j ↦ (hX j).2⟩
  have hHull := mem_convexHull_binary_of_mem_unitCube hcube
  obtain ⟨v, hv, hle⟩ :=
    (convex_mgf_population hn w t).exists_ge_of_mem_convexHull
      (t := Set.univ.pi fun _ : Fin N ↦ ({0, 1} : Set ℝ)) (Set.subset_univ _) hHull
  refine ⟨v, ?_, hle⟩
  intro j
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hv j (Set.mem_univ j)

/-- Affine-range version of `binaryReduction`: a population in `[a,b]` is
dominated by a population whose coordinates are endpoints of that interval. -/
theorem binaryRangeReduction {N n : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) (t : ℝ)
    {a b : ℝ} (hab : a ≤ b) (X : Fin N → ℝ)
    (hX : ∀ j, a ≤ X j ∧ X j ≤ b) :
    ∃ v : Fin N → ℝ, (∀ j, v j = a ∨ v j = b) ∧ mgf hn X w t ≤ mgf hn v w t := by
  have hcube : X ∈ Set.Icc (fun _ : Fin N ↦ a) (fun _ ↦ b) :=
    ⟨fun j ↦ (hX j).1, fun j ↦ (hX j).2⟩
  have hHull := mem_convexHull_endpoints_of_mem_Icc hab hcube
  obtain ⟨v, hv, hle⟩ :=
    (convex_mgf_population hn w t).exists_ge_of_mem_convexHull
      (t := Set.univ.pi fun _ : Fin N ↦ ({a, b} : Set ℝ)) (Set.subset_univ _) hHull
  refine ⟨v, ?_, hle⟩
  intro j
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hv j (Set.mem_univ j)

end SharpSerfling.FinitePopulation
