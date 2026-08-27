import SharpSerfling.FinitePopulation.Slice
import Mathlib.Topology.MetricSpace.Bounded

namespace SharpSerfling.FinitePopulation

open scoped BigOperators
open Set Bornology

/-- Squared Euclidean norm on a finite real coordinate space. -/
noncomputable def sqNorm {N : ℕ} (y : Fin N → ℝ) : ℝ :=
  ∑ i, (y i) ^ 2

/-- The centered Euclidean sphere section used in the cited two-level
variational proposition.  The parameter is the squared radius. -/
def centeredSphere (N : ℕ) (rSq : ℝ) : Set (Fin N → ℝ) :=
  {y | (∑ i, y i) = 0 ∧ sqNorm y = rSq}

theorem continuous_sqNorm {N : ℕ} : Continuous (sqNorm : (Fin N → ℝ) → ℝ) := by
  unfold sqNorm
  fun_prop

theorem isClosed_centeredSphere (N : ℕ) (rSq : ℝ) : IsClosed (centeredSphere N rSq) := by
  unfold centeredSphere
  have hsum : Continuous (fun y : Fin N → ℝ ↦ ∑ i, y i) := by fun_prop
  exact (isClosed_eq hsum continuous_const).inter
    (isClosed_eq continuous_sqNorm continuous_const)

theorem isBounded_centeredSphere {N : ℕ} {rSq : ℝ} (hr : 0 ≤ rSq) :
    IsBounded (centeredSphere N rSq) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨rSq + 1, ?_⟩
  intro y hy
  rw [pi_norm_le_iff_of_nonneg (by linarith)]
  intro i
  rw [Real.norm_eq_abs]
  have hi : (y i) ^ 2 ≤ ∑ j, (y j) ^ 2 := by
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (y j)) (Finset.mem_univ i)
  rw [show (∑ j, (y j) ^ 2) = rSq by exact hy.2] at hi
  have habsSq : |y i| ^ 2 = (y i) ^ 2 := sq_abs (y i)
  have hsq : |y i| ^ 2 ≤ rSq := by simpa [habsSq] using hi
  have hrlt : rSq < (rSq + 1) ^ 2 := by nlinarith [sq_nonneg rSq]
  have habs : 0 ≤ |y i| := abs_nonneg _
  nlinarith [sq_nonneg (|y i| + (rSq + 1))]

theorem isCompact_centeredSphere {N : ℕ} {rSq : ℝ} (hr : 0 ≤ rSq) :
    IsCompact (centeredSphere N rSq) := by
  exact (Metric.isCompact_iff_isClosed_bounded (s := centeredSphere N rSq)).2
    ⟨isClosed_centeredSphere N rSq, isBounded_centeredSphere hr⟩

theorem continuous_sliceMgf (N K : ℕ) :
    Continuous (sliceMgf N K : (Fin N → ℝ) → ℝ) := by
  unfold sliceMgf SharpSerfling.finiteAverage
  fun_prop

/-- The slice objective attains a maximum on every nonempty centered sphere
section. -/
theorem exists_sliceMgf_maximizer {N K : ℕ} {rSq : ℝ} (hr : 0 ≤ rSq)
    {y : Fin N → ℝ} (hy : y ∈ centeredSphere N rSq) :
    ∃ z ∈ centeredSphere N rSq,
      ∀ x ∈ centeredSphere N rSq, sliceMgf N K x ≤ sliceMgf N K z := by
  obtain ⟨z, hz, hmax⟩ :=
    (isCompact_centeredSphere hr).exists_isMaxOn ⟨y, hy⟩
      (continuous_sliceMgf N K).continuousOn
  exact ⟨z, hz, hmax⟩

end SharpSerfling.FinitePopulation
