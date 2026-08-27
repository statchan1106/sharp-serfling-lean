import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace SharpSerfling

open scoped BigOperators

/-- Uniform average on an explicitly finite type. -/
noncomputable def finiteAverage {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

theorem finiteAverage_zero {Ω : Type*} [Fintype Ω] :
    finiteAverage (fun _ : Ω => (0 : ℝ)) = 0 := by
  simp [finiteAverage]

theorem finiteAverage_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    finiteAverage (fun _ : Ω => c) = c := by
  rw [finiteAverage, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

theorem finiteAverage_one {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    finiteAverage (fun _ : Ω => (1 : ℝ)) = 1 := by
  exact finiteAverage_const 1

theorem finiteAverage_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    finiteAverage (fun ω => f ω + g ω) = finiteAverage f + finiteAverage g := by
  simp [finiteAverage, Finset.sum_add_distrib, add_div]

theorem finiteAverage_smul {Ω : Type*} [Fintype Ω] (c : ℝ) (f : Ω → ℝ) :
    finiteAverage (fun ω => c * f ω) = c * finiteAverage f := by
  rw [finiteAverage, finiteAverage, ← Finset.mul_sum, mul_div_assoc]

theorem finiteAverage_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ finiteAverage f := by
  rw [finiteAverage]
  exact div_nonneg (Finset.sum_nonneg fun ω _ => hf ω) (Nat.cast_nonneg _)

theorem finiteAverage_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ)
    (hf : ∀ ω, 0 < f ω) : 0 < finiteAverage f := by
  rw [finiteAverage]
  apply div_pos
  · rw [Finset.sum_pos_iff_of_nonneg]
    · obtain ⟨ω⟩ := ‹Nonempty Ω›
      exact ⟨ω, Finset.mem_univ _, hf ω⟩
    · intro ω _
      exact (hf ω).le
  · exact_mod_cast Fintype.card_pos

/-- Uniform averages are invariant under a relabeling of the finite sample space. -/
theorem finiteAverage_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (f : Ω' → ℝ) : finiteAverage (f ∘ e) = finiteAverage f := by
  unfold finiteAverage
  simp only [Function.comp_apply]
  rw [e.sum_comp, Fintype.card_congr e]

end SharpSerfling
