import SharpSerfling.FinitePopulation.Slice
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

namespace SharpSerfling

open scoped BigOperators

/-- Fubini's identity for two uniform finite averages. -/
theorem finiteAverage_comm {A B : Type*} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    finiteAverage (fun a ↦ finiteAverage (fun b ↦ f a b)) =
      finiteAverage (fun b ↦ finiteAverage (fun a ↦ f a b)) := by
  unfold finiteAverage
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Uniform finite averaging is invariant under group inversion. -/
theorem finiteAverage_inv {G : Type*} [Group G] [Fintype G] (f : G → ℝ) :
    finiteAverage (fun g : G ↦ f g⁻¹) = finiteAverage f := by
  unfold finiteAverage
  rw [show (∑ g : G, f g⁻¹) = ∑ g : G, f g by
    simpa only [Equiv.inv_apply] using (Equiv.sum_comp (Equiv.inv G) f)]

/-- Averaging a function along the orbit of one point under a finite
pretransitive group action gives its uniform average over the acted-on type. -/
theorem finiteAverage_orbit_eq {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [Nonempty X] [MulAction G X] [MulAction.IsPretransitive G X]
    (x₀ : X) (f : X → ℝ) :
    finiteAverage (fun g : G ↦ f (g • x₀)) = finiteAverage f := by
  have horbit (x : X) :
      finiteAverage (fun g : G ↦ f (g • x)) =
        finiteAverage (fun g : G ↦ f (g • x₀)) := by
    obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq G x₀ x
    let e : G ≃ G := Equiv.mulRight h
    calc
      finiteAverage (fun g : G ↦ f (g • (h • x₀))) =
          finiteAverage ((fun g : G ↦ f (g • x₀)) ∘ e) := by
        apply congrArg finiteAverage
        funext g
        simp [e, smul_smul]
      _ = finiteAverage (fun g : G ↦ f (g • x₀)) :=
        finiteAverage_equiv e _
  calc
    finiteAverage (fun g : G ↦ f (g • x₀)) =
        finiteAverage (fun x : X ↦ finiteAverage (fun g : G ↦ f (g • x))) := by
      simp_rw [horbit]
      exact (finiteAverage_const _).symm
    _ = finiteAverage (fun g : G ↦ finiteAverage (fun x : X ↦ f (g • x))) :=
      finiteAverage_comm _
    _ = finiteAverage (fun _g : G ↦ finiteAverage f) := by
      apply congrArg finiteAverage
      funext g
      exact finiteAverage_equiv (MulAction.toPerm g) f
    _ = finiteAverage f := finiteAverage_const _

end SharpSerfling

namespace SharpSerfling.FinitePopulation

open SharpSerfling.Hypergeometric

/-- A fixed-cardinality subset average is the same as averaging the orbit of
any one subset under all population permutations. -/
theorem finiteAverage_sample_orbit {N K : ℕ} (hK : K ≤ N) (s₀ : Sample N K)
    (f : Sample N K → ℝ) :
    SharpSerfling.finiteAverage
        (fun π : Equiv.Perm (Fin N) ↦ f (π • s₀)) =
      SharpSerfling.finiteAverage f := by
  letI : Nonempty (Sample N K) := sample_nonempty hK
  letI : MulAction.IsPretransitive (Equiv.Perm (Fin N)) (Sample N K) :=
    Set.powersetCard.isPretransitive
  exact SharpSerfling.finiteAverage_orbit_eq s₀ f

end SharpSerfling.FinitePopulation
