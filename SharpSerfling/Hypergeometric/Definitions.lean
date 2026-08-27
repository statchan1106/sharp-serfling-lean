import SharpSerfling.Basic
import SharpSerfling.FiniteAverage
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Set.PowersetCard

namespace SharpSerfling.Hypergeometric

open scoped BigOperators

/-- The canonical set of the first `K` marked elements in a population of size `N`. -/
def marked (N K : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i => (i : ℕ) < K

/-- All size-`m` samples from a population of size `N`. -/
abbrev Sample (N m : ℕ) := Set.powersetCard (Fin N) m

/-- Number of marked elements in a fixed-cardinality sample. -/
def count {N m : ℕ} (K : ℕ) (s : Sample N m) : ℕ :=
  (s.1 ∩ marked N K).card

theorem card_sample (N m : ℕ) : Fintype.card (Sample N m) = Nat.choose N m := by
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_fin]

theorem sample_nonempty {N m : ℕ} (hm : m ≤ N) : Nonempty (Sample N m) := by
  classical
  have hnonempty : ((Finset.univ : Finset (Fin N)).powersetCard m).Nonempty := by
    rw [Finset.powersetCard_nonempty]
    simpa using hm
  obtain ⟨s, hs⟩ := hnonempty
  exact ⟨⟨s, (Finset.mem_powersetCard.mp hs).2⟩⟩

theorem card_marked {N K : ℕ} (hK : K ≤ N) : (marked N K).card = K := by
  rw [marked, Fin.card_filter_val_lt, Nat.min_eq_right hK]

theorem count_le_sample {N K m : ℕ} (s : Sample N m) : count K s ≤ m := by
  change (s.1 ∩ marked N K).card ≤ m
  calc
    (s.1 ∩ marked N K).card ≤ s.1.card :=
      Finset.card_le_card Finset.inter_subset_left
    _ = m := s.property

theorem count_le_marked {N K m : ℕ} (hK : K ≤ N) (s : Sample N m) : count K s ≤ K := by
  change (s.1 ∩ marked N K).card ≤ K
  calc
    (s.1 ∩ marked N K).card ≤ (marked N K).card :=
      Finset.card_le_card Finset.inter_subset_right
    _ = K := card_marked hK

/-- Centering constant `K m / N`, regarded as a real number. -/
noncomputable def center (N K m : ℕ) : ℝ :=
  (K : ℝ) * (m : ℝ) / (N : ℝ)

/-- Centered hypergeometric MGF, defined as an explicit uniform finite average. -/
noncomputable def mgf (N K m : ℕ) (t : ℝ) : ℝ :=
  SharpSerfling.finiteAverage fun s : Sample N m =>
    Real.exp (t * ((count K s : ℕ) - center N K m))

/-- The exact variance prefactor in the dimension-reducing identity. -/
noncomputable def variance (N K m : ℕ) : ℝ :=
  (K : ℝ) * ((N : ℝ) - (K : ℝ)) * (m : ℝ) * ((N : ℝ) - (m : ℝ)) /
    ((N : ℝ) ^ 2 * ((N : ℝ) - 1))

/-- The linear exponential tilt in the dimension-reducing identity. -/
noncomputable def recursionTilt (N K m : ℕ) : ℝ :=
  (((N : ℝ) - 2 * (K : ℝ)) * ((N : ℝ) - 2 * (m : ℝ))) /
    (2 * (N : ℝ) * ((N : ℝ) - 2))

theorem mgf_zero (N K m : ℕ) [Nonempty (Sample N m)] : mgf N K m 0 = 1 := by
  simp [mgf, SharpSerfling.finiteAverage_one]

theorem mgf_zero_of_le (N K m : ℕ) (hm : m ≤ N) : mgf N K m 0 = 1 := by
  letI : Nonempty (Sample N m) := sample_nonempty hm
  exact mgf_zero N K m

theorem mgf_pos {N K m : ℕ} (hm : m ≤ N) (t : ℝ) : 0 < mgf N K m t := by
  letI : Nonempty (Sample N m) := sample_nonempty hm
  exact SharpSerfling.finiteAverage_pos _ fun _ => Real.exp_pos _

theorem mgf_zeroSuccesses {N m : ℕ} (hm : m ≤ N) (t : ℝ) : mgf N 0 m t = 1 := by
  letI : Nonempty (Sample N m) := sample_nonempty hm
  simp [mgf, count, marked, center, SharpSerfling.finiteAverage_one]

theorem mgf_allSuccesses {N m : ℕ} (hN : 0 < N) (hm : m ≤ N) (t : ℝ) :
    mgf N N m t = 1 := by
  letI : Nonempty (Sample N m) := sample_nonempty hm
  have hcenter : center N N m = (m : ℝ) := by
    unfold center
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp
  have hcount (s : Sample N m) : count N s = m := by
    change (s.1 ∩ marked N N).card = m
    rw [show marked N N = Finset.univ by ext i; simp [marked]]
    simp
  simp_rw [mgf, hcount, hcenter, sub_self, mul_zero, Real.exp_zero]
  exact SharpSerfling.finiteAverage_one

/-- Exact statement of manuscript Theorem `thm:hypergeom`. -/
def SharpMGFStatement : Prop :=
  ∀ N K m : ℕ, 2 ≤ N → K ≤ N → 1 ≤ m → m ≤ N - 1 → ∀ t : ℝ,
    Real.log (mgf N K m t) ≤
      SharpSerfling.kappa N * SharpSerfling.hypergeomScale N m * t ^ 2

end SharpSerfling.Hypergeometric
