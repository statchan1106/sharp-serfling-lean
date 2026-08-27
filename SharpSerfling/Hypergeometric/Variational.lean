import SharpSerfling.Hypergeometric.Sharpness

namespace SharpSerfling.Hypergeometric

open Filter Topology

/-- The dimensionless logarithmic-MGF ratio occurring literally in
Proposition 1.  The variational set below excludes `t = 0`, so no value is
assigned to the removable singularity here. -/
noncomputable def normalizedLogMgf (N K m : ℕ) (t : ℝ) : ℝ :=
  Real.log (mgf N K m t) /
    (SharpSerfling.hypergeomScale N m * t ^ 2)

/-- The flattened set of all values under the `max_m sup_{K,t≠0}` in the
manuscript definition of `κ_N★`.  Flattening the two finite maxima and the
real supremum does not change their value. -/
def variationalValues (N : ℕ) : Set ℝ :=
  {x | ∃ K m : ℕ, K ≤ N ∧ 1 ≤ m ∧ m ≤ N - 1 ∧
      ∃ t : ℝ, t ≠ 0 ∧ x = normalizedLogMgf N K m t}

/-- The sharp coefficient as the literal variational supremum from
Proposition 1. -/
noncomputable def kappaStar (N : ℕ) : ℝ :=
  sSup (variationalValues N)

theorem hypergeomScale_pos_of_nontrivial {N m : ℕ} (hN : 2 ≤ N)
    (hm0 : 1 ≤ m) (hmN : m ≤ N - 1) :
    0 < SharpSerfling.hypergeomScale N m := by
  unfold SharpSerfling.hypergeomScale
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hmNR : (m : ℝ) < (N : ℝ) := by exact_mod_cast (show m < N by omega)
  have hNm1 : 0 < (N : ℝ) - 1 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  positivity

theorem variationalValues_nonempty {N : ℕ} (hN : 2 ≤ N) :
    (variationalValues N).Nonempty := by
  refine ⟨0, 0, 1, by omega, by omega, by omega, 1, one_ne_zero, ?_⟩
  rw [normalizedLogMgf, mgf_zeroSuccesses (by omega)]
  norm_num

theorem normalizedLogMgf_le_kappa {N K m : ℕ} (hN : 2 ≤ N)
    (hK : K ≤ N) (hm0 : 1 ≤ m) (hmN : m ≤ N - 1)
    {t : ℝ} (ht : t ≠ 0) :
    normalizedLogMgf N K m t ≤ SharpSerfling.kappa N := by
  have hscale := hypergeomScale_pos_of_nontrivial hN hm0 hmN
  have hden : 0 < SharpSerfling.hypergeomScale N m * t ^ 2 :=
    mul_pos hscale (sq_pos_of_ne_zero ht)
  rw [normalizedLogMgf, div_le_iff₀ hden]
  calc
    Real.log (mgf N K m t) ≤
        SharpSerfling.kappa N * SharpSerfling.hypergeomScale N m * t ^ 2 :=
      sharp_mgf hN hK (by omega) t
    _ = SharpSerfling.kappa N *
        (SharpSerfling.hypergeomScale N m * t ^ 2) := by ring

theorem variationalValues_bddAbove {N : ℕ} (hN : 2 ≤ N) :
    BddAbove (variationalValues N) := by
  refine ⟨SharpSerfling.kappa N, ?_⟩
  rintro x ⟨K, m, hK, hm0, hmN, t, ht, rfl⟩
  exact normalizedLogMgf_le_kappa hN hK hm0 hmN ht

theorem kappaStar_le_kappa {N : ℕ} (hN : 2 ≤ N) :
    kappaStar N ≤ SharpSerfling.kappa N := by
  unfold kappaStar
  exact csSup_le (variationalValues_nonempty hN) (by
    intro x hx
    rcases hx with ⟨K, m, hK, hm0, hmN, t, ht, rfl⟩
    exact normalizedLogMgf_le_kappa hN hK hm0 hmN ht)

/-- The variational supremum is itself a valid uniform coefficient. -/
theorem uniformCoefficient_kappaStar {N : ℕ} (hN : 2 ≤ N) :
    UniformCoefficient N (kappaStar N) := by
  intro K m hK hm0 hmN t
  by_cases ht : t = 0
  · subst t
    rw [mgf_zero_of_le N K m (by omega)]
    norm_num
  · have hmem : normalizedLogMgf N K m t ∈ variationalValues N :=
      ⟨K, m, hK, hm0, hmN, t, ht, rfl⟩
    have hratio : normalizedLogMgf N K m t ≤ kappaStar N :=
      le_csSup (variationalValues_bddAbove hN) hmem
    have hscale := hypergeomScale_pos_of_nontrivial hN hm0 hmN
    have hden : 0 < SharpSerfling.hypergeomScale N m * t ^ 2 :=
      mul_pos hscale (sq_pos_of_ne_zero ht)
    rw [normalizedLogMgf, div_le_iff₀ hden] at hratio
    calc
      Real.log (mgf N K m t) ≤
          kappaStar N * (SharpSerfling.hypergeomScale N m * t ^ 2) := hratio
      _ = kappaStar N * SharpSerfling.hypergeomScale N m * t ^ 2 := by ring

/-- Proposition 1 in its literal variational form: the maximum/supremum
coefficient is exactly the parity-dependent closed form `κ_N`. -/
theorem kappaStar_eq_kappa {N : ℕ} (hN : 2 ≤ N) :
    kappaStar N = SharpSerfling.kappa N := by
  apply le_antisymm (kappaStar_le_kappa hN)
  exact kappa_le_of_uniformCoefficient hN (uniformCoefficient_kappaStar hN)

/-- For odd population size, the manuscript's explicit one-draw choice
`K=(N-1)/2`, `t=2 log((N+1)/(N-1))` attains the variational supremum. -/
theorem normalizedLogMgf_odd_witness {q : ℕ} (hq : 0 < q) :
    normalizedLogMgf (2 * q + 1) q 1
        (2 * oddLogIncrement (2 * q + 1)) =
      SharpSerfling.kappa (2 * q + 1) := by
  let L := oddLogIncrement (2 * q + 1)
  have hL : 0 < L := by
    dsimp [L]
    exact oddLogIncrement_pos (by omega)
  have hnotEven : ¬Even (2 * q + 1) :=
    Nat.not_even_iff_odd.mpr ⟨q, by omega⟩
  rw [normalizedLogMgf, log_mgf_one_eq_phi hq (by omega),
    onePhi_odd_witness hq, hypergeomScale_one (by omega),
    SharpSerfling.kappa_of_not_even hnotEven]
  have hlog :
      Real.log ((((2 * q + 1 : ℕ) : ℝ) + 1) /
        (((2 * q + 1 : ℕ) : ℝ) - 1)) = L := by
    dsimp [L]
    unfold oddLogIncrement
    congr 1
  rw [hlog]
  dsimp [L] at hL ⊢
  push_cast
  field_simp [ne_of_gt hL]
  norm_num

theorem kappaStar_odd_attained {q : ℕ} (hq : 0 < q) :
    normalizedLogMgf (2 * q + 1) q 1
        (2 * oddLogIncrement (2 * q + 1)) = kappaStar (2 * q + 1) := by
  rw [normalizedLogMgf_odd_witness hq, kappaStar_eq_kappa (by omega)]

end SharpSerfling.Hypergeometric
