import SharpSerfling.Hypergeometric.KearnsSaul
import Mathlib.Analysis.Calculus.DerivativeTest

namespace SharpSerfling.Hypergeometric

open Filter Topology

/-- A coefficient valid uniformly over every nontrivial hypergeometric slice. -/
def UniformCoefficient (N : ℕ) (c : ℝ) : Prop :=
  ∀ K m : ℕ, K ≤ N → 1 ≤ m → m ≤ N - 1 → ∀ t : ℝ,
    Real.log (mgf N K m t) ≤ c * SharpSerfling.hypergeomScale N m * t ^ 2

theorem second_deriv_nonneg_of_global_min {g : ℝ → ℝ}
    (hmin : ∀ x, g 0 ≤ g x) (hderiv : deriv g 0 = 0)
    (hcont : ContinuousAt g 0) :
    0 ≤ deriv (deriv g) 0 := by
  by_contra hnot
  have hneg : deriv (deriv g) 0 < 0 := lt_of_not_ge hnot
  have hmax : IsLocalMax g 0 := isLocalMax_of_deriv_deriv_neg hneg hderiv hcont
  have heq : Filter.EventuallyEq (nhds 0) g (fun _ ↦ g 0) := by
    filter_upwards [hmax] with x hx
    exact le_antisymm hx (hmin x)
  have hderivEq : Filter.EventuallyEq (nhds 0) (deriv g)
      (deriv (fun _ : ℝ ↦ g 0)) := heq.deriv
  have hsecond : deriv (deriv g) 0 = deriv (deriv (fun _ : ℝ ↦ g 0)) 0 :=
    hderivEq.deriv_eq
  rw [deriv_const'] at hsecond
  norm_num at hsecond
  linarith

noncomputable def evenSharpnessGap (c : ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  c * t ^ 2 / 8 - onePhi (2 * q) q t

noncomputable def evenSharpnessGapDeriv1 (c : ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  c * t / 4 - onePhiDeriv1 (2 * q) q t

noncomputable def evenSharpnessGapDeriv2 (c : ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  c / 4 - onePhiDeriv2 (2 * q) q t

theorem hasDerivAt_evenSharpnessGap {c : ℝ} {q : ℕ} (hq : 0 < q) (t : ℝ) :
    HasDerivAt (evenSharpnessGap c q) (evenSharpnessGapDeriv1 c q t) t := by
  have hphi := hasDerivAt_onePhi (N := 2 * q) (K := q) hq (by omega) t
  have hquad := ((hasDerivAt_const t c).mul (hasDerivAt_pow 2 t)).div_const 8
  have htotal := hquad.fun_sub hphi
  exact htotal.congr_deriv (by
    unfold evenSharpnessGapDeriv1
    norm_num
    ring)

theorem hasDerivAt_evenSharpnessGapDeriv1 {c : ℝ} {q : ℕ}
    (hq : 0 < q) (t : ℝ) :
    HasDerivAt (evenSharpnessGapDeriv1 c q) (evenSharpnessGapDeriv2 c q t) t := by
  have hphi := hasDerivAt_onePhiDeriv1 (N := 2 * q) (K := q) hq (by omega) t
  have hlin := ((hasDerivAt_const t c).mul (hasDerivAt_id t)).div_const 4
  have htotal := hlin.fun_sub hphi
  exact htotal.congr_deriv (by
    unfold evenSharpnessGapDeriv2
    norm_num)

theorem evenSharpnessGap_zero {c : ℝ} {q : ℕ} (hq : 0 < q) :
    evenSharpnessGap c q 0 = 0 := by
  unfold evenSharpnessGap
  rw [onePhi_zero (by omega) (by omega)]
  norm_num

theorem evenSharpnessGap_deriv_zero {c : ℝ} {q : ℕ} (hq : 0 < q) :
    deriv (evenSharpnessGap c q) 0 = 0 := by
  rw [(hasDerivAt_evenSharpnessGap hq 0).deriv]
  unfold evenSharpnessGapDeriv1 onePhiDeriv1 onePartitionDeriv onePartition
  norm_num

theorem evenSharpnessGap_second_deriv {c : ℝ} {q : ℕ} (hq : 0 < q) :
    deriv (deriv (evenSharpnessGap c q)) 0 = c / 4 - 1 / 4 := by
  have hfirst : deriv (evenSharpnessGap c q) = evenSharpnessGapDeriv1 c q := by
    funext t
    exact (hasDerivAt_evenSharpnessGap hq t).deriv
  rw [hfirst, (hasDerivAt_evenSharpnessGapDeriv1 hq 0).deriv]
  unfold evenSharpnessGapDeriv2 onePhiDeriv2 onePartitionDeriv onePartition
  norm_num
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp [hqR]
  ring

theorem hypergeomScale_one {N : ℕ} (hN : 2 ≤ N) :
    SharpSerfling.hypergeomScale N 1 = 1 / 8 := by
  unfold SharpSerfling.hypergeomScale
  norm_num only [Nat.cast_one]
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  field_simp [hN1]

theorem onePhi_odd_witness {q : ℕ} (hq : 0 < q) :
    onePhi (2 * q + 1) q (2 * oddLogIncrement (2 * q + 1)) =
      oddLogIncrement (2 * q + 1) / (2 * (q : ℝ) + 1) := by
  have hlogEq : oneLogIncrement (2 * q + 1) q = oddLogIncrement (2 * q + 1) := by
    unfold oneLogIncrement oddLogIncrement
    congr 1
    push_cast
    field_simp [show (q : ℝ) ≠ 0 by positivity]
    ring
  have hreflect := onePhi_reflect (N := 2 * q + 1) (K := q) hq (by omega) 0
  rw [sub_zero, onePhi_zero (by omega) (by omega)] at hreflect
  rw [hlogEq] at hreflect
  convert hreflect using 1 <;> push_cast <;> ring

theorem kappa_le_of_uniformCoefficient {N : ℕ} (hN : 2 ≤ N) {c : ℝ}
    (hc : UniformCoefficient N c) : SharpSerfling.kappa N ≤ c := by
  by_cases hEven : Even N
  · obtain ⟨q, hqN⟩ := hEven
    subst N
    have hq : 0 < q := by omega
    have hbound (t : ℝ) : 0 ≤ evenSharpnessGap c q t := by
      have hu := hc q 1 (by omega) (by omega) (by omega) t
      rw [log_mgf_one_eq_phi hq (by omega), hypergeomScale_one (by omega)] at hu
      have hu' : onePhi (2 * q) q t ≤ c * (1 / 8 : ℝ) * t ^ 2 := by
        simpa [two_mul] using hu
      unfold evenSharpnessGap
      linarith [hu']
    have hmin : ∀ t, evenSharpnessGap c q 0 ≤ evenSharpnessGap c q t := by
      intro t
      rw [evenSharpnessGap_zero hq]
      exact hbound t
    have hsecond := second_deriv_nonneg_of_global_min hmin
      (evenSharpnessGap_deriv_zero hq)
      (hasDerivAt_evenSharpnessGap hq 0).continuousAt
    rw [evenSharpnessGap_second_deriv hq] at hsecond
    rw [SharpSerfling.kappa_of_even ⟨q, rfl⟩]
    linarith
  · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
    obtain ⟨q, hqN⟩ := hOdd
    subst N
    have hq : 0 < q := by omega
    let L := oddLogIncrement (2 * q + 1)
    have hLpos : 0 < L := by
      dsimp [L]
      exact oddLogIncrement_pos (by omega)
    have hu := hc q 1 (by omega) (by omega) (by omega) (2 * L)
    rw [log_mgf_one_eq_phi hq (by omega), hypergeomScale_one (by omega)] at hu
    rw [show onePhi (2 * q + 1) q (2 * L) = L / (2 * (q : ℝ) + 1) by
      simpa [L] using onePhi_odd_witness hq] at hu
    have hnotEven : ¬Even (2 * q + 1) := by omega
    rw [SharpSerfling.kappa_of_not_even hnotEven]
    dsimp only [L] at hu hLpos
    unfold oddLogIncrement at hu hLpos
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    push_cast at hu hLpos
    have hNpos : 0 < 2 * (q : ℝ) + 1 := by positivity
    rw [div_le_iff₀ (mul_pos hNpos hLpos)]
    rw [div_le_iff₀ hNpos] at hu
    nlinarith

/-- Manuscript proposition `prop:sharpness`, formulated equivalently as the
validity and minimality of the uniform coefficient `κ_N`. -/
theorem sharp_constant {N : ℕ} (hN : 2 ≤ N) :
    UniformCoefficient N (SharpSerfling.kappa N) ∧
      ∀ c : ℝ, UniformCoefficient N c → SharpSerfling.kappa N ≤ c := by
  constructor
  · intro K m hK hm0 hm t
    exact sharp_mgf hN hK (by omega) t
  · intro c hc
    exact kappa_le_of_uniformCoefficient hN hc

end SharpSerfling.Hypergeometric
