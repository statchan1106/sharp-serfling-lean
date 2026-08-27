import SharpSerfling.Hypergeometric.CentralTwo

namespace SharpSerfling.Hypergeometric

open Finset Finset.Nat

noncomputable def oneLogIncrement (N K : ℕ) : ℝ :=
  Real.log (((N : ℝ) - (K : ℝ)) / (K : ℝ))

noncomputable def onePartition (N K : ℕ) (t : ℝ) : ℝ :=
  ((N : ℝ) - (K : ℝ)) + (K : ℝ) * Real.exp t

noncomputable def onePartitionDeriv (K : ℕ) (t : ℝ) : ℝ :=
  (K : ℝ) * Real.exp t

theorem oneLogIncrement_pos {N K : ℕ} (hK0 : 0 < K) (hKhalf : 2 * K < N) :
    0 < oneLogIncrement N K := by
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK0
  have hhalfR : 2 * (K : ℝ) < (N : ℝ) := by exact_mod_cast hKhalf
  unfold oneLogIncrement
  apply Real.log_pos
  rw [one_lt_div hKR]
  linarith

theorem onePartition_pos {N K : ℕ} (hK0 : 0 < K) (hKN : K < N) (t : ℝ) :
    0 < onePartition N K t := by
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK0
  have hKNR : (K : ℝ) < (N : ℝ) := by exact_mod_cast hKN
  unfold onePartition
  positivity

theorem hasDerivAt_onePartition (N K : ℕ) (t : ℝ) :
    HasDerivAt (onePartition N K) (onePartitionDeriv K t) t := by
  unfold onePartition onePartitionDeriv
  have h := (hasDerivAt_id t).exp.const_mul (K : ℝ)
  have hconst : HasDerivAt (fun _ : ℝ ↦ (N : ℝ) - (K : ℝ)) 0 t :=
    hasDerivAt_const t _
  have htotal := hconst.fun_add h
  simpa only [id_eq, zero_add, mul_one] using htotal

theorem hasDerivAt_onePartitionDeriv (K : ℕ) (t : ℝ) :
    HasDerivAt (onePartitionDeriv K) (onePartitionDeriv K t) t := by
  unfold onePartitionDeriv
  simpa only [id_eq, mul_one] using (hasDerivAt_id t).exp.const_mul (K : ℝ)

noncomputable def onePhi (N K : ℕ) (t : ℝ) : ℝ :=
  -((K : ℝ) / (N : ℝ)) * t + Real.log (onePartition N K t) - Real.log (N : ℝ)

noncomputable def onePhiDeriv1 (N K : ℕ) (t : ℝ) : ℝ :=
  onePartitionDeriv K t / onePartition N K t - (K : ℝ) / (N : ℝ)

noncomputable def onePhiDeriv2 (N K : ℕ) (t : ℝ) : ℝ :=
  onePartitionDeriv K t / onePartition N K t -
    (onePartitionDeriv K t / onePartition N K t) *
      (onePartitionDeriv K t / onePartition N K t)

noncomputable def onePhiDeriv3 (N K : ℕ) (t : ℝ) : ℝ :=
  onePartitionDeriv K t / onePartition N K t -
    3 * onePartitionDeriv K t ^ 2 / onePartition N K t ^ 2 +
    2 * onePartitionDeriv K t ^ 3 / onePartition N K t ^ 3

theorem hasDerivAt_onePhi {N K : ℕ} (hK0 : 0 < K) (hKN : K < N) (t : ℝ) :
    HasDerivAt (onePhi N K) (onePhiDeriv1 N K t) t := by
  have hP := hasDerivAt_onePartition N K t
  have hPne : onePartition N K t ≠ 0 := ne_of_gt (onePartition_pos hK0 hKN t)
  have hlin := (hasDerivAt_id t).const_mul (-((K : ℝ) / (N : ℝ)))
  have htotal := (hlin.fun_add (hP.log hPne)).sub_const (Real.log (N : ℝ))
  change HasDerivAt
    (fun x : ℝ ↦ -((K : ℝ) / (N : ℝ)) * x +
      Real.log (onePartition N K x) - Real.log (N : ℝ))
    (onePartitionDeriv K t / onePartition N K t - (K : ℝ) / (N : ℝ)) t
  exact htotal.congr_deriv (by ring)

theorem hasDerivAt_onePhiDeriv1 {N K : ℕ} (hK0 : 0 < K) (hKN : K < N) (t : ℝ) :
    HasDerivAt (onePhiDeriv1 N K) (onePhiDeriv2 N K t) t := by
  have hP := hasDerivAt_onePartition N K t
  have hP1 := hasDerivAt_onePartitionDeriv K t
  have hPne : onePartition N K t ≠ 0 := ne_of_gt (onePartition_pos hK0 hKN t)
  have hratio := hP1.fun_div hP hPne
  have htotal := hratio.sub_const ((K : ℝ) / (N : ℝ))
  have heq :
      (onePartitionDeriv K t * onePartition N K t -
          onePartitionDeriv K t * onePartitionDeriv K t) /
            onePartition N K t ^ 2 = onePhiDeriv2 N K t := by
    unfold onePhiDeriv2
    field_simp [hPne]
  exact htotal.congr_deriv heq

theorem hasDerivAt_onePhiDeriv2 {N K : ℕ} (hK0 : 0 < K) (hKN : K < N) (t : ℝ) :
    HasDerivAt (onePhiDeriv2 N K) (onePhiDeriv3 N K t) t := by
  have hP := hasDerivAt_onePartition N K t
  have hP1 := hasDerivAt_onePartitionDeriv K t
  have hPne : onePartition N K t ≠ 0 := ne_of_gt (onePartition_pos hK0 hKN t)
  have hr := hP1.fun_div hP hPne
  have htotal := hr.fun_sub (hr.fun_mul hr)
  have heq :
      (onePartitionDeriv K t * onePartition N K t -
          onePartitionDeriv K t * onePartitionDeriv K t) /
            onePartition N K t ^ 2 -
        (((onePartitionDeriv K t * onePartition N K t -
              onePartitionDeriv K t * onePartitionDeriv K t) /
                onePartition N K t ^ 2) *
              (onePartitionDeriv K t / onePartition N K t) +
          (onePartitionDeriv K t / onePartition N K t) *
            ((onePartitionDeriv K t * onePartition N K t -
                onePartitionDeriv K t * onePartitionDeriv K t) /
                  onePartition N K t ^ 2)) = onePhiDeriv3 N K t := by
    unfold onePhiDeriv3
    field_simp [hPne]
    ring
  exact htotal.congr_deriv heq

theorem onePhiDeriv3_factor {N K : ℕ} (hK0 : 0 < K) (hKN : K < N) (t : ℝ) :
    onePhiDeriv3 N K t =
      (K : ℝ) * ((N : ℝ) - (K : ℝ)) * Real.exp t *
        (((N : ℝ) - (K : ℝ)) - (K : ℝ) * Real.exp t) /
          onePartition N K t ^ 3 := by
  have hPne : onePartition N K t ≠ 0 := ne_of_gt (onePartition_pos hK0 hKN t)
  unfold onePhiDeriv3 onePartitionDeriv onePartition
  field_simp [hPne]
  ring

theorem onePhiDeriv3_nonneg_before_midpoint {N K : ℕ}
    (hK0 : 0 < K) (hKhalf : 2 * K < N) {t : ℝ}
    (ht : t ≤ oneLogIncrement N K) :
    0 ≤ onePhiDeriv3 N K t := by
  have hKN : K < N := by omega
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK0
  have hKNR : (K : ℝ) < (N : ℝ) := by exact_mod_cast hKN
  have hratioPos : 0 < ((N : ℝ) - (K : ℝ)) / (K : ℝ) := by positivity
  have hExpL : Real.exp (oneLogIncrement N K) =
      ((N : ℝ) - (K : ℝ)) / (K : ℝ) := by
    unfold oneLogIncrement
    exact Real.exp_log hratioPos
  have hexpLe : Real.exp t ≤ ((N : ℝ) - (K : ℝ)) / (K : ℝ) := by
    rw [← hExpL]
    exact Real.exp_le_exp.mpr ht
  have hfactor : (K : ℝ) * Real.exp t ≤ (N : ℝ) - (K : ℝ) := by
    rw [le_div_iff₀ hKR] at hexpLe
    nlinarith
  rw [onePhiDeriv3_factor hK0 hKN]
  have hNK : 0 ≤ (N : ℝ) - (K : ℝ) := by linarith
  have hlast : 0 ≤ (N : ℝ) - (K : ℝ) - (K : ℝ) * Real.exp t := by linarith
  have hdenPow : 0 ≤ onePartition N K t ^ 3 :=
    pow_nonneg (onePartition_pos hK0 hKN t).le 3
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg hKR.le hNK) (Real.exp_pos t).le) hlast)
    hdenPow

noncomputable def oneError (N K : ℕ) (t : ℝ) : ℝ :=
  onePhi N K t -
    (((N : ℝ) - 2 * (K : ℝ)) /
      (4 * (N : ℝ) * oneLogIncrement N K)) * t ^ 2

noncomputable def oneErrorDeriv1 (N K : ℕ) (t : ℝ) : ℝ :=
  onePhiDeriv1 N K t -
    (((N : ℝ) - 2 * (K : ℝ)) /
      (2 * (N : ℝ) * oneLogIncrement N K)) * t

noncomputable def oneErrorDeriv2 (N K : ℕ) (t : ℝ) : ℝ :=
  onePhiDeriv2 N K t -
    (((N : ℝ) - 2 * (K : ℝ)) /
      (2 * (N : ℝ) * oneLogIncrement N K))

theorem hasDerivAt_oneError {N K : ℕ} (hK0 : 0 < K) (hKN : K < N) (t : ℝ) :
    HasDerivAt (oneError N K) (oneErrorDeriv1 N K t) t := by
  have hphi := hasDerivAt_onePhi hK0 hKN t
  have hquad := (hasDerivAt_pow 2 t).const_mul
    (((N : ℝ) - 2 * (K : ℝ)) /
      (4 * (N : ℝ) * oneLogIncrement N K))
  have htotal := hphi.fun_sub hquad
  change HasDerivAt
    (fun x : ℝ ↦ onePhi N K x -
      (((N : ℝ) - 2 * (K : ℝ)) /
        (4 * (N : ℝ) * oneLogIncrement N K)) * x ^ 2)
    (oneErrorDeriv1 N K t) t
  exact htotal.congr_deriv (by
    unfold oneErrorDeriv1
    ring)

theorem hasDerivAt_oneErrorDeriv1 {N K : ℕ} (hK0 : 0 < K) (hKN : K < N) (t : ℝ) :
    HasDerivAt (oneErrorDeriv1 N K) (oneErrorDeriv2 N K t) t := by
  have hphi := hasDerivAt_onePhiDeriv1 hK0 hKN t
  have hlin := (hasDerivAt_id t).const_mul
    (((N : ℝ) - 2 * (K : ℝ)) /
      (2 * (N : ℝ) * oneLogIncrement N K))
  have htotal := hphi.fun_sub hlin
  exact htotal.congr_deriv (by
    unfold oneErrorDeriv2
    ring)

theorem hasDerivAt_oneErrorDeriv2 {N K : ℕ} (hK0 : 0 < K) (hKN : K < N) (t : ℝ) :
    HasDerivAt (oneErrorDeriv2 N K) (onePhiDeriv3 N K t) t := by
  exact (hasDerivAt_onePhiDeriv2 hK0 hKN t).sub_const _

theorem oneErrorDeriv2_monotoneOn {N K : ℕ}
    (hK0 : 0 < K) (hKhalf : 2 * K < N) :
    MonotoneOn (oneErrorDeriv2 N K) (Set.Iic (oneLogIncrement N K)) := by
  have hKN : K < N := by omega
  apply monotoneOn_of_deriv_nonneg (convex_Iic _)
  · intro x hx
    exact (hasDerivAt_oneErrorDeriv2 hK0 hKN x).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_oneErrorDeriv2 hK0 hKN x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hasDerivAt_oneErrorDeriv2 hK0 hKN x).deriv]
    apply onePhiDeriv3_nonneg_before_midpoint hK0 hKhalf
    exact Set.mem_Iic.mp (interior_subset hx)

theorem oneErrorDeriv1_convexOn {N K : ℕ}
    (hK0 : 0 < K) (hKhalf : 2 * K < N) :
    ConvexOn ℝ (Set.Iic (oneLogIncrement N K)) (oneErrorDeriv1 N K) := by
  have hKN : K < N := by omega
  have hmono := oneErrorDeriv2_monotoneOn hK0 hKhalf
  have hderivMono : MonotoneOn (deriv (oneErrorDeriv1 N K))
      (interior (Set.Iic (oneLogIncrement N K))) := by
    intro x hx y hy hxy
    rw [(hasDerivAt_oneErrorDeriv1 hK0 hKN x).deriv,
      (hasDerivAt_oneErrorDeriv1 hK0 hKN y).deriv]
    exact hmono (interior_subset hx) (interior_subset hy) hxy
  apply hderivMono.convexOn_of_deriv (convex_Iic _)
  · intro x hx
    exact (hasDerivAt_oneErrorDeriv1 hK0 hKN x).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_oneErrorDeriv1 hK0 hKN x).differentiableAt.differentiableWithinAt

theorem onePhi_zero {N K : ℕ} (hKN : K ≤ N) (hN0 : 0 < N) :
    onePhi N K 0 = 0 := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN0)
  have hP0 : onePartition N K 0 = (N : ℝ) := by
    unfold onePartition
    norm_num
  unfold onePhi
  rw [hP0]
  norm_num

theorem oneError_zero {N K : ℕ} (hKN : K ≤ N) (hN0 : 0 < N) :
    oneError N K 0 = 0 := by
  unfold oneError
  rw [onePhi_zero hKN hN0]
  norm_num

theorem oneErrorDeriv1_zero {N K : ℕ} (hK0 : 0 < K) (hKN : K < N) :
    oneErrorDeriv1 N K 0 = 0 := by
  have hN0 : 0 < N := hK0.trans hKN
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN0)
  have hP0 : onePartition N K 0 = (N : ℝ) := by
    unfold onePartition
    norm_num
  have hP10 : onePartitionDeriv K 0 = (K : ℝ) := by
    unfold onePartitionDeriv
    norm_num
  unfold oneErrorDeriv1 onePhiDeriv1
  rw [hP0, hP10]
  norm_num

theorem oneErrorDeriv1_midpoint {N K : ℕ}
    (hK0 : 0 < K) (hKhalf : 2 * K < N) :
    oneErrorDeriv1 N K (oneLogIncrement N K) = 0 := by
  let L := oneLogIncrement N K
  have hKN : K < N := by omega
  have hN0 : 0 < N := hK0.trans hKN
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN0)
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK0)
  have hKNR : (K : ℝ) < (N : ℝ) := by exact_mod_cast hKN
  have hratioPos : 0 < ((N : ℝ) - (K : ℝ)) / (K : ℝ) := by positivity
  have hLpos : 0 < L := by
    dsimp [L]
    exact oneLogIncrement_pos hK0 hKhalf
  have hExpL : Real.exp L = ((N : ℝ) - (K : ℝ)) / (K : ℝ) := by
    dsimp [L, oneLogIncrement]
    exact Real.exp_log hratioPos
  have hP1 : onePartitionDeriv K L = (N : ℝ) - (K : ℝ) := by
    unfold onePartitionDeriv
    rw [hExpL]
    field_simp [hKR]
  have hP : onePartition N K L = 2 * ((N : ℝ) - (K : ℝ)) := by
    unfold onePartition
    rw [hExpL]
    field_simp [hKR]
    ring
  have hNKne : (N : ℝ) - (K : ℝ) ≠ 0 := by linarith
  have hLogne : oneLogIncrement N K ≠ 0 := by
    simpa [L] using ne_of_gt hLpos
  unfold oneErrorDeriv1 onePhiDeriv1
  rw [hP1, hP]
  field_simp [hNne, hNKne, hLogne]
  simp

theorem oneErrorDeriv1_nonpos_between {N K : ℕ}
    (hK0 : 0 < K) (hKhalf : 2 * K < N) {t : ℝ}
    (ht0 : 0 ≤ t) (htL : t ≤ oneLogIncrement N K) :
    oneErrorDeriv1 N K t ≤ 0 := by
  let L := oneLogIncrement N K
  have hLpos : 0 < L := by dsimp [L]; exact oneLogIncrement_pos hK0 hKhalf
  have hconv := oneErrorDeriv1_convexOn hK0 hKhalf
  have hseg : t ∈ segment ℝ (0 : ℝ) L := by
    rw [segment_eq_uIcc, Set.mem_uIcc]
    exact Or.inl ⟨ht0, htL⟩
  have hle := hconv.le_on_segment
    (show (0 : ℝ) ∈ Set.Iic L by exact hLpos.le)
    (Set.mem_Iic.mpr le_rfl) hseg
  have hKN : K < N := by omega
  rw [oneErrorDeriv1_zero hK0 hKN,
    show oneErrorDeriv1 N K L = 0 by
      simpa [L] using oneErrorDeriv1_midpoint hK0 hKhalf] at hle
  simpa using hle

theorem oneErrorDeriv1_nonneg_of_nonpos {N K : ℕ}
    (hK0 : 0 < K) (hKhalf : 2 * K < N) {t : ℝ} (ht : t ≤ 0) :
    0 ≤ oneErrorDeriv1 N K t := by
  have hKN : K < N := by omega
  rcases ht.eq_or_lt with rfl | htlt
  · rw [oneErrorDeriv1_zero hK0 hKN]
  · let L := oneLogIncrement N K
    let lam := L / (L - t)
    let mu := -t / (L - t)
    have hLpos : 0 < L := by dsimp [L]; exact oneLogIncrement_pos hK0 hKhalf
    have hden : 0 < L - t := by linarith
    have hlam : 0 < lam := div_pos hLpos hden
    have hmu : 0 ≤ mu := by
      dsimp [mu]
      exact div_nonneg (neg_nonneg.mpr ht) hden.le
    have hsum : lam + mu = 1 := by
      dsimp [lam, mu]
      field_simp [ne_of_gt hden]
      ring
    have hcombo : lam • t + mu • L = (0 : ℝ) := by
      simp only [smul_eq_mul]
      dsimp [lam, mu]
      field_simp [ne_of_gt hden]
      ring
    have hconv := oneErrorDeriv1_convexOn hK0 hKhalf
    have hineq := hconv.2
      (show t ∈ Set.Iic L by exact le_trans ht hLpos.le)
      (Set.mem_Iic.mpr le_rfl) hlam.le hmu hsum
    rw [hcombo, oneErrorDeriv1_zero hK0 hKN,
      show oneErrorDeriv1 N K L = 0 by
        simpa [L] using oneErrorDeriv1_midpoint hK0 hKhalf] at hineq
    simp only [smul_eq_mul, mul_zero, add_zero] at hineq
    exact (mul_nonneg_iff_of_pos_left hlam).mp hineq

theorem oneError_nonpos_before_midpoint {N K : ℕ}
    (hK0 : 0 < K) (hKhalf : 2 * K < N) {t : ℝ}
    (ht : t ≤ oneLogIncrement N K) : oneError N K t ≤ 0 := by
  have hKN : K < N := by omega
  have hN0 : 0 < N := hK0.trans hKN
  rcases le_total t 0 with ht0 | h0t
  · have hmono : MonotoneOn (oneError N K) (Set.Iic 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
      · intro x hx
        exact (hasDerivAt_oneError hK0 hKN x).continuousAt.continuousWithinAt
      · intro x hx
        exact (hasDerivAt_oneError hK0 hKN x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hasDerivAt_oneError hK0 hKN x).deriv]
        exact oneErrorDeriv1_nonneg_of_nonpos hK0 hKhalf
          (Set.mem_Iic.mp (interior_subset hx))
    have hle := hmono (show t ∈ Set.Iic (0 : ℝ) by exact ht0)
      (Set.mem_Iic.mpr le_rfl) ht0
    rw [oneError_zero (Nat.le_of_lt hKN) hN0] at hle
    exact hle
  · have hanti : AntitoneOn (oneError N K)
        (Set.Icc 0 (oneLogIncrement N K)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · intro x hx
        exact (hasDerivAt_oneError hK0 hKN x).continuousAt.continuousWithinAt
      · intro x hx
        exact (hasDerivAt_oneError hK0 hKN x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hasDerivAt_oneError hK0 hKN x).deriv]
        have hx' : x ∈ Set.Icc (0 : ℝ) (oneLogIncrement N K) := interior_subset hx
        exact oneErrorDeriv1_nonpos_between hK0 hKhalf hx'.1 hx'.2
    have hL0 : 0 ≤ oneLogIncrement N K := (oneLogIncrement_pos hK0 hKhalf).le
    have hle := hanti ⟨le_rfl, hL0⟩ ⟨h0t, ht⟩ h0t
    rw [oneError_zero (Nat.le_of_lt hKN) hN0] at hle
    exact hle

theorem onePartition_reflect {N K : ℕ}
    (hK0 : 0 < K) (hKhalf : 2 * K < N) (t : ℝ) :
    onePartition N K (2 * oneLogIncrement N K - t) =
      Real.exp (oneLogIncrement N K - t) * onePartition N K t := by
  let L := oneLogIncrement N K
  have hKN : K < N := by omega
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK0)
  have hKNR : (K : ℝ) < (N : ℝ) := by exact_mod_cast hKN
  have hNKne : (N : ℝ) - (K : ℝ) ≠ 0 := by linarith
  have hratioPos : 0 < ((N : ℝ) - (K : ℝ)) / (K : ℝ) := by positivity
  have hExpL : Real.exp L = ((N : ℝ) - (K : ℝ)) / (K : ℝ) := by
    dsimp [L, oneLogIncrement]
    exact Real.exp_log hratioPos
  have hExpT : Real.exp t ≠ 0 := Real.exp_ne_zero t
  have hExpLeft : Real.exp (2 * L - t) =
      (((N : ℝ) - (K : ℝ)) / (K : ℝ)) ^ 2 / Real.exp t := by
    rw [Real.exp_sub, show Real.exp (2 * L) = Real.exp L ^ 2 by
      rw [show 2 * L = L + L by ring, Real.exp_add, pow_two], hExpL]
  have hExpFactor : Real.exp (L - t) =
      (((N : ℝ) - (K : ℝ)) / (K : ℝ)) / Real.exp t := by
    rw [Real.exp_sub, hExpL]
  dsimp [L] at hExpLeft hExpFactor ⊢
  unfold onePartition
  rw [hExpLeft, hExpFactor]
  field_simp [hKR, hNKne, hExpT]
  ring

theorem onePhi_reflect {N K : ℕ}
    (hK0 : 0 < K) (hKhalf : 2 * K < N) (t : ℝ) :
    onePhi N K (2 * oneLogIncrement N K - t) =
      onePhi N K t +
        (((N : ℝ) - 2 * (K : ℝ)) / (N : ℝ)) *
          (oneLogIncrement N K - t) := by
  have hKN : K < N := by omega
  have hN0 : 0 < N := hK0.trans hKN
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN0)
  have hPne : onePartition N K t ≠ 0 := ne_of_gt (onePartition_pos hK0 hKN t)
  unfold onePhi
  rw [onePartition_reflect hK0 hKhalf,
    Real.log_mul (Real.exp_ne_zero _) hPne, Real.log_exp]
  field_simp [hNne]
  ring

theorem oneError_reflect {N K : ℕ}
    (hK0 : 0 < K) (hKhalf : 2 * K < N) (t : ℝ) :
    oneError N K (2 * oneLogIncrement N K - t) = oneError N K t := by
  have hKN : K < N := by omega
  have hN0 : 0 < N := hK0.trans hKN
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN0)
  have hLne : oneLogIncrement N K ≠ 0 := ne_of_gt (oneLogIncrement_pos hK0 hKhalf)
  unfold oneError
  rw [onePhi_reflect hK0 hKhalf]
  field_simp [hNne, hLne]
  ring

/-- Self-contained Kearns--Saul logarithmic inequality for a Bernoulli grid
point strictly below one half. -/
theorem onePhi_le_exact {N K : ℕ}
    (hK0 : 0 < K) (hKhalf : 2 * K < N) (t : ℝ) :
    onePhi N K t ≤
      (((N : ℝ) - 2 * (K : ℝ)) /
        (4 * (N : ℝ) * oneLogIncrement N K)) * t ^ 2 := by
  have herror : oneError N K t ≤ 0 := by
    rcases le_total t (oneLogIncrement N K) with ht | ht
    · exact oneError_nonpos_before_midpoint hK0 hKhalf ht
    · rw [← oneError_reflect hK0 hKhalf t]
      apply oneError_nonpos_before_midpoint hK0 hKhalf
      linarith
  unfold oneError at herror
  linarith

theorem deriv_scaledOddLog_nonpos_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv scaledOddLog x ≤ 0 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 ≤ (1 : ℝ) / x := by positivity
  have hy1 : (1 : ℝ) / x < 1 := by
    rw [div_lt_one hx0]
    exact hx
  have hhalf := Real.log_div_le_sum_range_add hy0 hy1 0
  norm_num at hhalf
  have hden : 0 < x ^ 2 - 1 := by nlinarith
  have hright : ((1 : ℝ) / x) / (1 - ((1 : ℝ) / x) ^ 2) =
      x / (x ^ 2 - 1) := by
    field_simp [ne_of_gt hx0, ne_of_gt hden]
  have hx1ne : x - 1 ≠ 0 := by linarith
  have hratio : ((1 + (1 : ℝ) / x) / (1 - (1 : ℝ) / x)) =
      (x + 1) / (x - 1) := by
    field_simp [ne_of_gt hx0, hx1ne]
  have hratio' : (1 + x⁻¹) / (1 - x⁻¹) = (x + 1) / (x - 1) := by
    simpa only [one_div] using hratio
  have hright' : x⁻¹ / (1 - (x ^ 2)⁻¹) = x / (x ^ 2 - 1) := by
    rw [← inv_pow]
    simpa only [one_div] using hright
  rw [hratio', hright'] at hhalf
  rw [(hasDerivAt_scaledOddLog hx).deriv]
  calc
    Real.log ((x + 1) / (x - 1)) - 2 * x / (x ^ 2 - 1) =
        2 * (1 / 2 * Real.log ((x + 1) / (x - 1))) -
          2 * (x / (x ^ 2 - 1)) := by ring
    _ ≤ 0 := by nlinarith

theorem scaledOddLog_antitoneOn_Ioi_one :
    AntitoneOn scaledOddLog (Set.Ioi 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 1)
  · intro x hx
    exact (hasDerivAt_scaledOddLog (Set.mem_Ioi.mp hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioi (1 : ℝ) := interior_subset hx
    exact (hasDerivAt_scaledOddLog (Set.mem_Ioi.mp hx')).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioi (1 : ℝ) := interior_subset hx
    exact deriv_scaledOddLog_nonpos_of_one_lt (Set.mem_Ioi.mp hx')

theorem oneLogIncrement_eq_scaled {N K : ℕ}
    (hK0 : 0 < K) (hKhalf : 2 * K < N) :
    oneLogIncrement N K =
      Real.log ((((N : ℝ) / ((N : ℝ) - 2 * (K : ℝ))) + 1) /
        (((N : ℝ) / ((N : ℝ) - 2 * (K : ℝ))) - 1)) := by
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK0)
  have hhalfR : 2 * (K : ℝ) < (N : ℝ) := by exact_mod_cast hKhalf
  have hdne : (N : ℝ) - 2 * (K : ℝ) ≠ 0 := by linarith
  have hdpos : 0 < (N : ℝ) - 2 * (K : ℝ) := by linarith
  have hxgt : 1 < (N : ℝ) / ((N : ℝ) - 2 * (K : ℝ)) := by
    rw [one_lt_div hdpos]
    have hKRpos : 0 < (K : ℝ) := by exact_mod_cast hK0
    linarith
  have hxminus : (N : ℝ) / ((N : ℝ) - 2 * (K : ℝ)) - 1 ≠ 0 := by
    linarith
  have hxminus' : (-1 : ℝ) + (N : ℝ) *
      ((N : ℝ) - 2 * (K : ℝ))⁻¹ ≠ 0 := by
    rw [show (-1 : ℝ) + (N : ℝ) *
      ((N : ℝ) - 2 * (K : ℝ))⁻¹ =
        (N : ℝ) / ((N : ℝ) - 2 * (K : ℝ)) - 1 by
      rw [div_eq_mul_inv]
      ring]
    exact hxminus
  have hdne' : (N : ℝ) - (K : ℝ) * 2 ≠ 0 := by linarith
  have hxminus'' : (-1 : ℝ) + (N : ℝ) *
      ((N : ℝ) - (K : ℝ) * 2)⁻¹ ≠ 0 := by
    have hden' : 0 < (N : ℝ) - (K : ℝ) * 2 := by linarith
    have : 1 < (N : ℝ) / ((N : ℝ) - (K : ℝ) * 2) := by
      rw [one_lt_div hden']
      have hKRpos : 0 < (K : ℝ) := by exact_mod_cast hK0
      linarith
    rw [show (-1 : ℝ) + (N : ℝ) *
      ((N : ℝ) - (K : ℝ) * 2)⁻¹ =
        (N : ℝ) / ((N : ℝ) - (K : ℝ) * 2) - 1 by
      rw [div_eq_mul_inv]
      ring]
    linarith
  unfold oneLogIncrement
  congr 1
  field_simp [hKR, hdne, hdne', hxminus, hxminus', hxminus'']
  ring

theorem oddGrid_log_comparison {N K : ℕ}
    (hN : 3 ≤ N) (hK0 : 0 < K) (hKhalf : 2 * K < N) :
    ((N : ℝ) - 2 * (K : ℝ)) * oddLogIncrement N ≤ oneLogIncrement N K := by
  let d : ℝ := (N : ℝ) - 2 * (K : ℝ)
  let x : ℝ := (N : ℝ) / d
  have hNr : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hhalfR : 2 * (K : ℝ) < (N : ℝ) := by exact_mod_cast hKhalf
  have hdpos : 0 < d := by dsimp [d]; linarith
  have hdOne : 1 ≤ d := by
    have hdNat : 1 ≤ N - 2 * K := by omega
    have hdCast : (1 : ℝ) ≤ ((N - 2 * K : ℕ) : ℝ) := by exact_mod_cast hdNat
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat] at hdCast
    exact hdCast
  have hKRpos : 0 < (K : ℝ) := by exact_mod_cast hK0
  have hdLtN : d < (N : ℝ) := by dsimp [d]; linarith
  have hx1 : 1 < x := by
    dsimp [x]
    rw [one_lt_div hdpos]
    exact hdLtN
  have hxN : x ≤ (N : ℝ) := by
    dsimp [x]
    rw [div_le_iff₀ hdpos]
    nlinarith
  have hNmem : (N : ℝ) ∈ Set.Ioi (1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hxmem : x ∈ Set.Ioi (1 : ℝ) := Set.mem_Ioi.mpr hx1
  have hanti := scaledOddLog_antitoneOn_Ioi_one hxmem hNmem hxN
  unfold scaledOddLog at hanti
  rw [show Real.log (((N : ℝ) + 1) / ((N : ℝ) - 1)) = oddLogIncrement N by
    rfl] at hanti
  rw [oneLogIncrement_eq_scaled hK0 hKhalf]
  change d * oddLogIncrement N ≤ _
  have hNrPos : 0 < (N : ℝ) := by linarith
  calc
    d * oddLogIncrement N =
        (d / (N : ℝ)) * ((N : ℝ) * oddLogIncrement N) := by
      field_simp [ne_of_gt hNrPos]
    _ ≤ (d / (N : ℝ)) *
        (x * Real.log ((x + 1) / (x - 1))) :=
      mul_le_mul_of_nonneg_left hanti (div_nonneg hdpos.le hNrPos.le)
    _ = Real.log ((x + 1) / (x - 1)) := by
      dsimp [x]
      field_simp [ne_of_gt hdpos, ne_of_gt hNrPos]

theorem oddProxyScale_one_div_two_eq {N : ℕ}
    (hN : 3 ≤ N) (hOdd : Odd N) :
    oddProxyScale N 1 / 2 = 1 / (4 * (N : ℝ) * oddLogIncrement N) := by
  have hnotEven : ¬Even N := Nat.not_even_iff_odd.mpr hOdd
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hlog : oddLogIncrement N ≠ 0 := ne_of_gt (oddLogIncrement_pos (by omega))
  unfold oddProxyScale
  rw [SharpSerfling.kappa_of_not_even hnotEven]
  unfold oddLogIncrement at hlog ⊢
  norm_num only [Nat.cast_one]
  field_simp [hNr, hN1, hlog]

theorem one_exact_scale_le_oddProxy {N K : ℕ}
    (hN : 3 ≤ N) (hOdd : Odd N) (hK0 : 0 < K) (hKhalf : 2 * K < N) :
    ((N : ℝ) - 2 * (K : ℝ)) /
        (4 * (N : ℝ) * oneLogIncrement N K) ≤ oddProxyScale N 1 / 2 := by
  have hNr : 0 < (N : ℝ) := by positivity
  have hd : 0 < (N : ℝ) - 2 * (K : ℝ) := by
    have hcast : 2 * (K : ℝ) < (N : ℝ) := by exact_mod_cast hKhalf
    linarith
  have hL : 0 < oneLogIncrement N K := oneLogIncrement_pos hK0 hKhalf
  have hLN : 0 < oddLogIncrement N := oddLogIncrement_pos (by omega)
  have hcomp := oddGrid_log_comparison hN hK0 hKhalf
  rw [oddProxyScale_one_div_two_eq hN hOdd]
  rw [div_le_div_iff₀ (by positivity : 0 < 4 * (N : ℝ) * oneLogIncrement N K)
    (by positivity : 0 < 4 * (N : ℝ) * oddLogIncrement N)]
  nlinarith

theorem binomialMgf_one_expansion {N K : ℕ}
    (hN : 1 ≤ N) (hK : K ≤ N) (t : ℝ) :
    binomialMgf N K 1 t =
      (N : ℝ)⁻¹ *
        (((N : ℝ) - (K : ℝ)) * Real.exp (t * (0 - center N K 1)) +
          (K : ℝ) * Real.exp (t * (1 - center N K 1))) := by
  unfold binomialMgf binomialAverage binomialSum
  rw [show antidiagonal 1 = {(0, 1), (1, 0)} by decide]
  simp [hypergeomWeight]
  rw [Nat.cast_sub hK]
  norm_num

theorem mgf_one_eq_partition {N K : ℕ}
    (hN : 1 ≤ N) (hK : K ≤ N) (t : ℝ) :
    mgf N K 1 t =
      Real.exp (-((K : ℝ) / (N : ℝ)) * t) * onePartition N K t / (N : ℝ) := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [mgf_eq_binomialMgf hK, binomialMgf_one_expansion hN hK]
  have hcenter : center N K 1 = (K : ℝ) / (N : ℝ) := by
    unfold center
    norm_num
  rw [hcenter]
  have h0 : Real.exp (t * (0 - (K : ℝ) / (N : ℝ))) =
      Real.exp (-((K : ℝ) / (N : ℝ)) * t) := by
    congr 1
    ring
  have h1 : Real.exp (t * (1 - (K : ℝ) / (N : ℝ))) =
      Real.exp (-((K : ℝ) / (N : ℝ)) * t) * Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    field_simp [hNne]
    ring
  rw [h0, h1]
  unfold onePartition
  field_simp [hNne]

theorem log_mgf_one_eq_phi {N K : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (t : ℝ) :
    Real.log (mgf N K 1 t) = onePhi N K t := by
  have hN0 : 0 < N := hK0.trans hKN
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN0)
  have hPne : onePartition N K t ≠ 0 := ne_of_gt (onePartition_pos hK0 hKN t)
  rw [mgf_one_eq_partition (by omega) (Nat.le_of_lt hKN)]
  rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero _) hPne) hNne,
    Real.log_mul (Real.exp_ne_zero _) hPne, Real.log_exp]
  unfold onePhi
  ring

theorem log_mgf_one_le_exact {N K : ℕ}
    (hK0 : 0 < K) (hKhalf : 2 * K < N) (t : ℝ) :
    Real.log (mgf N K 1 t) ≤
      (((N : ℝ) - 2 * (K : ℝ)) /
        (4 * (N : ℝ) * oneLogIncrement N K)) * t ^ 2 := by
  rw [log_mgf_one_eq_phi hK0 (by omega)]
  exact onePhi_le_exact hK0 hKhalf t

theorem mgf_one_le_oddProxy_of_lower {N K : ℕ}
    (hN : 3 ≤ N) (hOdd : Odd N) (hK0 : 0 < K) (hKhalf : 2 * K < N) (t : ℝ) :
    mgf N K 1 t ≤ Real.exp (oddProxyScale N 1 * t ^ 2 / 2) := by
  apply (Real.log_le_iff_le_exp (mgf_pos (by omega) t)).mp
  have hexact := log_mgf_one_le_exact hK0 hKhalf t
  have hscale := one_exact_scale_le_oddProxy hN hOdd hK0 hKhalf
  have hmul := mul_le_mul_of_nonneg_right hscale (sq_nonneg t)
  calc
    Real.log (mgf N K 1 t) ≤
        (((N : ℝ) - 2 * (K : ℝ)) /
          (4 * (N : ℝ) * oneLogIncrement N K)) * t ^ 2 := hexact
    _ ≤ (oddProxyScale N 1 / 2) * t ^ 2 := hmul
    _ = oddProxyScale N 1 * t ^ 2 / 2 := by ring

/-- Fully internal Kearns--Saul one-draw base on the odd population grid. -/
theorem mgf_one_le_oddProxy {N K : ℕ}
    (hN : 3 ≤ N) (hOdd : Odd N) (hK : K ≤ N) (t : ℝ) :
    mgf N K 1 t ≤ Real.exp (oddProxyScale N 1 * t ^ 2 / 2) := by
  by_cases hK0eq : K = 0
  · subst K
    rw [mgf_zeroSuccesses (by omega)]
    apply Real.one_le_exp
    exact div_nonneg
      (mul_nonneg (oddProxyScale_pos (by omega) (by omega) (by omega)).le (sq_nonneg t))
      (by norm_num)
  by_cases hKNeq : K = N
  · subst K
    rw [mgf_allSuccesses (by omega) (by omega)]
    apply Real.one_le_exp
    exact div_nonneg
      (mul_nonneg (oddProxyScale_pos (by omega) (by omega) (by omega)).le (sq_nonneg t))
      (by norm_num)
  have hK0 : 0 < K := Nat.pos_of_ne_zero hK0eq
  have hKN : K < N := lt_of_le_of_ne hK hKNeq
  by_cases hLower : 2 * K < N
  · exact mgf_one_le_oddProxy_of_lower hN hOdd hK0 hLower t
  · have hneq : 2 * K ≠ N := by
      intro heq
      obtain ⟨q, hq⟩ := hOdd
      omega
    have hUpper : N < 2 * K := by omega
    have hcomp0 : 0 < N - K := Nat.sub_pos_of_lt hKN
    have hcompHalf : 2 * (N - K) < N := by omega
    have hbound := mgf_one_le_oddProxy_of_lower hN hOdd hcomp0 hcompHalf (-t)
    rw [mgf_successComplement (by omega) hK (-t)] at hbound
    simpa only [neg_neg, neg_sq] using hbound

/-- Complete sharp MGF theorem for odd population sizes. -/
theorem odd_mgf_le {N K m : ℕ} (hN : 3 ≤ N) (hOdd : Odd N)
    (hK : K ≤ N) (hm : m ≤ N) (t : ℝ) :
    mgf N K m t ≤ Real.exp (oddProxyScale N m * t ^ 2 / 2) := by
  exact odd_mgf_le_of_one_draw
    (fun hN hOdd hK ↦ mgf_one_le_oddProxy hN hOdd hK _) hN hOdd hK hm t

theorem sharp_mgf_of_odd {N K m : ℕ} (hN : 3 ≤ N) (hOdd : Odd N)
    (hK : K ≤ N) (hm : m ≤ N) (t : ℝ) :
    Real.log (mgf N K m t) ≤
      SharpSerfling.kappa N * SharpSerfling.hypergeomScale N m * t ^ 2 := by
  apply (Real.log_le_iff_le_exp (mgf_pos hm t)).2
  have hbound := odd_mgf_le hN hOdd hK hm t
  rw [oddProxyScale_eq_two_mul] at hbound
  convert hbound using 1 <;> ring

/-- Manuscript theorem `thm:hypergeom`, with all parity branches closed. -/
theorem sharp_mgf {N K m : ℕ} (hN : 2 ≤ N) (hK : K ≤ N)
    (hm : m ≤ N) (t : ℝ) :
    Real.log (mgf N K m t) ≤
      SharpSerfling.kappa N * SharpSerfling.hypergeomScale N m * t ^ 2 := by
  by_cases hEven : Even N
  · exact sharp_mgf_of_even hN hEven hK hm t
  · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
    have hN3 : 3 ≤ N := by
      obtain ⟨q, hq⟩ := hOdd
      omega
    exact sharp_mgf_of_odd hN3 hOdd hK hm t

theorem sharpMGFStatement : SharpMGFStatement := by
  intro N K m hN hK hm0 hm t
  exact sharp_mgf hN hK (by omega) t

end SharpSerfling.Hypergeometric
