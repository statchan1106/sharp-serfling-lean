import SharpSerfling.Hypergeometric.SharpInduction
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.Convex.Deriv

namespace SharpSerfling.Hypergeometric

open Finset Finset.Nat
open scoped BigOperators

noncomputable def centralTwoLogIncrement (N : ℕ) : ℝ :=
  Real.log (((N : ℝ) + 1) / ((N : ℝ) - 3))

theorem centralTwoLogIncrement_pos {N : ℕ} (hN : 5 ≤ N) :
    0 < centralTwoLogIncrement N := by
  unfold centralTwoLogIncrement
  apply Real.log_pos
  rw [one_lt_div]
  · linarith
  · have hNr : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith

noncomputable def scaledOddLog (x : ℝ) : ℝ :=
  x * Real.log ((x + 1) / (x - 1))

/-- Unnormalised probability generating polynomial of the central two-draw law,
evaluated at `exp t`. -/
noncomputable def centralTwoPartition (N : ℕ) (t : ℝ) : ℝ :=
  ((N : ℝ) - 3) * Real.exp (2 * t) +
    2 * ((N : ℝ) + 1) * Real.exp t + ((N : ℝ) + 1)

noncomputable def centralTwoPartitionDeriv1 (N : ℕ) (t : ℝ) : ℝ :=
  2 * ((N : ℝ) - 3) * Real.exp (2 * t) +
    2 * ((N : ℝ) + 1) * Real.exp t

noncomputable def centralTwoPartitionDeriv2 (N : ℕ) (t : ℝ) : ℝ :=
  4 * ((N : ℝ) - 3) * Real.exp (2 * t) +
    2 * ((N : ℝ) + 1) * Real.exp t

noncomputable def centralTwoPartitionDeriv3 (N : ℕ) (t : ℝ) : ℝ :=
  8 * ((N : ℝ) - 3) * Real.exp (2 * t) +
    2 * ((N : ℝ) + 1) * Real.exp t

theorem centralTwoPartition_pos {N : ℕ} (hN : 5 ≤ N) (t : ℝ) :
    0 < centralTwoPartition N t := by
  unfold centralTwoPartition
  have hNr : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) - 3 := by linarith
  have hC : 0 < (N : ℝ) + 1 := by linarith
  positivity

theorem hasDerivAt_centralTwoPartition (N : ℕ) (t : ℝ) :
    HasDerivAt (centralTwoPartition N) (centralTwoPartitionDeriv1 N t) t := by
  unfold centralTwoPartition centralTwoPartitionDeriv1
  have hA := ((hasDerivAt_id t).const_mul 2).exp.const_mul ((N : ℝ) - 3)
  have hB := (hasDerivAt_id t).exp.const_mul (2 * ((N : ℝ) + 1))
  have htotal := (hA.fun_add hB).add_const ((N : ℝ) + 1)
  simpa only [Pi.add_apply, id_eq] using htotal.congr_deriv (by
    simp only [id_eq]
    ring)

theorem hasDerivAt_centralTwoPartitionDeriv1 (N : ℕ) (t : ℝ) :
    HasDerivAt (centralTwoPartitionDeriv1 N) (centralTwoPartitionDeriv2 N t) t := by
  unfold centralTwoPartitionDeriv1 centralTwoPartitionDeriv2
  have hA := ((hasDerivAt_id t).const_mul 2).exp.const_mul
    (2 * ((N : ℝ) - 3))
  have hB := (hasDerivAt_id t).exp.const_mul (2 * ((N : ℝ) + 1))
  have htotal := hA.fun_add hB
  simpa only [Pi.add_apply, id_eq] using htotal.congr_deriv (by
    simp only [id_eq]
    ring)

theorem hasDerivAt_centralTwoPartitionDeriv2 (N : ℕ) (t : ℝ) :
    HasDerivAt (centralTwoPartitionDeriv2 N) (centralTwoPartitionDeriv3 N t) t := by
  unfold centralTwoPartitionDeriv2 centralTwoPartitionDeriv3
  have hA := ((hasDerivAt_id t).const_mul 2).exp.const_mul
    (4 * ((N : ℝ) - 3))
  have hB := (hasDerivAt_id t).exp.const_mul (2 * ((N : ℝ) + 1))
  have htotal := hA.fun_add hB
  simpa only [Pi.add_apply, id_eq] using htotal.congr_deriv (by
    simp only [id_eq]
    ring)

/-- Log-MGF of the explicit central two-draw law, written through its
unnormalised generating polynomial. -/
noncomputable def centralTwoPhi (N : ℕ) (t : ℝ) : ℝ :=
  -(((N : ℝ) - 1) / (N : ℝ)) * t +
    Real.log (centralTwoPartition N t) - Real.log (4 * (N : ℝ))

noncomputable def centralTwoPhiDeriv1 (N : ℕ) (t : ℝ) : ℝ :=
  centralTwoPartitionDeriv1 N t / centralTwoPartition N t -
    ((N : ℝ) - 1) / (N : ℝ)

noncomputable def centralTwoPhiDeriv2 (N : ℕ) (t : ℝ) : ℝ :=
  centralTwoPartitionDeriv2 N t / centralTwoPartition N t -
    (centralTwoPartitionDeriv1 N t / centralTwoPartition N t) *
      (centralTwoPartitionDeriv1 N t / centralTwoPartition N t)

noncomputable def centralTwoPhiDeriv3 (N : ℕ) (t : ℝ) : ℝ :=
  centralTwoPartitionDeriv3 N t / centralTwoPartition N t -
    3 * centralTwoPartitionDeriv1 N t * centralTwoPartitionDeriv2 N t /
      centralTwoPartition N t ^ 2 +
    2 * centralTwoPartitionDeriv1 N t ^ 3 / centralTwoPartition N t ^ 3

theorem hasDerivAt_centralTwoPhi {N : ℕ} (hN : 5 ≤ N) (t : ℝ) :
    HasDerivAt (centralTwoPhi N) (centralTwoPhiDeriv1 N t) t := by
  have hP := hasDerivAt_centralTwoPartition N t
  have hPne : centralTwoPartition N t ≠ 0 := ne_of_gt (centralTwoPartition_pos hN t)
  have hlin := (hasDerivAt_id t).const_mul
    (-(((N : ℝ) - 1) / (N : ℝ)))
  have htotal := (hlin.fun_add (hP.log hPne)).sub_const (Real.log (4 * (N : ℝ)))
  change HasDerivAt
    (fun x : ℝ ↦ -(((N : ℝ) - 1) / (N : ℝ)) * x +
      Real.log (centralTwoPartition N x) - Real.log (4 * (N : ℝ)))
    (centralTwoPartitionDeriv1 N t / centralTwoPartition N t -
      ((N : ℝ) - 1) / (N : ℝ)) t
  exact htotal.congr_deriv (by ring)

theorem hasDerivAt_centralTwoPhiDeriv1 {N : ℕ} (hN : 5 ≤ N) (t : ℝ) :
    HasDerivAt (centralTwoPhiDeriv1 N) (centralTwoPhiDeriv2 N t) t := by
  have hP := hasDerivAt_centralTwoPartition N t
  have hP1 := hasDerivAt_centralTwoPartitionDeriv1 N t
  have hPne : centralTwoPartition N t ≠ 0 := ne_of_gt (centralTwoPartition_pos hN t)
  have hratio := hP1.fun_div hP hPne
  have htotal := hratio.add_const (-(((N : ℝ) - 1) / (N : ℝ)))
  have heq :
      (centralTwoPartitionDeriv2 N t * centralTwoPartition N t -
          centralTwoPartitionDeriv1 N t * centralTwoPartitionDeriv1 N t) /
            centralTwoPartition N t ^ 2 = centralTwoPhiDeriv2 N t := by
    unfold centralTwoPhiDeriv2
    field_simp [hPne]
  change HasDerivAt
    (fun x : ℝ ↦ centralTwoPartitionDeriv1 N x / centralTwoPartition N x -
      ((N : ℝ) - 1) / (N : ℝ))
    (centralTwoPhiDeriv2 N t) t
  exact htotal.congr_deriv heq

theorem hasDerivAt_centralTwoPhiDeriv2 {N : ℕ} (hN : 5 ≤ N) (t : ℝ) :
    HasDerivAt (centralTwoPhiDeriv2 N) (centralTwoPhiDeriv3 N t) t := by
  have hP := hasDerivAt_centralTwoPartition N t
  have hP1 := hasDerivAt_centralTwoPartitionDeriv1 N t
  have hP2 := hasDerivAt_centralTwoPartitionDeriv2 N t
  have hPne : centralTwoPartition N t ≠ 0 := ne_of_gt (centralTwoPartition_pos hN t)
  have hr1 := hP1.fun_div hP hPne
  have hr2 := hP2.fun_div hP hPne
  have hsquare := hr1.fun_mul hr1
  have htotal := hr2.fun_sub hsquare
  have heq :
      (centralTwoPartitionDeriv3 N t * centralTwoPartition N t -
          centralTwoPartitionDeriv2 N t * centralTwoPartitionDeriv1 N t) /
            centralTwoPartition N t ^ 2 -
        (((centralTwoPartitionDeriv2 N t * centralTwoPartition N t -
              centralTwoPartitionDeriv1 N t * centralTwoPartitionDeriv1 N t) /
                centralTwoPartition N t ^ 2) *
              (centralTwoPartitionDeriv1 N t / centralTwoPartition N t) +
          (centralTwoPartitionDeriv1 N t / centralTwoPartition N t) *
            ((centralTwoPartitionDeriv2 N t * centralTwoPartition N t -
                centralTwoPartitionDeriv1 N t * centralTwoPartitionDeriv1 N t) /
                  centralTwoPartition N t ^ 2)) = centralTwoPhiDeriv3 N t := by
    unfold centralTwoPhiDeriv3
    field_simp [hPne]
    ring
  change HasDerivAt
    (fun x : ℝ ↦ centralTwoPartitionDeriv2 N x / centralTwoPartition N x -
      (centralTwoPartitionDeriv1 N x / centralTwoPartition N x) *
        (centralTwoPartitionDeriv1 N x / centralTwoPartition N x))
    (centralTwoPhiDeriv3 N t) t
  exact htotal.congr_deriv heq

noncomputable def centralTwoQ (N : ℕ) (z : ℝ) : ℝ :=
  ((N : ℝ) - 3) * z ^ 2 + (2 * (N : ℝ) - 14) * z + ((N : ℝ) + 1)

theorem centralTwoQ_pos {N : ℕ} (hN : 5 ≤ N) (hOdd : Odd N) {z : ℝ}
    (hz : 0 < z) : 0 < centralTwoQ N z := by
  rcases eq_or_lt_of_le hN with rfl | hNgt
  · norm_num [centralTwoQ]
    nlinarith [sq_nonneg (z - 1)]
  · have hN7 : 7 ≤ N := by
      have : N ≠ 6 := by
        intro h
        subst N
        obtain ⟨q, hq⟩ := hOdd
        omega
      omega
    have hNr : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN7
    unfold centralTwoQ
    have hA : 0 ≤ (N : ℝ) - 3 := by linarith
    have hB : 0 ≤ 2 * (N : ℝ) - 14 := by linarith
    have hC : 0 < (N : ℝ) + 1 := by linarith
    positivity

/-- The exact factorisation of the third derivative used in the manuscript's
central `m = 2` argument. -/
theorem centralTwoPhiDeriv3_factor {N : ℕ} (hN : 5 ≤ N) (t : ℝ) :
    centralTwoPhiDeriv3 N t =
      -(2 * Real.exp t * ((N : ℝ) + 1) *
          (((N : ℝ) - 3) * Real.exp t ^ 2 - ((N : ℝ) + 1)) *
            centralTwoQ N (Real.exp t) /
          centralTwoPartition N t ^ 3) := by
  have hPne : centralTwoPartition N t ≠ 0 := ne_of_gt (centralTwoPartition_pos hN t)
  have hexp : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold centralTwoPhiDeriv3 centralTwoPartitionDeriv1
    centralTwoPartitionDeriv2 centralTwoPartitionDeriv3 centralTwoPartition centralTwoQ
  rw [hexp]
  field_simp [hPne]
  ring

theorem centralTwoPhiDeriv3_nonneg_before_midpoint
    {N : ℕ} (hN : 5 ≤ N) (hOdd : Odd N) {t : ℝ}
    (ht : t ≤ centralTwoLogIncrement N / 2) :
    0 ≤ centralTwoPhiDeriv3 N t := by
  have hNr : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) - 3 := by linarith
  have hratioPos : 0 < ((N : ℝ) + 1) / ((N : ℝ) - 3) := by positivity
  have hexpL : Real.exp (centralTwoLogIncrement N) =
      ((N : ℝ) + 1) / ((N : ℝ) - 3) := by
    unfold centralTwoLogIncrement
    exact Real.exp_log hratioPos
  have htwoT : 2 * t ≤ centralTwoLogIncrement N := by linarith
  have hexpLe : Real.exp (2 * t) ≤
      ((N : ℝ) + 1) / ((N : ℝ) - 3) := by
    rw [← hexpL]
    exact Real.exp_le_exp.mpr htwoT
  have hexpSq : Real.exp t ^ 2 = Real.exp (2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hfactor : ((N : ℝ) - 3) * Real.exp t ^ 2 - ((N : ℝ) + 1) ≤ 0 := by
    rw [hexpSq]
    rw [le_div_iff₀ hden] at hexpLe
    linarith
  have hQ : 0 < centralTwoQ N (Real.exp t) :=
    centralTwoQ_pos hN hOdd (Real.exp_pos t)
  have hP : 0 < centralTwoPartition N t := centralTwoPartition_pos hN t
  rw [centralTwoPhiDeriv3_factor hN]
  have hnum : 2 * Real.exp t * ((N : ℝ) + 1) *
      (((N : ℝ) - 3) * Real.exp t ^ 2 - ((N : ℝ) + 1)) *
        centralTwoQ N (Real.exp t) ≤ 0 := by
    have hpref : 0 ≤ 2 * Real.exp t * ((N : ℝ) + 1) := by positivity
    have hfirst : 2 * Real.exp t * ((N : ℝ) + 1) *
        (((N : ℝ) - 3) * Real.exp t ^ 2 - ((N : ℝ) + 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hpref hfactor
    exact mul_nonpos_of_nonpos_of_nonneg hfirst hQ.le
  exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hnum (by positivity))

noncomputable def centralTwoError (N : ℕ) (t : ℝ) : ℝ :=
  centralTwoPhi N t - t ^ 2 / ((N : ℝ) * centralTwoLogIncrement N)

noncomputable def centralTwoErrorDeriv1 (N : ℕ) (t : ℝ) : ℝ :=
  centralTwoPhiDeriv1 N t -
    (2 / ((N : ℝ) * centralTwoLogIncrement N)) * t

noncomputable def centralTwoErrorDeriv2 (N : ℕ) (t : ℝ) : ℝ :=
  centralTwoPhiDeriv2 N t -
    2 / ((N : ℝ) * centralTwoLogIncrement N)

theorem hasDerivAt_centralTwoError {N : ℕ} (hN : 5 ≤ N) (t : ℝ) :
    HasDerivAt (centralTwoError N) (centralTwoErrorDeriv1 N t) t := by
  have hphi := hasDerivAt_centralTwoPhi hN t
  have hquad := (hasDerivAt_pow 2 t).div_const
    ((N : ℝ) * centralTwoLogIncrement N)
  have htotal := hphi.fun_sub hquad
  change HasDerivAt
    (fun x : ℝ ↦ centralTwoPhi N x -
      x ^ 2 / ((N : ℝ) * centralTwoLogIncrement N))
    (centralTwoErrorDeriv1 N t) t
  exact htotal.congr_deriv (by
    unfold centralTwoErrorDeriv1
    ring)

theorem hasDerivAt_centralTwoErrorDeriv1 {N : ℕ} (hN : 5 ≤ N) (t : ℝ) :
    HasDerivAt (centralTwoErrorDeriv1 N) (centralTwoErrorDeriv2 N t) t := by
  have hphi := hasDerivAt_centralTwoPhiDeriv1 hN t
  have hlin := (hasDerivAt_id t).const_mul
    (2 / ((N : ℝ) * centralTwoLogIncrement N))
  have htotal := hphi.fun_sub hlin
  have heq : centralTwoPhiDeriv2 N t -
      (2 / ((N : ℝ) * centralTwoLogIncrement N)) * 1 =
        centralTwoErrorDeriv2 N t := by
    unfold centralTwoErrorDeriv2
    ring
  change HasDerivAt
    (fun x : ℝ ↦ centralTwoPhiDeriv1 N x -
      (2 / ((N : ℝ) * centralTwoLogIncrement N)) * x)
    (centralTwoErrorDeriv2 N t) t
  exact htotal.congr_deriv heq

theorem hasDerivAt_centralTwoErrorDeriv2 {N : ℕ} (hN : 5 ≤ N) (t : ℝ) :
    HasDerivAt (centralTwoErrorDeriv2 N) (centralTwoPhiDeriv3 N t) t := by
  have hphi := hasDerivAt_centralTwoPhiDeriv2 hN t
  have htotal := hphi.sub_const
    (2 / ((N : ℝ) * centralTwoLogIncrement N))
  exact htotal

theorem centralTwoErrorDeriv2_monotoneOn {N : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) :
    MonotoneOn (centralTwoErrorDeriv2 N)
      (Set.Iic (centralTwoLogIncrement N / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Iic _)
  · intro x hx
    exact (hasDerivAt_centralTwoErrorDeriv2 hN x).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_centralTwoErrorDeriv2 hN x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hasDerivAt_centralTwoErrorDeriv2 hN x).deriv]
    apply centralTwoPhiDeriv3_nonneg_before_midpoint hN hOdd
    have hx' : x ∈ Set.Iic (centralTwoLogIncrement N / 2) := interior_subset hx
    exact Set.mem_Iic.mp hx'

theorem centralTwoErrorDeriv1_convexOn {N : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) :
    ConvexOn ℝ (Set.Iic (centralTwoLogIncrement N / 2))
      (centralTwoErrorDeriv1 N) := by
  let a := centralTwoLogIncrement N / 2
  have hmono := centralTwoErrorDeriv2_monotoneOn hN hOdd
  have hderivMono : MonotoneOn (deriv (centralTwoErrorDeriv1 N))
      (interior (Set.Iic a)) := by
    intro x hx y hy hxy
    rw [(hasDerivAt_centralTwoErrorDeriv1 hN x).deriv,
      (hasDerivAt_centralTwoErrorDeriv1 hN y).deriv]
    exact hmono (interior_subset hx) (interior_subset hy) hxy
  apply hderivMono.convexOn_of_deriv (convex_Iic a)
  · intro x hx
    exact (hasDerivAt_centralTwoErrorDeriv1 hN x).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_centralTwoErrorDeriv1 hN x).differentiableAt.differentiableWithinAt

theorem centralTwoPhi_zero {N : ℕ} : centralTwoPhi N 0 = 0 := by
  have hP0 : centralTwoPartition N 0 = 4 * (N : ℝ) := by
    unfold centralTwoPartition
    norm_num
    ring
  unfold centralTwoPhi
  rw [hP0]
  ring

theorem centralTwoError_zero {N : ℕ} : centralTwoError N 0 = 0 := by
  unfold centralTwoError
  rw [centralTwoPhi_zero]
  norm_num

theorem centralTwoErrorDeriv1_zero {N : ℕ} (hN : 5 ≤ N) :
    centralTwoErrorDeriv1 N 0 = 0 := by
  have hNr : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  have hP0 : centralTwoPartition N 0 = 4 * (N : ℝ) := by
    unfold centralTwoPartition
    norm_num
    ring
  have hP10 : centralTwoPartitionDeriv1 N 0 = 4 * ((N : ℝ) - 1) := by
    unfold centralTwoPartitionDeriv1
    norm_num
    ring
  unfold centralTwoErrorDeriv1 centralTwoPhiDeriv1
  rw [hP0, hP10]
  norm_num
  field_simp [hNr]
  ring

theorem centralTwoErrorDeriv1_midpoint {N : ℕ} (hN : 5 ≤ N) :
    centralTwoErrorDeriv1 N (centralTwoLogIncrement N / 2) = 0 := by
  let L := centralTwoLogIncrement N
  let a := L / 2
  have hNr : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := by linarith
  have hden : 0 < (N : ℝ) - 3 := by linarith
  have hratioPos : 0 < ((N : ℝ) + 1) / ((N : ℝ) - 3) := by positivity
  have hLpos : 0 < L := by
    dsimp [L, centralTwoLogIncrement]
    apply Real.log_pos
    rw [one_lt_div hden]
    linarith
  have hexp : Real.exp (2 * a) =
      ((N : ℝ) + 1) / ((N : ℝ) - 3) := by
    have : 2 * a = L := by dsimp [a]; ring
    rw [this]
    dsimp [L, centralTwoLogIncrement]
    exact Real.exp_log hratioPos
  have hP1eq : centralTwoPartitionDeriv1 N a = centralTwoPartition N a := by
    unfold centralTwoPartitionDeriv1 centralTwoPartition
    rw [hexp]
    field_simp [ne_of_gt hden]
    ring
  have hPne : centralTwoPartition N a ≠ 0 :=
    ne_of_gt (centralTwoPartition_pos hN a)
  have hLne : centralTwoLogIncrement N ≠ 0 := ne_of_gt hLpos
  change centralTwoErrorDeriv1 N a = 0
  unfold centralTwoErrorDeriv1 centralTwoPhiDeriv1
  rw [hP1eq, div_self hPne]
  dsimp [a, L]
  field_simp [hNne, hLne]
  simp

theorem centralTwoErrorDeriv1_nonpos_between {N : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) {t : ℝ} (ht0 : 0 ≤ t)
    (htmid : t ≤ centralTwoLogIncrement N / 2) :
    centralTwoErrorDeriv1 N t ≤ 0 := by
  let a := centralTwoLogIncrement N / 2
  have hapos : 0 < a := by
    dsimp [a]
    exact half_pos (centralTwoLogIncrement_pos hN)
  have hconv := centralTwoErrorDeriv1_convexOn hN hOdd
  have hseg : t ∈ segment ℝ (0 : ℝ) a := by
    rw [segment_eq_uIcc, Set.mem_uIcc]
    exact Or.inl ⟨ht0, htmid⟩
  have hle := hconv.le_on_segment
    (show (0 : ℝ) ∈ Set.Iic a by exact hapos.le)
    (Set.mem_Iic.mpr le_rfl) hseg
  rw [centralTwoErrorDeriv1_zero hN,
    show centralTwoErrorDeriv1 N a = 0 by
      simpa [a] using centralTwoErrorDeriv1_midpoint hN] at hle
  simpa using hle

theorem centralTwoErrorDeriv1_nonneg_of_nonpos {N : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) {t : ℝ} (ht : t ≤ 0) :
    0 ≤ centralTwoErrorDeriv1 N t := by
  rcases ht.eq_or_lt with rfl | htlt
  · rw [centralTwoErrorDeriv1_zero hN]
  · let a := centralTwoLogIncrement N / 2
    let lam := a / (a - t)
    let mu := -t / (a - t)
    have hapos : 0 < a := by
      dsimp [a]
      exact half_pos (centralTwoLogIncrement_pos hN)
    have hden : 0 < a - t := by linarith
    have hlam : 0 < lam := div_pos hapos hden
    have hmu : 0 ≤ mu := by
      dsimp [mu]
      exact div_nonneg (neg_nonneg.mpr ht) hden.le
    have hsum : lam + mu = 1 := by
      dsimp [lam, mu]
      field_simp [ne_of_gt hden]
      ring
    have hcombo : lam • t + mu • a = (0 : ℝ) := by
      simp only [smul_eq_mul]
      dsimp [lam, mu]
      field_simp [ne_of_gt hden]
      ring
    have hconv := centralTwoErrorDeriv1_convexOn hN hOdd
    have hineq := hconv.2
      (show t ∈ Set.Iic a by exact le_trans ht hapos.le)
      (Set.mem_Iic.mpr le_rfl) hlam.le hmu hsum
    rw [hcombo, centralTwoErrorDeriv1_zero hN,
      show centralTwoErrorDeriv1 N a = 0 by
        simpa [a] using centralTwoErrorDeriv1_midpoint hN] at hineq
    simp only [smul_eq_mul, mul_zero, add_zero] at hineq
    exact (mul_nonneg_iff_of_pos_left hlam).mp hineq

theorem centralTwoError_nonpos_before_midpoint {N : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) {t : ℝ}
    (ht : t ≤ centralTwoLogIncrement N / 2) :
    centralTwoError N t ≤ 0 := by
  rcases le_total t 0 with ht0 | h0t
  · have hmono : MonotoneOn (centralTwoError N) (Set.Iic 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
      · intro x hx
        exact (hasDerivAt_centralTwoError hN x).continuousAt.continuousWithinAt
      · intro x hx
        exact (hasDerivAt_centralTwoError hN x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hasDerivAt_centralTwoError hN x).deriv]
        apply centralTwoErrorDeriv1_nonneg_of_nonpos hN hOdd
        exact Set.mem_Iic.mp (interior_subset hx)
    have hle := hmono (show t ∈ Set.Iic (0 : ℝ) by exact ht0)
      (Set.mem_Iic.mpr le_rfl) ht0
    rw [centralTwoError_zero] at hle
    exact hle
  · have hanti : AntitoneOn (centralTwoError N)
        (Set.Icc 0 (centralTwoLogIncrement N / 2)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · intro x hx
        exact (hasDerivAt_centralTwoError hN x).continuousAt.continuousWithinAt
      · intro x hx
        exact (hasDerivAt_centralTwoError hN x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hasDerivAt_centralTwoError hN x).deriv]
        have hx' : x ∈ Set.Icc (0 : ℝ) (centralTwoLogIncrement N / 2) :=
          interior_subset hx
        exact centralTwoErrorDeriv1_nonpos_between hN hOdd hx'.1 hx'.2
    have hmid0 : 0 ≤ centralTwoLogIncrement N / 2 :=
      (half_pos (centralTwoLogIncrement_pos hN)).le
    have hle := hanti ⟨le_rfl, hmid0⟩ ⟨h0t, ht⟩ h0t
    rw [centralTwoError_zero] at hle
    exact hle

theorem centralTwoPartition_reflect {N : ℕ} (hN : 5 ≤ N) (t : ℝ) :
    centralTwoPartition N (centralTwoLogIncrement N - t) =
      Real.exp (centralTwoLogIncrement N - 2 * t) * centralTwoPartition N t := by
  let L := centralTwoLogIncrement N
  have hNr : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hden : (N : ℝ) - 3 ≠ 0 := by linarith
  have hdenPos : 0 < (N : ℝ) - 3 := by linarith
  have hnumPos : 0 < (N : ℝ) + 1 := by linarith
  have hratioPos : 0 < ((N : ℝ) + 1) / ((N : ℝ) - 3) :=
    div_pos hnumPos hdenPos
  have hExpL : Real.exp L = ((N : ℝ) + 1) / ((N : ℝ) - 3) := by
    dsimp [L, centralTwoLogIncrement]
    exact Real.exp_log hratioPos
  have hExpT : Real.exp t ≠ 0 := ne_of_gt (Real.exp_pos t)
  have hExpLsub : Real.exp (L - t) =
      (((N : ℝ) + 1) / ((N : ℝ) - 3)) / Real.exp t := by
    rw [Real.exp_sub, hExpL]
  have hExpTwoLsub : Real.exp (2 * (L - t)) =
      ((((N : ℝ) + 1) / ((N : ℝ) - 3)) / Real.exp t) ^ 2 := by
    rw [show 2 * (L - t) = (L - t) + (L - t) by ring, Real.exp_add,
      hExpLsub, pow_two]
  have hExpTwoT : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [show 2 * t = t + t by ring, Real.exp_add, pow_two]
  have hExpRight : Real.exp (L - 2 * t) =
      (((N : ℝ) + 1) / ((N : ℝ) - 3)) / Real.exp t ^ 2 := by
    rw [Real.exp_sub, hExpL, hExpTwoT]
  dsimp [L] at hExpLsub hExpTwoLsub hExpRight ⊢
  unfold centralTwoPartition
  rw [hExpLsub, hExpTwoLsub, hExpRight, hExpTwoT]
  field_simp [hden, hExpT]
  ring

theorem centralTwoPhi_reflect {N : ℕ} (hN : 5 ≤ N) (t : ℝ) :
    centralTwoPhi N (centralTwoLogIncrement N - t) =
      centralTwoPhi N t + (centralTwoLogIncrement N - 2 * t) / (N : ℝ) := by
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  have hPne : centralTwoPartition N t ≠ 0 :=
    ne_of_gt (centralTwoPartition_pos hN t)
  unfold centralTwoPhi
  rw [centralTwoPartition_reflect hN]
  rw [Real.log_mul (Real.exp_ne_zero _) hPne, Real.log_exp]
  field_simp [hNne]
  ring

theorem centralTwoError_reflect {N : ℕ} (hN : 5 ≤ N) (t : ℝ) :
    centralTwoError N (centralTwoLogIncrement N - t) = centralTwoError N t := by
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  have hLne : centralTwoLogIncrement N ≠ 0 :=
    ne_of_gt (centralTwoLogIncrement_pos hN)
  unfold centralTwoError
  rw [centralTwoPhi_reflect hN]
  field_simp [hNne, hLne]
  ring

theorem centralTwoError_nonpos {N : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (t : ℝ) :
    centralTwoError N t ≤ 0 := by
  rcases le_total t (centralTwoLogIncrement N / 2) with ht | ht
  · exact centralTwoError_nonpos_before_midpoint hN hOdd ht
  · rw [← centralTwoError_reflect hN t]
    apply centralTwoError_nonpos_before_midpoint hN hOdd
    linarith

theorem hasDerivAt_scaledOddLog {x : ℝ} (hx : 1 < x) :
    HasDerivAt scaledOddLog
      (Real.log ((x + 1) / (x - 1)) - 2 * x / (x ^ 2 - 1)) x := by
  have hden : x - 1 ≠ 0 := by linarith
  have hsq : x ^ 2 - 1 ≠ 0 := by nlinarith
  have hsq' : (-1 : ℝ) + x ^ 2 ≠ 0 := by
    intro h
    apply hsq
    rw [show x ^ 2 - 1 = (-1 : ℝ) + x ^ 2 by ring]
    exact h
  have hratio : (x + 1) / (x - 1) ≠ 0 := by positivity
  have hquot := ((hasDerivAt_id x).add_const 1).div
    ((hasDerivAt_id x).sub_const 1) hden
  have hlog := hquot.log hratio
  have hmul := (hasDerivAt_id x).fun_mul hlog
  unfold scaledOddLog
  convert hmul using 1 <;> try rfl
  simp only [id_eq, Pi.div_apply, one_mul]
  field_simp [hden, hratio, hsq, hsq']
  ring

theorem deriv_scaledOddLog_nonpos {x : ℝ} (hx : 3 ≤ x) :
    deriv scaledOddLog x ≤ 0 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 ≤ (1 : ℝ) / x := by positivity
  have hyThird : (1 : ℝ) / x ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hx0 (by norm_num : (0 : ℝ) < 3)]
    linarith
  have hlog0 := half_log_div_le_sharp_rational hy0 hyThird
  have hdenLeft : 0 < 1 - ((1 : ℝ) / x) ^ 2 / 2 := by
    have hySq : ((1 : ℝ) / x) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 :=
      (sq_le_sq₀ hy0 (by norm_num : (0 : ℝ) ≤ 1 / 3)).2 hyThird
    norm_num at hySq ⊢
    nlinarith
  have hdenRight : 0 < x ^ 2 - 1 := by nlinarith
  have hcomp : ((1 : ℝ) / x) / (1 - ((1 : ℝ) / x) ^ 2 / 2) ≤
      x / (x ^ 2 - 1) := by
    rw [div_le_div_iff₀ hdenLeft hdenRight]
    field_simp [ne_of_gt hx0]
    nlinarith [sq_nonneg x]
  have hlog : Real.log ((1 + (1 : ℝ) / x) / (1 - (1 : ℝ) / x)) ≤
      2 * x / (x ^ 2 - 1) := by
    calc
      _ = 2 * (1 / 2 * Real.log
          ((1 + (1 : ℝ) / x) / (1 - (1 : ℝ) / x))) := by ring
      _ ≤ 2 * (((1 : ℝ) / x) / (1 - ((1 : ℝ) / x) ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hlog0 (by norm_num)
      _ ≤ 2 * (x / (x ^ 2 - 1)) :=
        mul_le_mul_of_nonneg_left hcomp (by norm_num)
      _ = 2 * x / (x ^ 2 - 1) := by ring
  have hx1ne : x - 1 ≠ 0 := by linarith
  have hratio : ((1 + (1 : ℝ) / x) / (1 - (1 : ℝ) / x)) =
      (x + 1) / (x - 1) := by
    field_simp [ne_of_gt hx0, hx1ne]
  rw [hratio] at hlog
  rw [(hasDerivAt_scaledOddLog (by linarith)).deriv]
  linarith

theorem scaledOddLog_antitoneOn : AntitoneOn scaledOddLog (Set.Ici 3) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 3)
  · intro x hx
    have hx3 : (3 : ℝ) ≤ x := Set.mem_Ici.mp hx
    exact (hasDerivAt_scaledOddLog (by linarith)).continuousAt.continuousWithinAt
  · intro x hx
    have hx3 : (3 : ℝ) ≤ x :=
      Set.mem_Ici.mp (interior_subset hx)
    exact (hasDerivAt_scaledOddLog (by linarith)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx3 : (3 : ℝ) ≤ x :=
      Set.mem_Ici.mp (interior_subset hx)
    exact deriv_scaledOddLog_nonpos hx3

theorem scaled_oddLogIncrement_step {N : ℕ} (hN : 5 ≤ N) :
    (N : ℝ) * oddLogIncrement N ≤
      ((N : ℝ) - 2) * oddLogIncrement (N - 2) := by
  have hNr : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hleft : (3 : ℝ) ≤ (N : ℝ) - 2 := by linarith
  have hright : (N : ℝ) - 2 ≤ (N : ℝ) := by linarith
  have hleftMem : (N : ℝ) - 2 ∈ Set.Ici (3 : ℝ) := Set.mem_Ici.mpr hleft
  have hrightMem : (N : ℝ) ∈ Set.Ici (3 : ℝ) := Set.mem_Ici.mpr (by linarith)
  have hanti := scaledOddLog_antitoneOn hleftMem hrightMem hright
  unfold scaledOddLog at hanti
  unfold oddLogIncrement
  rw [Nat.cast_sub (by omega)]
  norm_num only [Nat.cast_ofNat] at hanti ⊢
  simpa using hanti

theorem centralTwoLogIncrement_eq_sum {N : ℕ} (hN : 5 ≤ N) :
    centralTwoLogIncrement N = oddLogIncrement (N - 2) + oddLogIncrement N := by
  unfold centralTwoLogIncrement oddLogIncrement
  rw [Nat.cast_sub (by omega)]
  norm_num only [Nat.cast_ofNat]
  have hNr : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1 : 0 < (N : ℝ) - 1 := by linarith
  have hN3 : 0 < (N : ℝ) - 3 := by linarith
  rw [show (N : ℝ) - 2 + 1 = (N : ℝ) - 1 by ring,
    show (N : ℝ) - 2 - 1 = (N : ℝ) - 3 by ring]
  have hratio1 : ((N : ℝ) - 1) / ((N : ℝ) - 3) ≠ 0 := by
    exact div_ne_zero (ne_of_gt hN1) (ne_of_gt hN3)
  have hratio2 : ((N : ℝ) + 1) / ((N : ℝ) - 1) ≠ 0 := by
    positivity
  rw [← Real.log_mul hratio1 hratio2]
  rw [div_mul_div_cancel₀' (ne_of_gt hN1)]

theorem oddLogIncrement_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < oddLogIncrement N := by
  unfold oddLogIncrement
  apply Real.log_pos
  rw [one_lt_div]
  · linarith
  · have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith

theorem oddProxyScale_two_eq {N : ℕ} (hN : 5 ≤ N) (hOdd : Odd N) :
    oddProxyScale N 2 =
      ((N : ℝ) - 2) /
        ((N : ℝ) * ((N : ℝ) - 1) * oddLogIncrement N) := by
  have hnotEven : ¬Even N := Nat.not_even_iff_odd.mpr hOdd
  have hNr : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 < oddLogIncrement N := oddLogIncrement_pos (by omega)
  unfold oddProxyScale
  rw [SharpSerfling.kappa_of_not_even hnotEven]
  unfold oddLogIncrement at hlog ⊢
  norm_num only [Nat.cast_ofNat]
  field_simp [show (N : ℝ) ≠ 0 by linarith,
    show (N : ℝ) - 1 ≠ 0 by linarith, ne_of_gt hlog]
  ring

/-- The exact three-point coefficient is no larger than the final odd proxy.
This is the manuscript's telescoping logarithm comparison for `m = 2`. -/
theorem centralTwo_scale_le_oddProxy {N : ℕ} (hN : 5 ≤ N) (hOdd : Odd N) :
    2 / ((N : ℝ) * centralTwoLogIncrement N) ≤ oddProxyScale N 2 := by
  have hNr : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 < oddLogIncrement N := oddLogIncrement_pos (by omega)
  have htwo : 0 < centralTwoLogIncrement N := centralTwoLogIncrement_pos hN
  have hstep := scaled_oddLogIncrement_step hN
  have hsum := centralTwoLogIncrement_eq_sum hN
  have hkey : 2 * ((N : ℝ) - 1) * oddLogIncrement N ≤
      ((N : ℝ) - 2) * centralTwoLogIncrement N := by
    rw [hsum]
    nlinarith
  rw [oddProxyScale_two_eq hN hOdd]
  have hdenLeft : 0 < (N : ℝ) * centralTwoLogIncrement N :=
    mul_pos (by linarith) htwo
  have hdenRight : 0 <
      (N : ℝ) * ((N : ℝ) - 1) * oddLogIncrement N :=
    mul_pos (mul_pos (by linarith) (by linarith)) hlog
  rw [div_le_div_iff₀ hdenLeft hdenRight]
  have hmul := mul_le_mul_of_nonneg_left hkey (show (0 : ℝ) ≤ N by positivity)
  nlinarith

/-- Explicit three-term expansion of every two-draw hypergeometric MGF. -/
theorem binomialMgf_two_expansion {N K : ℕ}
    (hN : 2 ≤ N) (hK : K ≤ N) (t : ℝ) :
    binomialMgf N K 2 t =
      (N.choose 2 : ℝ)⁻¹ *
        (((N - K).choose 2 : ℝ) * Real.exp (t * (0 - center N K 2)) +
          ((K * (N - K) : ℕ) : ℝ) * Real.exp (t * (1 - center N K 2)) +
          (K.choose 2 : ℝ) * Real.exp (t * (2 - center N K 2))) := by
  unfold binomialMgf binomialAverage binomialSum
  rw [show antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} by decide]
  simp [hypergeomWeight]
  rw [Nat.cast_sub hK]
  field_simp [show (N.choose 2 : ℝ) ≠ 0 by
    exact_mod_cast Nat.choose_ne_zero hN]
  left
  ring

/-- The hard `m = 2` slice is the manuscript's explicit three-point law. -/
theorem mgf_lowerNearest_two_explicit {N : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (t : ℝ) :
    mgf N ((N - 1) / 2) 2 t =
      ((N : ℝ) + 1) / (4 * (N : ℝ)) *
          Real.exp (t * (-(N : ℝ) + 1) / (N : ℝ)) +
        ((N : ℝ) + 1) / (2 * (N : ℝ)) *
          Real.exp (t / (N : ℝ)) +
        ((N : ℝ) - 3) / (4 * (N : ℝ)) *
          Real.exp (t * ((N : ℝ) + 1) / (N : ℝ)) := by
  let K := (N - 1) / 2
  have hK : K ≤ N := by dsimp [K]; omega
  rw [mgf_eq_binomialMgf hK, binomialMgf_two_expansion (by omega) hK]
  obtain ⟨q, rfl⟩ := hOdd
  have hq2 : 2 ≤ q := by omega
  have hKq : ((2 * q + 1 - 1) / 2) = q := by omega
  simp only [K, hKq]
  rw [show 2 * q + 1 - q = q + 1 by omega]
  have hcenter : center (2 * q + 1) q 2 =
      (2 * (q : ℝ)) / (2 * (q : ℝ) + 1) := by
    unfold center
    push_cast
    ring
  rw [hcenter]
  rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two]
  push_cast
  ring_nf
  field_simp [show (q : ℝ) ≠ 0 by positivity,
    show (2 * (q : ℝ) + 1) ≠ 0 by positivity]
  ring

theorem mgf_lowerNearest_two_eq_partition {N : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (t : ℝ) :
    mgf N ((N - 1) / 2) 2 t =
      Real.exp (-(((N : ℝ) - 1) / (N : ℝ)) * t) *
        centralTwoPartition N t / (4 * (N : ℝ)) := by
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  have h0 : Real.exp (t * (-(N : ℝ) + 1) / (N : ℝ)) =
      Real.exp (-(((N : ℝ) - 1) / (N : ℝ)) * t) := by
    congr 1
    field_simp [hNne]
    ring
  have h1 : Real.exp (t / (N : ℝ)) =
      Real.exp (-(((N : ℝ) - 1) / (N : ℝ)) * t) * Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    field_simp [hNne]
    ring
  have h2 : Real.exp (t * ((N : ℝ) + 1) / (N : ℝ)) =
      Real.exp (-(((N : ℝ) - 1) / (N : ℝ)) * t) * Real.exp (2 * t) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [hNne]
    ring
  rw [mgf_lowerNearest_two_explicit hN hOdd, h0, h1, h2]
  unfold centralTwoPartition
  field_simp [hNne]
  ring

theorem log_mgf_lowerNearest_two_eq_phi {N : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (t : ℝ) :
    Real.log (mgf N ((N - 1) / 2) 2 t) = centralTwoPhi N t := by
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  have hdenNe : 4 * (N : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hNne
  have hPne : centralTwoPartition N t ≠ 0 :=
    ne_of_gt (centralTwoPartition_pos hN t)
  rw [mgf_lowerNearest_two_eq_partition hN hOdd]
  rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero _) hPne) hdenNe,
    Real.log_mul (Real.exp_ne_zero _) hPne, Real.log_exp]
  unfold centralTwoPhi
  ring

/-- Equality in the central two-draw estimate at the manuscript's distinguished
tilt `log ((N + 1) / (N - 1))` (Lemma 5). -/
theorem log_mgf_lowerNearest_two_eq_exact_at_increment {N : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) :
    Real.log (mgf N ((N - 1) / 2) 2 (centralTwoLogIncrement N)) =
      (centralTwoLogIncrement N) ^ 2 /
        ((N : ℝ) * centralTwoLogIncrement N) := by
  rw [log_mgf_lowerNearest_two_eq_phi hN hOdd]
  have hreflect := centralTwoError_reflect hN (0 : ℝ)
  rw [sub_zero, centralTwoError_zero] at hreflect
  unfold centralTwoError at hreflect
  linarith

/-- The optimal quadratic logarithmic proxy for the manuscript's central
three-point base case. -/
theorem log_mgf_lowerNearest_two_le_exact {N : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (t : ℝ) :
    Real.log (mgf N ((N - 1) / 2) 2 t) ≤
      t ^ 2 / ((N : ℝ) * centralTwoLogIncrement N) := by
  rw [log_mgf_lowerNearest_two_eq_phi hN hOdd]
  have herror := centralTwoError_nonpos hN hOdd t
  unfold centralTwoError at herror
  linarith

theorem mgf_lowerNearest_two_le_oddProxy {N : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (t : ℝ) :
    mgf N ((N - 1) / 2) 2 t ≤
      Real.exp (oddProxyScale N 2 * t ^ 2 / 2) := by
  apply (Real.log_le_iff_le_exp (mgf_pos (by omega) t)).mp
  have hexact := log_mgf_lowerNearest_two_le_exact hN hOdd t
  have hscale := centralTwo_scale_le_oddProxy hN hOdd
  have hmul := mul_le_mul_of_nonneg_right hscale (sq_nonneg t)
  calc
    Real.log (mgf N ((N - 1) / 2) 2 t) ≤
        t ^ 2 / ((N : ℝ) * centralTwoLogIncrement N) := hexact
    _ = (2 / ((N : ℝ) * centralTwoLogIncrement N)) * t ^ 2 / 2 := by ring
    _ ≤ oddProxyScale N 2 * t ^ 2 / 2 := by nlinarith

/-- The full sharp odd-population theorem is now reduced solely to the
one-draw (Kearns--Saul) bound; the central two-draw base is discharged here. -/
theorem odd_mgf_le_of_one_draw
    (hone : ∀ {N K : ℕ} {t : ℝ}, 3 ≤ N → Odd N → K ≤ N →
      mgf N K 1 t ≤ Real.exp (oddProxyScale N 1 * t ^ 2 / 2))
    {N K m : ℕ} (hN : 3 ≤ N) (hOdd : Odd N)
    (hK : K ≤ N) (hm : m ≤ N) (t : ℝ) :
    mgf N K m t ≤ Real.exp (oddProxyScale N m * t ^ 2 / 2) := by
  exact odd_mgf_le_of_bases hone
    (fun hN hOdd ↦ mgf_lowerNearest_two_le_oddProxy hN hOdd _) hN hOdd hK hm t

end SharpSerfling.Hypergeometric
