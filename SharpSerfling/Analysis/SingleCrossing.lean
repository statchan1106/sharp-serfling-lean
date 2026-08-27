import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace SharpSerfling.Analysis

open Set
open scoped Interval

private theorem iteratedDerivWithin_exp_zero {x : ℝ} (hx : 0 ≠ x) (n : ℕ) :
    iteratedDerivWithin n Real.exp (uIcc 0 x) 0 = Real.exp 0 := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx)
    Real.contDiff_exp.contDiffAt left_mem_uIcc]
  have h := congrFun (iteratedDeriv_exp_const_mul n 1) 0
  simpa only [one_mul, one_pow] using h

/-- Third-order Taylor upper bound for `1 - exp (-a)`. -/
theorem one_sub_exp_neg_le_cubic {a : ℝ} (ha : 0 ≤ a) :
    1 - Real.exp (-a) ≤ a - a ^ 2 / 2 + a ^ 3 / 6 := by
  rcases ha.eq_or_lt with rfl | ha
  · norm_num
  · obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.exp) (n := 3) (x := -a) (x₀ := 0) (by linarith)
        Real.contDiff_exp.contDiffOn
    have hiter : iteratedDeriv 4 Real.exp y = Real.exp y := by
      have h := congrFun (iteratedDeriv_exp_const_mul 4 1) y
      simpa only [one_mul, one_pow] using h
    rw [hiter] at heq
    rw [taylorWithinEval_succ, taylorWithinEval_succ, taylorWithinEval_succ,
      taylor_within_zero_eval] at heq
    rw [iteratedDerivWithin_exp_zero (by linarith) 1,
      iteratedDerivWithin_exp_zero (by linarith) 2,
      iteratedDerivWithin_exp_zero (by linarith) 3] at heq
    norm_num at heq
    have hrem : 0 ≤ Real.exp y * a ^ 4 / 24 := by positivity
    nlinarith

/-- Lagrange-form third-order upper bound for the positive exponential. -/
theorem exp_le_quadratic_add_cubic_remainder {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 * Real.exp x / 6 := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num
  · obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.exp) (n := 2) (x := x) (x₀ := 0) (hx.ne').symm
        Real.contDiff_exp.contDiffOn
    have hiter : iteratedDeriv 3 Real.exp y = Real.exp y := by
      have h := congrFun (iteratedDeriv_exp_const_mul 3 1) y
      simpa only [one_mul, one_pow] using h
    rw [hiter] at heq
    rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval] at heq
    rw [iteratedDerivWithin_exp_zero (hx.ne').symm 1,
      iteratedDerivWithin_exp_zero (hx.ne').symm 2] at heq
    norm_num at heq
    have hy' : y ∈ Ioo (0 : ℝ) x := by simpa [uIoo_of_lt hx] using hy
    have hey : Real.exp y ≤ Real.exp x := Real.exp_le_exp.mpr hy'.2.le
    have hmul := mul_le_mul_of_nonneg_right hey (by positivity : 0 ≤ x ^ 3 / 6)
    nlinarith

noncomputable def singleCrossingBase (a c d z : ℝ) : ℝ :=
  Real.exp ((d - c) * z ^ 2 + (a + c) * z - a)

noncomputable def singleCrossingIntegrand (a c d z : ℝ) : ℝ :=
  z * Real.exp (d * z ^ 2) *
    (1 - Real.exp ((1 - z) * (c * z - a)))

/-- Accumulated derivative difference on the hard central slice. -/
noncomputable def hardCentralQ (S v r B beta : ℝ) : ℝ :=
  Real.exp (S * beta ^ 2 / 2) - 1 -
    ∫ x in (0 : ℝ)..beta, v * x * Real.exp (r * x + B * x ^ 2 / 2)

noncomputable def hardCentralDiscriminant (a r gamma : ℝ) : ℝ :=
  r ^ 2 - 2 * gamma * a

noncomputable def hardCentralLowerRoot (a r gamma : ℝ) : ℝ :=
  (r - Real.sqrt (hardCentralDiscriminant a r gamma)) / gamma

noncomputable def hardCentralUpperRoot (a r gamma : ℝ) : ℝ :=
  (r + Real.sqrt (hardCentralDiscriminant a r gamma)) / gamma

theorem continuous_singleCrossingBase (a c d : ℝ) :
    Continuous (singleCrossingBase a c d) := by
  unfold singleCrossingBase
  fun_prop

theorem continuous_singleCrossingIntegrand (a c d : ℝ) :
    Continuous (singleCrossingIntegrand a c d) := by
  unfold singleCrossingIntegrand
  fun_prop

/-- Integral representation of the accumulated central comparison. -/
theorem hardCentralQ_eq_integral {S v r B gamma a t : ℝ}
    (hv : v = S * Real.exp (-a)) (hgamma : gamma = S - B) :
    hardCentralQ S v r B t =
      ∫ x in (0 : ℝ)..t,
        S * x * Real.exp (S * x ^ 2 / 2) *
          (1 - Real.exp (-a + r * x - gamma * x ^ 2 / 2)) := by
  let F : ℝ → ℝ := fun x ↦ Real.exp (S * x ^ 2 / 2)
  let U : ℝ → ℝ := fun x ↦ S * x * Real.exp (S * x ^ 2 / 2)
  have hFderiv : deriv F = U := by
    funext x
    have hinner := ((hasDerivAt_pow 2 x).const_mul S).div_const 2
    have hexp := hinner.exp.deriv
    dsimp [F, U] at hexp ⊢
    rw [hexp]
    norm_num
    ring
  have hFInt := intervalIntegral.integral_deriv_eq_sub'
    (a := (0 : ℝ)) (b := t) F hFderiv
      (fun x _ ↦ by dsimp [F]; fun_prop) (by dsimp [U]; fun_prop)
  have htarget : Real.exp (S * t ^ 2 / 2) - 1 =
      ∫ x in (0 : ℝ)..t, U x := by
    simpa [F] using hFInt.symm
  have hU : IntervalIntegrable U MeasureTheory.volume 0 t := by
    have : Continuous U := by dsimp [U]; fun_prop
    exact this.intervalIntegrable 0 t
  have hV : IntervalIntegrable
      (fun x : ℝ ↦ v * x * Real.exp (r * x + B * x ^ 2 / 2))
      MeasureTheory.volume 0 t := by
    have : Continuous (fun x : ℝ ↦
        v * x * Real.exp (r * x + B * x ^ 2 / 2)) := by fun_prop
    exact this.intervalIntegrable 0 t
  unfold hardCentralQ
  rw [htarget]
  rw [← intervalIntegral.integral_sub hU hV]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp [U]
  rw [hv]
  have hexp :
      Real.exp (-a) * Real.exp (r * x + B * x ^ 2 / 2) =
        Real.exp (S * x ^ 2 / 2) *
          Real.exp (-a + r * x - gamma * x ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hgamma]
    ring
  calc
    S * x * Real.exp (S * x ^ 2 / 2) -
          S * Real.exp (-a) * x * Real.exp (r * x + B * x ^ 2 / 2) =
        S * x * Real.exp (S * x ^ 2 / 2) -
          S * x * (Real.exp (-a) * Real.exp (r * x + B * x ^ 2 / 2)) := by ring
    _ = S * x * Real.exp (S * x ^ 2 / 2) -
          S * x * (Real.exp (S * x ^ 2 / 2) *
            Real.exp (-a + r * x - gamma * x ^ 2 / 2)) := by rw [hexp]
    _ = _ := by ring

theorem hardCentral_quadratic_factor {a r gamma x : ℝ}
    (hgamma : gamma ≠ 0)
    (hdisc : 0 ≤ hardCentralDiscriminant a r gamma) :
    -a + r * x - gamma * x ^ 2 / 2 =
      -(gamma / 2) * ((x - hardCentralLowerRoot a r gamma) *
        (x - hardCentralUpperRoot a r gamma)) := by
  have hsqrt := Real.sq_sqrt hdisc
  unfold hardCentralLowerRoot hardCentralUpperRoot
  unfold hardCentralDiscriminant at hsqrt ⊢
  field_simp [hgamma]
  ring_nf at hsqrt ⊢
  nlinarith

theorem hardCentral_lowerRoot_pos {a r gamma : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hgamma : 0 < gamma)
    (hcross : 2 * gamma * a < r ^ 2) :
    0 < hardCentralLowerRoot a r gamma := by
  have hdisc : 0 ≤ hardCentralDiscriminant a r gamma := by
    unfold hardCentralDiscriminant
    linarith
  have hsqrt := Real.sq_sqrt hdisc
  have hsqrt0 := Real.sqrt_nonneg (hardCentralDiscriminant a r gamma)
  have hterm : 0 < 2 * gamma * a := by positivity
  have hsqrtLt : Real.sqrt (hardCentralDiscriminant a r gamma) < r := by
    by_contra hnot
    have hrle : r ≤ Real.sqrt (hardCentralDiscriminant a r gamma) := le_of_not_gt hnot
    have hsquares : r ^ 2 ≤
        Real.sqrt (hardCentralDiscriminant a r gamma) ^ 2 :=
      (sq_le_sq₀ hr.le hsqrt0).2 hrle
    unfold hardCentralDiscriminant at hsqrt hsquares
    nlinarith
  unfold hardCentralLowerRoot
  exact div_pos (sub_pos.mpr hsqrtLt) hgamma

theorem hardCentral_lowerRoot_lt_upperRoot {a r gamma : ℝ}
    (hgamma : 0 < gamma)
    (hcross : 0 < hardCentralDiscriminant a r gamma) :
    hardCentralLowerRoot a r gamma < hardCentralUpperRoot a r gamma := by
  unfold hardCentralLowerRoot hardCentralUpperRoot
  exact div_lt_div_of_pos_right (by
    have := Real.sqrt_pos.2 hcross
    linarith) hgamma

theorem hardCentral_upperRoot_equation {a r gamma : ℝ}
    (hgamma : gamma ≠ 0)
    (hdisc : 0 ≤ hardCentralDiscriminant a r gamma) :
    r * hardCentralUpperRoot a r gamma =
      a + gamma * hardCentralUpperRoot a r gamma ^ 2 / 2 := by
  have hfactor := hardCentral_quadratic_factor
    (a := a) (r := r) (gamma := gamma)
    (x := hardCentralUpperRoot a r gamma) hgamma hdisc
  norm_num at hfactor
  linarith

/-- Once the accumulated difference is nonnegative at the larger crossing
root, it is nonnegative for every nonnegative endpoint. -/
theorem hardCentralQ_nonneg_of_upperRoot
    {S v r B gamma a : ℝ}
    (hS : 0 < S) (hv : v = S * Real.exp (-a))
    (hgammaEq : gamma = S - B) (ha : 0 < a) (hr : 0 < r)
    (hgamma : 0 < gamma) (hcross : 2 * gamma * a < r ^ 2)
    (hQroot : 0 ≤ hardCentralQ S v r B (hardCentralUpperRoot a r gamma))
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ hardCentralQ S v r B t := by
  let tau : ℝ := hardCentralLowerRoot a r gamma
  let beta : ℝ := hardCentralUpperRoot a r gamma
  let D : ℝ → ℝ := fun x ↦
    S * x * Real.exp (S * x ^ 2 / 2) *
      (1 - Real.exp (-a + r * x - gamma * x ^ 2 / 2))
  have hdisc : 0 < hardCentralDiscriminant a r gamma := by
    unfold hardCentralDiscriminant
    linarith
  have htau0 : 0 < tau := by
    dsimp [tau]
    exact hardCentral_lowerRoot_pos ha hr hgamma hcross
  have htaubeta : tau < beta := by
    dsimp [tau, beta]
    exact hardCentral_lowerRoot_lt_upperRoot hgamma hdisc
  have hbeta0 : 0 < beta := htau0.trans htaubeta
  have hfactor (x : ℝ) :
      -a + r * x - gamma * x ^ 2 / 2 =
        -(gamma / 2) * ((x - tau) * (x - beta)) := by
    dsimp [tau, beta]
    exact hardCentral_quadratic_factor (ne_of_gt hgamma) hdisc.le
  have hDcontinuous : Continuous D := by
    dsimp [D]
    fun_prop
  have hQeq (y : ℝ) : hardCentralQ S v r B y = ∫ x in (0 : ℝ)..y, D x := by
    simpa [D] using hardCentralQ_eq_integral (t := y) hv hgammaEq
  have hDleft {x : ℝ} (hx0 : 0 ≤ x) (hxtau : x ≤ tau) : 0 ≤ D x := by
    have hxbeta : x ≤ beta := hxtau.trans htaubeta.le
    have hproduct : 0 ≤ (x - tau) * (x - beta) :=
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxtau) (sub_nonpos.mpr hxbeta)
    have hq : -a + r * x - gamma * x ^ 2 / 2 ≤ 0 := by
      rw [hfactor]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hproduct
    dsimp [D]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hS.le hx0) (Real.exp_pos _).le)
      (sub_nonneg.mpr (Real.exp_le_one_iff.mpr hq))
  have hDmiddle {x : ℝ} (htaux : tau ≤ x) (hxbeta : x ≤ beta) : D x ≤ 0 := by
    have hproduct : (x - tau) * (x - beta) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr htaux) (sub_nonpos.mpr hxbeta)
    have hq : 0 ≤ -a + r * x - gamma * x ^ 2 / 2 := by
      rw [hfactor]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (by positivity)) hproduct
    have hpref : 0 ≤ S * x * Real.exp (S * x ^ 2 / 2) := by
      exact mul_nonneg (mul_nonneg hS.le (htau0.le.trans htaux)) (Real.exp_pos _).le
    dsimp [D]
    exact mul_nonpos_of_nonneg_of_nonpos hpref
      (sub_nonpos.mpr (Real.one_le_exp_iff.mpr hq))
  have hDright {x : ℝ} (hbetax : beta ≤ x) : 0 ≤ D x := by
    have hproduct : 0 ≤ (x - tau) * (x - beta) :=
      mul_nonneg (sub_nonneg.mpr (htaubeta.le.trans hbetax)) (sub_nonneg.mpr hbetax)
    have hq : -a + r * x - gamma * x ^ 2 / 2 ≤ 0 := by
      rw [hfactor]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hproduct
    dsimp [D]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hS.le (hbeta0.le.trans hbetax)) (Real.exp_pos _).le)
      (sub_nonneg.mpr (Real.exp_le_one_iff.mpr hq))
  rw [hQeq]
  rcases le_total t tau with httau | htaut
  · exact intervalIntegral.integral_nonneg ht (fun x hx ↦ hDleft hx.1 (hx.2.trans httau))
  · rcases le_total t beta with htbeta | hbetat
    · have hmiddleInt : (∫ x in t..beta, D x) ≤ 0 := by
        calc
          (∫ x in t..beta, D x) ≤ ∫ _ in t..beta, (0 : ℝ) := by
            apply intervalIntegral.integral_mono_on htbeta
              (hDcontinuous.intervalIntegrable t beta)
              (continuous_const.intervalIntegrable t beta)
            intro x hx
            exact hDmiddle (htaut.trans hx.1) hx.2
          _ = 0 := by simp
      have hadd : (∫ x in (0 : ℝ)..t, D x) + (∫ x in t..beta, D x) =
          ∫ x in (0 : ℝ)..beta, D x :=
        intervalIntegral.integral_add_adjacent_intervals
          (hDcontinuous.intervalIntegrable 0 t)
          (hDcontinuous.intervalIntegrable t beta)
      have hrootInt : 0 ≤ ∫ x in (0 : ℝ)..beta, D x := by
        rw [← hQeq]
        simpa [beta] using hQroot
      linarith

    · have hrightInt : 0 ≤ ∫ x in beta..t, D x := by
        exact intervalIntegral.integral_nonneg hbetat (fun x hx ↦ hDright hx.1)
      have hadd : (∫ x in (0 : ℝ)..beta, D x) + (∫ x in beta..t, D x) =
          ∫ x in (0 : ℝ)..t, D x :=
        intervalIntegral.integral_add_adjacent_intervals
          (hDcontinuous.intervalIntegrable 0 beta)
          (hDcontinuous.intervalIntegrable beta t)
      have hrootInt : 0 ≤ ∫ x in (0 : ℝ)..beta, D x := by
        rw [← hQeq]
        simpa [beta] using hQroot
      linarith

/-- In the complementary case where the derivative ratio never crosses one,
the accumulated comparison is pointwise nonnegative. -/
theorem hardCentralQ_nonneg_of_no_crossing
    {S v r B gamma a t : ℝ}
    (hS : 0 < S) (hv : v = S * Real.exp (-a))
    (hgammaEq : gamma = S - B) (hgamma : 0 < gamma)
    (hnoCross : r ^ 2 ≤ 2 * gamma * a) (ht : 0 ≤ t) :
    0 ≤ hardCentralQ S v r B t := by
  rw [hardCentralQ_eq_integral hv hgammaEq]
  apply intervalIntegral.integral_nonneg ht
  intro x hx
  have hq : -a + r * x - gamma * x ^ 2 / 2 ≤ 0 := by
    have hsquare := sq_nonneg (gamma * x - r)
    nlinarith
  exact mul_nonneg
    (mul_nonneg (mul_nonneg hS.le hx.1) (Real.exp_pos _).le)
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr hq))

/-- Exact integration identity behind the signed-area comparison. -/
theorem singleCrossing_integral_identity {a c d : ℝ}
    (hd : 0 < d) (hcd : c < d) :
    2 * (d - c) * (∫ z in (0 : ℝ)..1, singleCrossingIntegrand a c d z) =
      (a + c) * (∫ z in (0 : ℝ)..1, singleCrossingBase a c d z) +
        Real.exp (-a) - 1 - (c / d) * (Real.exp d - 1) := by
  let f : ℝ → ℝ := fun z ↦ Real.exp (d * z ^ 2)
  let g : ℝ → ℝ := singleCrossingBase a c d
  let p : ℝ → ℝ := fun z ↦ z * Real.exp (d * z ^ 2)
  let q : ℝ → ℝ := fun z ↦ z * singleCrossingBase a c d z
  have hfderiv : deriv f = fun z ↦ 2 * d * p z := by
    funext z
    have hsq := (hasDerivAt_id z).mul (hasDerivAt_id z)
    have hexp := (hsq.const_mul d).exp.deriv
    dsimp [f, p]
    have hfun : (fun x : ℝ ↦ Real.exp (d * x ^ 2)) =
        (fun x : ℝ ↦ Real.exp (d * ((id : ℝ → ℝ) * (id : ℝ → ℝ)) x)) := by
      funext x
      simp only [Pi.mul_apply, id_eq, pow_two]
    rw [hfun, hexp]
    simp only [Pi.mul_apply, id_eq, one_mul, mul_one]
    ring
  have hgderiv : deriv g =
      fun z ↦ 2 * (d - c) * q z + (a + c) * g z := by
    funext z
    have hsq := (hasDerivAt_id z).mul (hasDerivAt_id z)
    have hquad := hsq.const_mul (d - c)
    have hlin := (hasDerivAt_id z).const_mul (a + c)
    have hinner := (hquad.add hlin).sub_const a
    have hexp := hinner.exp.deriv
    dsimp [g, q, singleCrossingBase]
    have hfun : singleCrossingBase a c d =
        (fun x : ℝ ↦ Real.exp
          ((((fun y : ℝ ↦ (d - c) *
              ((id : ℝ → ℝ) * (id : ℝ → ℝ)) y) +
            fun y : ℝ ↦ (a + c) * id y) x) - a)) := by
      funext x
      simp only [singleCrossingBase, Pi.add_apply, Pi.mul_apply, id_eq, pow_two]
    rw [hfun, hexp]
    simp only [Pi.add_apply, Pi.mul_apply, id_eq, one_mul, mul_one]
    ring_nf
  have hfInt := intervalIntegral.integral_deriv_eq_sub' (a := (0 : ℝ)) (b := 1) f hfderiv
    (fun z _ ↦ by dsimp [f]; fun_prop)
    (by dsimp [p]; fun_prop)
  have hgInt := intervalIntegral.integral_deriv_eq_sub' (a := (0 : ℝ)) (b := 1) g hgderiv
    (fun z _ ↦ by
      change DifferentiableAt ℝ
        (fun x : ℝ ↦ Real.exp ((d - c) * x ^ 2 + (a + c) * x - a)) z
      fun_prop)
    (by dsimp [q, g, singleCrossingBase]; fun_prop)
  have hpInt :
      2 * d * (∫ z in (0 : ℝ)..1, p z) = Real.exp d - 1 := by
    simp only [intervalIntegral.integral_const_mul] at hfInt
    simpa [f] using hfInt
  have hqInt :
      2 * (d - c) * (∫ z in (0 : ℝ)..1, q z) +
          (a + c) * (∫ z in (0 : ℝ)..1, g z) =
        Real.exp d - Real.exp (-a) := by
    have hq : IntervalIntegrable q MeasureTheory.volume 0 1 := by
      dsimp [q]
      exact (continuous_id.mul (continuous_singleCrossingBase a c d)).intervalIntegrable 0 1
    have hg : IntervalIntegrable g MeasureTheory.volume 0 1 := by
      exact (continuous_singleCrossingBase a c d).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add (hq.const_mul (2 * (d - c)))
      (hg.const_mul (a + c))] at hgInt
    simp only [intervalIntegral.integral_const_mul] at hgInt
    simpa [g, singleCrossingBase] using hgInt
  have hintegrand (z : ℝ) : singleCrossingIntegrand a c d z = p z - q z := by
    have hexp :
        Real.exp (d * z ^ 2) * Real.exp ((1 - z) * (c * z - a)) =
          singleCrossingBase a c d z := by
      rw [← Real.exp_add]
      unfold singleCrossingBase
      congr 1
      ring
    unfold singleCrossingIntegrand p q
    rw [mul_sub, mul_one, mul_assoc, hexp]
  have hp : IntervalIntegrable p MeasureTheory.volume 0 1 := by
    have hpcont : Continuous p := by dsimp [p]; fun_prop
    exact hpcont.intervalIntegrable 0 1
  have hq : IntervalIntegrable q MeasureTheory.volume 0 1 := by
    dsimp [q]
    exact (continuous_id.mul (continuous_singleCrossingBase a c d)).intervalIntegrable 0 1
  have hsplit :
      (∫ z in (0 : ℝ)..1, singleCrossingIntegrand a c d z) =
        (∫ z in (0 : ℝ)..1, p z) - ∫ z in (0 : ℝ)..1, q z := by
    simp_rw [hintegrand]
    exact intervalIntegral.integral_sub hp hq
  have hd0 : d ≠ 0 := ne_of_gt hd
  rw [hsplit]
  field_simp [hd0]
  nlinarith

/-- Elementary lower bound for the auxiliary exponential integral. -/
theorem singleCrossingBase_integral_lower (a c d : ℝ) :
    1 + (d - c) / 3 + (c - a) / 2 ≤
      ∫ z in (0 : ℝ)..1, singleCrossingBase a c d z := by
  let P : ℝ → ℝ := fun z ↦
    1 + (d - c) * z ^ 2 + (a + c) * z - a
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hbase := continuous_singleCrossingBase a c d
  have hmono : (∫ z in (0 : ℝ)..1, P z) ≤
      ∫ z in (0 : ℝ)..1, singleCrossingBase a c d z := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hP.intervalIntegrable 0 1) (hbase.intervalIntegrable 0 1)
    intro z hz
    dsimp [P, singleCrossingBase]
    have h := Real.add_one_le_exp ((d - c) * z ^ 2 + (a + c) * z - a)
    linarith
  have hPint : (∫ z in (0 : ℝ)..1, P z) =
      1 + (d - c) / 3 + (c - a) / 2 := by
    have hA : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hB : IntervalIntegrable (fun z : ℝ ↦ (d - c) * z ^ 2)
        MeasureTheory.volume 0 1 :=
      (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
    have hC : IntervalIntegrable (fun z : ℝ ↦ (a + c) * z)
        MeasureTheory.volume 0 1 :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 1
    have hD : IntervalIntegrable (fun _ : ℝ ↦ a) MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hBval : (∫ z in (0 : ℝ)..1, (d - c) * z ^ 2) = (d - c) / 3 := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      ring
    have hCval : (∫ z in (0 : ℝ)..1, (a + c) * z) = (a + c) / 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      norm_num
      ring
    calc
      (∫ z in (0 : ℝ)..1, P z) =
          (∫ z in (0 : ℝ)..1, (1 : ℝ)) +
            (∫ z in (0 : ℝ)..1, (d - c) * z ^ 2) +
            (∫ z in (0 : ℝ)..1, (a + c) * z) -
            (∫ _ in (0 : ℝ)..1, a) := by
        rw [← intervalIntegral.integral_add hA hB,
          ← intervalIntegral.integral_add (hA.add hB) hC,
          ← intervalIntegral.integral_sub ((hA.add hB).add hC) hD]
      _ = 1 + (d - c) / 3 + (c - a) / 2 := by
        rw [hBval, hCval]
        simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, one_mul]
        norm_num
        ring
  rw [← hPint]
  exact hmono

/-- Signed-area lemma used for the hard central hypergeometric slice. -/
theorem singleCrossing_integral_nonneg {a c d : ℝ}
    (ha : 0 < a) (hac : a < c) (hcd : c < d) (hc2 : c ≤ 2 * a)
    (hcertificate : a ^ 3 + c * d ^ 2 * Real.exp d ≤
      (2 * a - c) * (d - c)) :
    0 ≤ ∫ z in (0 : ℝ)..1, singleCrossingIntegrand a c d z := by
  have hc : 0 < c := ha.trans hac
  have hd : 0 < d := hc.trans hcd
  have hI0 := singleCrossingBase_integral_lower a c d
  have hneg := one_sub_exp_neg_le_cubic ha.le
  have hexp := exp_le_quadratic_add_cubic_remainder hd.le
  have hratio : (Real.exp d - 1) / d ≤
      1 + d / 2 + d ^ 2 * Real.exp d / 6 := by
    rw [div_le_iff₀ hd]
    nlinarith
  have hI0mul := mul_le_mul_of_nonneg_left hI0 (add_nonneg ha.le hc.le)
  have hratiomul := mul_le_mul_of_nonneg_left hratio hc.le
  have hdiv : (c / d) * (Real.exp d - 1) = c * ((Real.exp d - 1) / d) := by
    field_simp [ne_of_gt hd]
  have hlower :
      ((2 * a - c) * (d - c) - a ^ 3 - c * d ^ 2 * Real.exp d) / 6 ≤
        (a + c) * (∫ z in (0 : ℝ)..1, singleCrossingBase a c d z) +
          Real.exp (-a) - 1 - (c / d) * (Real.exp d - 1) := by
    rw [hdiv]
    nlinarith
  have hnum : 0 ≤
      ((2 * a - c) * (d - c) - a ^ 3 - c * d ^ 2 * Real.exp d) / 6 := by
    nlinarith
  have hidentity := singleCrossing_integral_identity (a := a) (c := c) (d := d) hd hcd
  have hproduct : 0 ≤
      2 * (d - c) * (∫ z in (0 : ℝ)..1, singleCrossingIntegrand a c d z) := by
    rw [hidentity]
    exact hnum.trans hlower
  exact nonneg_of_mul_nonneg_right hproduct (by positivity)

/-- The endpoint accumulated difference is exactly the signed-area integral
after the manuscript's change of variables `x = beta * z`. -/
theorem hardCentralQ_endpoint_eq_singleCrossing
    {S v r B gamma a beta : ℝ}
    (hv : v = S * Real.exp (-a)) (hgamma : gamma = S - B)
    (hroot : r * beta = a + gamma * beta ^ 2 / 2) :
    hardCentralQ S v r B beta =
      S * beta ^ 2 *
        (∫ z in (0 : ℝ)..1,
          singleCrossingIntegrand a (gamma * beta ^ 2 / 2) (S * beta ^ 2 / 2) z) := by
  let F : ℝ → ℝ := fun x ↦ Real.exp (S * x ^ 2 / 2)
  let U : ℝ → ℝ := fun x ↦ S * x * Real.exp (S * x ^ 2 / 2)
  let V : ℝ → ℝ := fun x ↦ v * x * Real.exp (r * x + B * x ^ 2 / 2)
  let W : ℝ → ℝ := fun x ↦ U x - V x
  have hFderiv : deriv F = U := by
    funext x
    have hinner := ((hasDerivAt_pow 2 x).const_mul S).div_const 2
    have hexp := hinner.exp.deriv
    dsimp [F, U] at hexp ⊢
    rw [hexp]
    norm_num
    ring
  have hFInt := intervalIntegral.integral_deriv_eq_sub'
    (a := (0 : ℝ)) (b := beta) F hFderiv
      (fun x _ ↦ by dsimp [F]; fun_prop) (by dsimp [U]; fun_prop)
  have hF : Real.exp (S * beta ^ 2 / 2) - 1 =
      ∫ x in (0 : ℝ)..beta, U x := by
    simpa [F] using hFInt.symm
  have hU : IntervalIntegrable U MeasureTheory.volume 0 beta := by
    have : Continuous U := by dsimp [U]; fun_prop
    exact this.intervalIntegrable 0 beta
  have hV : IntervalIntegrable V MeasureTheory.volume 0 beta := by
    have : Continuous V := by dsimp [V]; fun_prop
    exact this.intervalIntegrable 0 beta
  have hQ : hardCentralQ S v r B beta =
      ∫ x in (0 : ℝ)..beta, W x := by
    unfold hardCentralQ
    rw [hF]
    dsimp [W, V]
    rw [intervalIntegral.integral_sub hU hV]
  have hchange : beta * (∫ z in (0 : ℝ)..1, W (beta * z)) =
      ∫ x in (0 : ℝ)..beta, W x := by
    simpa only [smul_eq_mul, mul_zero, mul_one] using
      (intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1) W beta)
  rw [hQ, ← hchange]
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro z hz
  dsimp [W, U, V, singleCrossingIntegrand]
  rw [hv]
  have hexp :
      Real.exp (-a) * Real.exp (r * (beta * z) + B * (beta * z) ^ 2 / 2) =
        Real.exp (S * beta ^ 2 / 2 * z ^ 2) *
          Real.exp ((1 - z) * (gamma * beta ^ 2 / 2 * z - a)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hgamma] at hroot ⊢
    rw [show r * (beta * z) = (r * beta) * z by ring, hroot]
    ring
  have hexpF : Real.exp (S * (beta * z) ^ 2 / 2) =
      Real.exp (S * beta ^ 2 / 2 * z ^ 2) := by
    congr 1
    ring
  rw [hexpF]
  calc
    beta *
        (S * (beta * z) * Real.exp (S * beta ^ 2 / 2 * z ^ 2) -
          S * Real.exp (-a) * (beta * z) *
            Real.exp (r * (beta * z) + B * (beta * z) ^ 2 / 2)) =
      S * beta ^ 2 * z *
        (Real.exp (S * beta ^ 2 / 2 * z ^ 2) -
          (Real.exp (-a) * Real.exp (r * (beta * z) + B * (beta * z) ^ 2 / 2))) := by ring
    _ = S * beta ^ 2 *
        (z * Real.exp (S * beta ^ 2 / 2 * z ^ 2) *
          (1 - Real.exp ((1 - z) * (gamma * beta ^ 2 / 2 * z - a)))) := by
      rw [hexp]
      ring

theorem hardCentralQ_endpoint_nonneg
    {S v r B gamma a beta : ℝ}
    (hS : 0 < S) (hv : v = S * Real.exp (-a)) (hgamma : gamma = S - B)
    (hroot : r * beta = a + gamma * beta ^ 2 / 2)
    (ha : 0 < a) (hac : a < gamma * beta ^ 2 / 2)
    (hcd : gamma * beta ^ 2 / 2 < S * beta ^ 2 / 2)
    (hc2 : gamma * beta ^ 2 / 2 ≤ 2 * a)
    (hcertificate : a ^ 3 + (gamma * beta ^ 2 / 2) *
        (S * beta ^ 2 / 2) ^ 2 * Real.exp (S * beta ^ 2 / 2) ≤
      (2 * a - gamma * beta ^ 2 / 2) *
        (S * beta ^ 2 / 2 - gamma * beta ^ 2 / 2)) :
    0 ≤ hardCentralQ S v r B beta := by
  rw [hardCentralQ_endpoint_eq_singleCrossing hv hgamma hroot]
  exact mul_nonneg
    (mul_nonneg hS.le (sq_nonneg beta))
    (singleCrossing_integral_nonneg ha hac hcd hc2 hcertificate)

end SharpSerfling.Analysis
