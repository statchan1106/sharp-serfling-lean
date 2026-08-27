import SharpSerfling.Analysis.HermiteRolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.FunProp

namespace SharpSerfling.Analysis

open Polynomial

/-- One basis term in the order-one Hermite interpolant at three nodes. -/
noncomputable def hermiteTerm3 (x y z c : ℝ) (t : ℝ) : ℝ :=
  c * (t - x) * (((t - y) * (t - z)) / ((x - y) * (x - z))) ^ 2

/-- The degree-five Hermite interpolant matching zero values and prescribed
first derivatives at three nodes. -/
noncomputable def hermiteInterpolant3
    (x₁ x₂ x₃ c₁ c₂ c₃ : ℝ) (t : ℝ) : ℝ :=
  hermiteTerm3 x₁ x₂ x₃ c₁ t +
    hermiteTerm3 x₂ x₁ x₃ c₂ t +
    hermiteTerm3 x₃ x₁ x₂ c₃ t

theorem contDiff_hermiteTerm3 (x y z c : ℝ) :
    ContDiff ℝ 5 (hermiteTerm3 x y z c) := by
  unfold hermiteTerm3
  fun_prop

theorem contDiff_hermiteInterpolant3 (x₁ x₂ x₃ c₁ c₂ c₃ : ℝ) :
    ContDiff ℝ 5 (hermiteInterpolant3 x₁ x₂ x₃ c₁ c₂ c₃) := by
  unfold hermiteInterpolant3
  exact ((contDiff_hermiteTerm3 x₁ x₂ x₃ c₁).add
    (contDiff_hermiteTerm3 x₂ x₁ x₃ c₂)).add
      (contDiff_hermiteTerm3 x₃ x₁ x₂ c₃)

theorem hasDerivAt_hermiteTerm3 (x y z c u : ℝ) :
    HasDerivAt (hermiteTerm3 x y z c)
      (c * (((u - y) * (u - z)) / ((x - y) * (x - z))) ^ 2 +
        c * (u - x) *
          (2 * (((u - y) * (u - z)) / ((x - y) * (x - z))) *
            (((u - z) + (u - y)) / ((x - y) * (x - z))))) u := by
  have hnum : HasDerivAt (fun t : ℝ ↦ (t - y) * (t - z))
      ((u - z) + (u - y)) u := by
    convert ((hasDerivAt_id u).sub_const y).mul
      ((hasDerivAt_id u).sub_const z) using 1
    all_goals first | rfl | (funext t; simp [pow_two]) | (simp [id_eq, pow_two] <;> ring)
  have hquot : HasDerivAt
      (fun t : ℝ ↦ ((t - y) * (t - z)) / ((x - y) * (x - z)))
      (((u - z) + (u - y)) / ((x - y) * (x - z))) u := hnum.div_const _
  have hlinear : HasDerivAt (fun t : ℝ ↦ c * (t - x)) c u := by
    convert (hasDerivAt_const u c).mul ((hasDerivAt_id u).sub_const x) using 1
    all_goals first | rfl | (funext t; rfl) | (simp [id_eq] <;> ring)
  have hsquare : HasDerivAt
      (fun t : ℝ ↦ (((t - y) * (t - z)) / ((x - y) * (x - z))) ^ 2)
      (2 * (((u - y) * (u - z)) / ((x - y) * (x - z))) *
        (((u - z) + (u - y)) / ((x - y) * (x - z)))) u := by
    convert hquot.mul hquot using 1
    all_goals try rfl
    · funext t
      rw [pow_two]
      rfl
    · ring
  unfold hermiteTerm3
  convert hlinear.mul hsquare using 1
  all_goals first | rfl | (funext t; simp [pow_two]) | (simp [id_eq, pow_two] <;> ring)

theorem hasDerivAt_hermiteTerm3_self {x y z c : ℝ}
    (hxy : x ≠ y) (hxz : x ≠ z) :
    HasDerivAt (hermiteTerm3 x y z c) c x := by
  have hD : (x-y)*(x-z) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hxz)
  convert hasDerivAt_hermiteTerm3 x y z c x using 1
  all_goals first | rfl | (funext t; rfl) | (simp [hD] <;> ring)

theorem hasDerivAt_hermiteTerm3_second (x y z c : ℝ) :
    HasDerivAt (hermiteTerm3 x y z c) 0 y := by
  convert hasDerivAt_hermiteTerm3 x y z c y using 1
  all_goals first | rfl | (funext t; rfl) | simp

theorem hasDerivAt_hermiteTerm3_third (x y z c : ℝ) :
    HasDerivAt (hermiteTerm3 x y z c) 0 z := by
  convert hasDerivAt_hermiteTerm3 x y z c z using 1
  all_goals first | rfl | (funext t; rfl) | simp

theorem hermiteInterpolant3_value_one {x₁ x₂ x₃ c₁ c₂ c₃ : ℝ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    hermiteInterpolant3 x₁ x₂ x₃ c₁ c₂ c₃ x₁ = 0 := by
  unfold hermiteInterpolant3 hermiteTerm3
  field_simp [h12, h13, h23]
  ring

theorem hermiteInterpolant3_value_two {x₁ x₂ x₃ c₁ c₂ c₃ : ℝ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    hermiteInterpolant3 x₁ x₂ x₃ c₁ c₂ c₃ x₂ = 0 := by
  unfold hermiteInterpolant3 hermiteTerm3
  field_simp [h12, h13, h23]
  ring

theorem hermiteInterpolant3_value_three {x₁ x₂ x₃ c₁ c₂ c₃ : ℝ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    hermiteInterpolant3 x₁ x₂ x₃ c₁ c₂ c₃ x₃ = 0 := by
  unfold hermiteInterpolant3 hermiteTerm3
  field_simp [h12, h13, h23]
  ring

theorem hasDerivAt_hermiteInterpolant3_one {x₁ x₂ x₃ c₁ c₂ c₃ : ℝ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    HasDerivAt (hermiteInterpolant3 x₁ x₂ x₃ c₁ c₂ c₃) c₁ x₁ := by
  unfold hermiteInterpolant3
  convert ((hasDerivAt_hermiteTerm3_self h12 h13).add
    (hasDerivAt_hermiteTerm3_second x₂ x₁ x₃ c₂)).add
      (hasDerivAt_hermiteTerm3_second x₃ x₁ x₂ c₃) using 1
  all_goals first | rfl | (funext t; rfl) | simp

theorem hasDerivAt_hermiteInterpolant3_two {x₁ x₂ x₃ c₁ c₂ c₃ : ℝ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    HasDerivAt (hermiteInterpolant3 x₁ x₂ x₃ c₁ c₂ c₃) c₂ x₂ := by
  unfold hermiteInterpolant3
  convert ((hasDerivAt_hermiteTerm3_second x₁ x₂ x₃ c₁).add
    (hasDerivAt_hermiteTerm3_self h12.symm h23)).add
      (hasDerivAt_hermiteTerm3_third x₃ x₁ x₂ c₃) using 1
  all_goals first | rfl | (funext t; rfl) | simp

theorem hasDerivAt_hermiteInterpolant3_three {x₁ x₂ x₃ c₁ c₂ c₃ : ℝ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    HasDerivAt (hermiteInterpolant3 x₁ x₂ x₃ c₁ c₂ c₃) c₃ x₃ := by
  unfold hermiteInterpolant3
  convert ((hasDerivAt_hermiteTerm3_third x₁ x₂ x₃ c₁).add
    (hasDerivAt_hermiteTerm3_third x₂ x₁ x₃ c₂)).add
      (hasDerivAt_hermiteTerm3_self h13.symm h23.symm) using 1
  all_goals first | rfl | (funext t; rfl) | simp

/-- Analytic iterated differentiation of a polynomial evaluation agrees with
algebraic iteration of `Polynomial.derivative`. -/
theorem iteratedDeriv_polynomial_eval (n : ℕ) (p : ℝ[X]) :
    iteratedDeriv n (fun x : ℝ ↦ p.eval x) =
      fun x ↦ (Polynomial.derivative^[n] p).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      rw [Polynomial.deriv]
      simp only [Function.iterate_succ_apply']

/-- The fifth derivative of a quintic written as a product of five linear
factors is `5!` times its leading coefficient. -/
theorem iteratedDeriv_five_quintic_product (c x y z u : ℝ) :
    iteratedDeriv 5 (fun t : ℝ ↦ c * (t - x) * (t - y) ^ 2 * (t - z) ^ 2) u =
      120 * c := by
  let Q : ℝ[X] := (X-C x) * (X-C y)^2 * (X-C z)^2
  let P : ℝ[X] := C c * Q
  have hA : (X-C x : ℝ[X]).Monic := monic_X_sub_C x
  have hB : ((X-C y : ℝ[X])^2).Monic := (monic_X_sub_C y).pow 2
  have hC : ((X-C z : ℝ[X])^2).Monic := (monic_X_sub_C z).pow 2
  have hQmonic : Q.Monic := (hA.mul hB).mul hC
  have hQdeg : Q.natDegree = 5 := by
    rw [(hA.mul hB).natDegree_mul hC, hA.natDegree_mul hB]
    simp [natDegree_pow]
  have hder : Polynomial.derivative^[5] P = C (120*c) := by
    ext n
    rw [coeff_iterate_derivative]
    by_cases hn : n = 0
    · subst n
      norm_num
      rw [show P = C c * Q by rfl, coeff_C_mul, ← hQdeg,
        hQmonic.coeff_natDegree]
      norm_num
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hzero : Q.coeff (n+5) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        omega
      rw [show P = C c * Q by rfl, coeff_C_mul, hzero]
      simp only [mul_zero, smul_zero, coeff_C]
      simp [hn]
  rw [show (fun t : ℝ ↦ c * (t-x) * (t-y)^2 * (t-z)^2) =
      fun t ↦ P.eval t by
    funext t
    simp [P, Q]
    ring]
  rw [congrFun (iteratedDeriv_polynomial_eval 5 P) u, hder]
  simp

theorem iteratedDeriv_five_hermiteTerm3 {x y z c u : ℝ}
    (hxy : x ≠ y) (hxz : x ≠ z) :
    iteratedDeriv 5 (hermiteTerm3 x y z c) u =
      120 * c / (((x - y) * (x - z)) ^ 2) := by
  rw [show hermiteTerm3 x y z c =
      fun t : ℝ ↦ (c / (((x-y)*(x-z))^2)) * (t-x) * (t-y)^2 * (t-z)^2 by
    funext t
    unfold hermiteTerm3
    field_simp [hxy, hxz] <;> ring]
  rw [iteratedDeriv_five_quintic_product]
  ring

theorem iteratedDeriv_five_hermiteInterpolant3
    {x₁ x₂ x₃ c₁ c₂ c₃ u : ℝ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    iteratedDeriv 5 (hermiteInterpolant3 x₁ x₂ x₃ c₁ c₂ c₃) u =
      120 * (c₁ / (((x₁-x₂)*(x₁-x₃))^2) +
        c₂ / (((x₂-x₁)*(x₂-x₃))^2) +
        c₃ / (((x₃-x₁)*(x₃-x₂))^2)) := by
  have h1 : ContDiffAt ℝ 5 (hermiteTerm3 x₁ x₂ x₃ c₁) u :=
    (contDiff_hermiteTerm3 x₁ x₂ x₃ c₁).contDiffAt
  have h2 : ContDiffAt ℝ 5 (hermiteTerm3 x₂ x₁ x₃ c₂) u :=
    (contDiff_hermiteTerm3 x₂ x₁ x₃ c₂).contDiffAt
  have h3 : ContDiffAt ℝ 5 (hermiteTerm3 x₃ x₁ x₂ c₃) u :=
    (contDiff_hermiteTerm3 x₃ x₁ x₂ c₃).contDiffAt
  unfold hermiteInterpolant3
  change iteratedDeriv 5
      ((hermiteTerm3 x₁ x₂ x₃ c₁ + hermiteTerm3 x₂ x₁ x₃ c₂) +
        hermiteTerm3 x₃ x₁ x₂ c₃) u = _
  have houter : iteratedDeriv 5
      ((hermiteTerm3 x₁ x₂ x₃ c₁ + hermiteTerm3 x₂ x₁ x₃ c₂) +
        hermiteTerm3 x₃ x₁ x₂ c₃) u =
      iteratedDeriv 5 (hermiteTerm3 x₁ x₂ x₃ c₁ +
        hermiteTerm3 x₂ x₁ x₃ c₂) u +
      iteratedDeriv 5 (hermiteTerm3 x₃ x₁ x₂ c₃) u := by
    convert iteratedDeriv_add (h1.add h2) h3 using 1
    all_goals first | rfl | (funext t; rfl)
  have hinner : iteratedDeriv 5
      (hermiteTerm3 x₁ x₂ x₃ c₁ + hermiteTerm3 x₂ x₁ x₃ c₂) u =
      iteratedDeriv 5 (hermiteTerm3 x₁ x₂ x₃ c₁) u +
        iteratedDeriv 5 (hermiteTerm3 x₂ x₁ x₃ c₂) u := by
    convert iteratedDeriv_add h1 h2 using 1
    all_goals first | rfl | (funext t; rfl)
  rw [houter, hinner,
    iteratedDeriv_five_hermiteTerm3 h12 h13,
    iteratedDeriv_five_hermiteTerm3 h12.symm h23,
    iteratedDeriv_five_hermiteTerm3 h13.symm h23.symm]
  ring

/-- Hermite interpolation sign lemma used by the three-coordinate extremal
argument.  This is Lemma 2 in the cited two-level reduction proof. -/
theorem hermite_weighted_deriv_pos {h : ℝ → ℝ} (hh : ContDiff ℝ 5 h)
    {x₁ x₂ x₃ : ℝ} (h12 : x₁ < x₂) (h23 : x₂ < x₃)
    (hz1 : h x₁ = 0) (hz2 : h x₂ = 0) (hz3 : h x₃ = 0)
    (hfive : ∀ x, 0 < iteratedDeriv 5 h x) :
    0 < deriv h x₁ / (((x₁-x₂)*(x₁-x₃))^2) +
      deriv h x₂ / (((x₂-x₁)*(x₂-x₃))^2) +
      deriv h x₃ / (((x₃-x₁)*(x₃-x₂))^2) := by
  let H := hermiteInterpolant3 x₁ x₂ x₃ (deriv h x₁) (deriv h x₂) (deriv h x₃)
  let r := h - H
  have h12ne : x₁ ≠ x₂ := h12.ne
  have h13ne : x₁ ≠ x₃ := (h12.trans h23).ne
  have h23ne : x₂ ≠ x₃ := h23.ne
  have hH : ContDiff ℝ 5 H := contDiff_hermiteInterpolant3 _ _ _ _ _ _
  have hr : ContDiff ℝ 5 r := hh.sub hH
  have hr1 : r x₁ = 0 := by
    rw [show r x₁ = h x₁ - H x₁ by rfl, hz1,
      show H x₁ = 0 by exact hermiteInterpolant3_value_one h12ne h13ne h23ne]
    ring
  have hr2 : r x₂ = 0 := by
    rw [show r x₂ = h x₂ - H x₂ by rfl, hz2,
      show H x₂ = 0 by exact hermiteInterpolant3_value_two h12ne h13ne h23ne]
    ring
  have hr3 : r x₃ = 0 := by
    rw [show r x₃ = h x₃ - H x₃ by rfl, hz3,
      show H x₃ = 0 by exact hermiteInterpolant3_value_three h12ne h13ne h23ne]
    ring
  have hdr1 : iteratedDeriv 1 r x₁ = 0 := by
    have hdH : HasDerivAt H (deriv h x₁) x₁ :=
      hasDerivAt_hermiteInterpolant3_one h12ne h13ne h23ne
    have hdh : HasDerivAt h (deriv h x₁) x₁ :=
      (hh.differentiable (by norm_num) x₁).hasDerivAt
    rw [iteratedDeriv_succ, iteratedDeriv_zero]
    change deriv (h - H) x₁ = 0
    rw [(hdh.sub hdH).deriv, sub_self]
  have hdr2 : iteratedDeriv 1 r x₂ = 0 := by
    have hdH : HasDerivAt H (deriv h x₂) x₂ :=
      hasDerivAt_hermiteInterpolant3_two h12ne h13ne h23ne
    have hdh : HasDerivAt h (deriv h x₂) x₂ :=
      (hh.differentiable (by norm_num) x₂).hasDerivAt
    rw [iteratedDeriv_succ, iteratedDeriv_zero]
    change deriv (h - H) x₂ = 0
    rw [(hdh.sub hdH).deriv, sub_self]
  have hdr3 : iteratedDeriv 1 r x₃ = 0 := by
    have hdH : HasDerivAt H (deriv h x₃) x₃ :=
      hasDerivAt_hermiteInterpolant3_three h12ne h13ne h23ne
    have hdh : HasDerivAt h (deriv h x₃) x₃ :=
      (hh.differentiable (by norm_num) x₃).hasDerivAt
    rw [iteratedDeriv_succ, iteratedDeriv_zero]
    change deriv (h - H) x₃ = 0
    rw [(hdh.sub hdH).deriv, sub_self]
  obtain ⟨ξ, hξI, hξ⟩ :=
    exists_iteratedDeriv_five_eq_zero_of_three_double_roots hr h12 h23
      hr1 hr2 hr3 hdr1 hdr2 hdr3
  have hsplit : iteratedDeriv 5 r ξ =
      iteratedDeriv 5 h ξ - iteratedDeriv 5 H ξ := by
    exact iteratedDeriv_sub hh.contDiffAt hH.contDiffAt
  rw [hsplit, iteratedDeriv_five_hermiteInterpolant3 h12ne h13ne h23ne] at hξ
  have hp := hfive ξ
  nlinarith

end SharpSerfling.Analysis
