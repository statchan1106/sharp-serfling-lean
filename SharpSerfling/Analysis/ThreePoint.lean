import SharpSerfling.Analysis.HermiteSign
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp

namespace SharpSerfling.Analysis

open Filter Topology

/-- The one-coordinate summand in the three-point extremal argument. -/
noncomputable def expPair (A B : ℝ) (x : ℝ) : ℝ :=
  A * Real.exp x + B * Real.exp (-x)

/-- First derivative of `expPair`. -/
noncomputable def expPairDeriv1 (A B : ℝ) (x : ℝ) : ℝ :=
  A * Real.exp x - B * Real.exp (-x)

theorem hasDerivAt_expPair (A B x : ℝ) :
    HasDerivAt (expPair A B) (expPairDeriv1 A B x) x := by
  have hp := (Real.hasDerivAt_exp x).const_mul A
  have hn := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).const_mul B
  convert hp.fun_add hn using 1
  all_goals first | rfl | (funext t; rfl) | (unfold expPairDeriv1; ring)

theorem hasDerivAt_expPairDeriv1 (A B x : ℝ) :
    HasDerivAt (expPairDeriv1 A B) (expPair A B x) x := by
  have hp := (Real.hasDerivAt_exp x).const_mul A
  have hn := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).const_mul B
  convert hp.fun_sub hn using 1
  all_goals first | rfl | (funext t; rfl) | (unfold expPair; ring)

theorem contDiff_expPair (A B : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (expPair A B) := by
  unfold expPair
  fun_prop

theorem contDiff_expPairDeriv1 (A B : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (expPairDeriv1 A B) := by
  unfold expPairDeriv1
  fun_prop

/-- A circle through `c+a` in the plane spanned by orthogonal vectors `a`
and `d` of the same squared length. -/
noncomputable def circleCoordinate (c a d : ℝ) (t : ℝ) : ℝ :=
  c + Real.cos t * a + Real.sin t * d

/-- First derivative of `circleCoordinate`. -/
noncomputable def circleCoordinateDeriv1 (a d : ℝ) (t : ℝ) : ℝ :=
  -Real.sin t * a + Real.cos t * d

/-- Second derivative of `circleCoordinate`. -/
noncomputable def circleCoordinateDeriv2 (a d : ℝ) (t : ℝ) : ℝ :=
  -Real.cos t * a - Real.sin t * d

theorem hasDerivAt_circleCoordinate (c a d t : ℝ) :
    HasDerivAt (circleCoordinate c a d) (circleCoordinateDeriv1 a d t) t := by
  have hc : HasDerivAt (fun _ : ℝ ↦ c) 0 t := hasDerivAt_const t c
  have hcos := (Real.hasDerivAt_cos t).mul_const a
  have hsin := (Real.hasDerivAt_sin t).mul_const d
  convert (hc.fun_add hcos).fun_add hsin using 1
  all_goals first | rfl | (funext u; rfl) |
    (unfold circleCoordinateDeriv1; ring)

theorem hasDerivAt_circleCoordinateDeriv1 (a d t : ℝ) :
    HasDerivAt (circleCoordinateDeriv1 a d) (circleCoordinateDeriv2 a d t) t := by
  have hsin := (Real.hasDerivAt_sin t).neg.mul_const a
  have hcos := (Real.hasDerivAt_cos t).mul_const d
  convert hsin.fun_add hcos using 1
  all_goals first | rfl | (funext u; rfl) |
    (unfold circleCoordinateDeriv2; ring)

/-- The objective restricted to the constraint-preserving circle. -/
noncomputable def threePointCurveObjective
    (A B c a₁ a₂ a₃ d₁ d₂ d₃ : ℝ) (t : ℝ) : ℝ :=
  expPair A B (circleCoordinate c a₁ d₁ t) +
    expPair A B (circleCoordinate c a₂ d₂ t) +
    expPair A B (circleCoordinate c a₃ d₃ t)

/-- Explicit first derivative along the circle. -/
noncomputable def threePointCurveDeriv1
    (A B c a₁ a₂ a₃ d₁ d₂ d₃ : ℝ) (t : ℝ) : ℝ :=
  expPairDeriv1 A B (circleCoordinate c a₁ d₁ t) *
      circleCoordinateDeriv1 a₁ d₁ t +
    expPairDeriv1 A B (circleCoordinate c a₂ d₂ t) *
      circleCoordinateDeriv1 a₂ d₂ t +
    expPairDeriv1 A B (circleCoordinate c a₃ d₃ t) *
      circleCoordinateDeriv1 a₃ d₃ t

/-- Explicit second derivative along the circle. -/
noncomputable def threePointCurveDeriv2
    (A B c a₁ a₂ a₃ d₁ d₂ d₃ : ℝ) (t : ℝ) : ℝ :=
  (expPair A B (circleCoordinate c a₁ d₁ t) *
        (circleCoordinateDeriv1 a₁ d₁ t) ^ 2 +
      expPairDeriv1 A B (circleCoordinate c a₁ d₁ t) *
        circleCoordinateDeriv2 a₁ d₁ t) +
    (expPair A B (circleCoordinate c a₂ d₂ t) *
        (circleCoordinateDeriv1 a₂ d₂ t) ^ 2 +
      expPairDeriv1 A B (circleCoordinate c a₂ d₂ t) *
        circleCoordinateDeriv2 a₂ d₂ t) +
    (expPair A B (circleCoordinate c a₃ d₃ t) *
        (circleCoordinateDeriv1 a₃ d₃ t) ^ 2 +
      expPairDeriv1 A B (circleCoordinate c a₃ d₃ t) *
        circleCoordinateDeriv2 a₃ d₃ t)

theorem hasDerivAt_threePointCurveObjective
    (A B c a₁ a₂ a₃ d₁ d₂ d₃ t : ℝ) :
    HasDerivAt (threePointCurveObjective A B c a₁ a₂ a₃ d₁ d₂ d₃)
      (threePointCurveDeriv1 A B c a₁ a₂ a₃ d₁ d₂ d₃ t) t := by
  have hterm (a d : ℝ) : HasDerivAt
      (fun u ↦ expPair A B (circleCoordinate c a d u))
      (expPairDeriv1 A B (circleCoordinate c a d t) *
        circleCoordinateDeriv1 a d t) t :=
    (hasDerivAt_expPair A B _).comp t (hasDerivAt_circleCoordinate c a d t)
  exact ((hterm a₁ d₁).fun_add (hterm a₂ d₂)).fun_add (hterm a₃ d₃)

theorem hasDerivAt_threePointCurveDeriv1
    (A B c a₁ a₂ a₃ d₁ d₂ d₃ t : ℝ) :
    HasDerivAt (threePointCurveDeriv1 A B c a₁ a₂ a₃ d₁ d₂ d₃)
      (threePointCurveDeriv2 A B c a₁ a₂ a₃ d₁ d₂ d₃ t) t := by
  have hterm (a d : ℝ) : HasDerivAt
      (fun u ↦ expPairDeriv1 A B (circleCoordinate c a d u) *
        circleCoordinateDeriv1 a d u)
      (expPair A B (circleCoordinate c a d t) *
          (circleCoordinateDeriv1 a d t) ^ 2 +
        expPairDeriv1 A B (circleCoordinate c a d t) *
          circleCoordinateDeriv2 a d t) t := by
    have hp := (hasDerivAt_expPairDeriv1 A B _).comp t
      (hasDerivAt_circleCoordinate c a d t)
    simpa only [pow_two, Function.comp_apply, mul_assoc] using
      hp.fun_mul (hasDerivAt_circleCoordinateDeriv1 a d t)
  exact ((hterm a₁ d₁).fun_add (hterm a₂ d₂)).fun_add (hterm a₃ d₃)

/-- A twice differentiable function that has a global maximum at zero has
nonpositive second derivative there. -/
theorem second_deriv_nonpos_of_global_max {g : ℝ → ℝ}
    (hmax : ∀ x, g x ≤ g 0) (hderiv : deriv g 0 = 0)
    (hcont : ContinuousAt g 0) :
    deriv (deriv g) 0 ≤ 0 := by
  by_contra hnot
  have hpos : 0 < deriv (deriv g) 0 := lt_of_not_ge hnot
  have hmin : IsLocalMin g 0 := isLocalMin_of_deriv_deriv_pos hpos hderiv hcont
  have heq : Filter.EventuallyEq (nhds 0) g (fun _ ↦ g 0) := by
    filter_upwards [hmin] with x hx
    exact le_antisymm (hmax x) hx
  have hderivEq : Filter.EventuallyEq (nhds 0) (deriv g)
      (deriv (fun _ : ℝ ↦ g 0)) := heq.deriv
  have hsecond : deriv (deriv g) 0 = deriv (deriv (fun _ : ℝ ↦ g 0)) 0 :=
    hderivEq.deriv_eq
  rw [deriv_const'] at hsecond
  norm_num at hsecond
  linarith

/-- Reciprocal derivative of the monic cubic at the node `x`. -/
noncomputable def cubicNodeWeight (x y z : ℝ) : ℝ :=
  1 / ((x - y) * (x - z))

theorem cubicNodeWeights_sum_eq_zero {x₁ x₂ x₃ : ℝ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    cubicNodeWeight x₁ x₂ x₃ + cubicNodeWeight x₂ x₁ x₃ +
      cubicNodeWeight x₃ x₁ x₂ = 0 := by
  unfold cubicNodeWeight
  field_simp [h12, h13, h23]
  ring

theorem cubicNodeWeights_linear_sum_eq_zero {x₁ x₂ x₃ : ℝ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    x₁ * cubicNodeWeight x₁ x₂ x₃ +
      x₂ * cubicNodeWeight x₂ x₁ x₃ +
      x₃ * cubicNodeWeight x₃ x₁ x₂ = 0 := by
  unfold cubicNodeWeight
  field_simp [h12, h13, h23]
  ring

/-- Three values whose divided-difference weight vanishes lie on an affine
function of their three distinct nodes. -/
theorem exists_affine_of_cubicNodeWeights_sum_eq_zero
    {x₁ x₂ x₃ y₁ y₂ y₃ : ℝ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (hweighted : y₁ * cubicNodeWeight x₁ x₂ x₃ +
      y₂ * cubicNodeWeight x₂ x₁ x₃ +
      y₃ * cubicNodeWeight x₃ x₁ x₂ = 0) :
    ∃ α β : ℝ, y₁ = α + β * x₁ ∧ y₂ = α + β * x₂ ∧
      y₃ = α + β * x₃ := by
  let β := (y₂ - y₁) / (x₂ - x₁)
  let α := y₁ - β * x₁
  refine ⟨α, β, ?_, ?_, ?_⟩
  · dsimp [α]
    ring
  · dsimp [α, β]
    field_simp [h12]
    ring
  · dsimp [α, β]
    have hrel : y₁ * (x₂ - x₃) - y₂ * (x₁ - x₃) +
        y₃ * (x₁ - x₂) = 0 := by
      calc
        _ = ((x₁ - x₂) * (x₁ - x₃) * (x₂ - x₃)) *
            (y₁ * cubicNodeWeight x₁ x₂ x₃ +
              y₂ * cubicNodeWeight x₂ x₁ x₃ +
              y₃ * cubicNodeWeight x₃ x₁ x₂) := by
          unfold cubicNodeWeight
          field_simp [h12, h13, h23]
          ring
        _ = 0 := by rw [hweighted]; ring
    field_simp [sub_ne_zero.mpr h12.symm]
    linear_combination -1 * hrel

theorem centered_three_sum (x₁ x₂ x₃ : ℝ) :
    (x₁ - (x₁ + x₂ + x₃) / 3) +
      (x₂ - (x₁ + x₂ + x₃) / 3) +
      (x₃ - (x₁ + x₂ + x₃) / 3) = 0 := by
  ring

theorem centered_cubicNodeWeights_inner_eq_zero {x₁ x₂ x₃ : ℝ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    (x₁ - (x₁ + x₂ + x₃) / 3) * cubicNodeWeight x₁ x₂ x₃ +
      (x₂ - (x₁ + x₂ + x₃) / 3) * cubicNodeWeight x₂ x₁ x₃ +
      (x₃ - (x₁ + x₂ + x₃) / 3) * cubicNodeWeight x₃ x₁ x₂ = 0 := by
  have hzero := cubicNodeWeights_sum_eq_zero h12 h13 h23
  have hlinear := cubicNodeWeights_linear_sum_eq_zero h12 h13 h23
  calc
    _ = (x₁ * cubicNodeWeight x₁ x₂ x₃ +
          x₂ * cubicNodeWeight x₂ x₁ x₃ +
          x₃ * cubicNodeWeight x₃ x₁ x₂) -
        ((x₁ + x₂ + x₃) / 3) *
          (cubicNodeWeight x₁ x₂ x₃ + cubicNodeWeight x₂ x₁ x₃ +
            cubicNodeWeight x₃ x₁ x₂) := by ring
    _ = 0 := by rw [hzero, hlinear]; ring

theorem centered_three_sq_pos_of_ne {x₁ x₂ x₃ : ℝ} (h12 : x₁ ≠ x₂) :
    0 < (x₁ - (x₁ + x₂ + x₃) / 3) ^ 2 +
      (x₂ - (x₁ + x₂ + x₃) / 3) ^ 2 +
      (x₃ - (x₁ + x₂ + x₃) / 3) ^ 2 := by
  have hs : 0 ≤ (x₃ - (x₁ + x₂ + x₃) / 3) ^ 2 := sq_nonneg _
  have hpair : 0 < (x₁ - (x₁ + x₂ + x₃) / 3) ^ 2 +
      (x₂ - (x₁ + x₂ + x₃) / 3) ^ 2 := by
    by_contra h
    have hle := le_of_not_gt h
    have hs1 := sq_nonneg (x₁ - (x₁ + x₂ + x₃) / 3)
    have hs2 := sq_nonneg (x₂ - (x₁ + x₂ + x₃) / 3)
    have hz1 : (x₁ - (x₁ + x₂ + x₃) / 3) ^ 2 = 0 := by linarith
    have hz2 : (x₂ - (x₁ + x₂ + x₃) / 3) ^ 2 = 0 := by linarith
    have h1 : x₁ - (x₁ + x₂ + x₃) / 3 = 0 := sq_eq_zero_iff.mp hz1
    have h2 : x₂ - (x₁ + x₂ + x₃) / 3 = 0 := sq_eq_zero_iff.mp hz2
    exact h12 (by linarith)
  linarith

theorem cubicNodeWeights_sq_sum_pos {x₁ x₂ x₃ : ℝ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) :
    0 < (cubicNodeWeight x₁ x₂ x₃) ^ 2 +
      (cubicNodeWeight x₂ x₁ x₃) ^ 2 +
      (cubicNodeWeight x₃ x₁ x₂) ^ 2 := by
  have hw : cubicNodeWeight x₁ x₂ x₃ ≠ 0 := by
    unfold cubicNodeWeight
    exact one_div_ne_zero (mul_ne_zero (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h13))
  have hpos : 0 < (cubicNodeWeight x₁ x₂ x₃) ^ 2 := sq_pos_of_ne_zero hw
  have h2 := sq_nonneg (cubicNodeWeight x₂ x₁ x₃)
  have h3 := sq_nonneg (cubicNodeWeight x₃ x₁ x₂)
  linarith

theorem circleCoordinates_sum_eq
    {c a₁ a₂ a₃ d₁ d₂ d₃ : ℝ}
    (ha : a₁ + a₂ + a₃ = 0) (hd : d₁ + d₂ + d₃ = 0) (t : ℝ) :
    circleCoordinate c a₁ d₁ t + circleCoordinate c a₂ d₂ t +
      circleCoordinate c a₃ d₃ t = 3 * c := by
  unfold circleCoordinate
  linear_combination Real.cos t * ha + Real.sin t * hd

theorem circleCoordinates_sq_sum_eq
    {c a₁ a₂ a₃ d₁ d₂ d₃ : ℝ}
    (ha : a₁ + a₂ + a₃ = 0) (hd : d₁ + d₂ + d₃ = 0)
    (had : a₁ * d₁ + a₂ * d₂ + a₃ * d₃ = 0)
    (hnorm : d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2 = a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2)
    (t : ℝ) :
    circleCoordinate c a₁ d₁ t ^ 2 + circleCoordinate c a₂ d₂ t ^ 2 +
      circleCoordinate c a₃ d₃ t ^ 2 =
      (c + a₁) ^ 2 + (c + a₂) ^ 2 + (c + a₃) ^ 2 := by
  unfold circleCoordinate
  have htrig := Real.cos_sq_add_sin_sq t
  calc
    _ = 3 * c ^ 2 + 2 * c * Real.cos t * (a₁ + a₂ + a₃) +
        2 * c * Real.sin t * (d₁ + d₂ + d₃) +
        Real.cos t ^ 2 * (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) +
        2 * Real.cos t * Real.sin t * (a₁ * d₁ + a₂ * d₂ + a₃ * d₃) +
        Real.sin t ^ 2 * (d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2) := by ring
    _ = 3 * c ^ 2 + (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) := by
      rw [ha, hd, had, hnorm]
      nlinarith
    _ = _ := by linear_combination -2 * c * ha

/-- The stationarity equation after subtracting its affine Lagrange part. -/
noncomputable def stationarityGap (A B α β : ℝ) (t : ℝ) : ℝ :=
  expPairDeriv1 A B t - α - β * t

theorem contDiff_stationarityGap (A B α β : ℝ) :
    ContDiff ℝ 5 (stationarityGap A B α β) := by
  unfold stationarityGap
  exact ((contDiff_expPairDeriv1 A B 5).sub contDiff_const).sub
    (contDiff_const.mul contDiff_id)

theorem hasDerivAt_stationarityGap (A B α β x : ℝ) :
    HasDerivAt (stationarityGap A B α β) (expPair A B x - β) x := by
  unfold stationarityGap
  convert ((hasDerivAt_expPairDeriv1 A B x).sub_const α).fun_sub
    ((hasDerivAt_const x β).fun_mul (hasDerivAt_id x)) using 1
  all_goals first | rfl | (funext t; rfl) | ring

theorem iteratedDeriv_five_affine (α β x : ℝ) :
    iteratedDeriv 5 (fun t : ℝ ↦ α + β * t) x = 0 := by
  have hc : ContDiffAt ℝ 5 (fun _ : ℝ ↦ α) x := by fun_prop
  have hl : ContDiffAt ℝ 5 (fun t : ℝ ↦ β * t) x := by fun_prop
  change iteratedDeriv 5 ((fun _ : ℝ ↦ α) + (fun t : ℝ ↦ β * t)) x = 0
  rw [iteratedDeriv_add hc hl, iteratedDeriv_const]
  rw [show (fun t : ℝ ↦ β * t) = β • id by rfl]
  rw [iteratedDeriv_const_smul
    (contDiff_id.contDiffAt : ContDiffAt ℝ 5 id x) β]
  simp [iteratedDeriv_id]

theorem iteratedDeriv_five_stationarityGap (A B α β x : ℝ) :
    iteratedDeriv 5 (stationarityGap A B α β) x = expPair A B x := by
  have hA : ContDiffAt ℝ 5 (fun t : ℝ ↦ A * Real.exp (1 * t)) x := by fun_prop
  have hB : ContDiffAt ℝ 5 (fun t : ℝ ↦ B * Real.exp ((-1) * t)) x := by fun_prop
  have hlin : ContDiffAt ℝ 5 (fun t : ℝ ↦ α + β * t) x := by fun_prop
  have hiA : iteratedDeriv 5 (fun t : ℝ ↦ A * Real.exp (1 * t)) x =
      A * Real.exp x := by
    rw [show (fun t : ℝ ↦ A * Real.exp (1 * t)) =
        A • (fun t : ℝ ↦ Real.exp (1 * t)) by rfl]
    rw [iteratedDeriv_const_smul
      (by fun_prop : ContDiffAt ℝ 5 (fun t : ℝ ↦ Real.exp (1 * t)) x) A]
    rw [congrFun (iteratedDeriv_exp_const_mul 5 1) x]
    norm_num [smul_eq_mul]
  have hiB : iteratedDeriv 5 (fun t : ℝ ↦ B * Real.exp ((-1) * t)) x =
      -B * Real.exp (-x) := by
    rw [show (fun t : ℝ ↦ B * Real.exp ((-1) * t)) =
        B • (fun t : ℝ ↦ Real.exp ((-1) * t)) by rfl]
    rw [iteratedDeriv_const_smul
      (by fun_prop : ContDiffAt ℝ 5 (fun t : ℝ ↦ Real.exp ((-1) * t)) x) B]
    rw [congrFun (iteratedDeriv_exp_const_mul 5 (-1)) x]
    norm_num [smul_eq_mul]
  rw [show stationarityGap A B α β =
      (fun t : ℝ ↦ A * Real.exp (1 * t)) -
        (fun t : ℝ ↦ B * Real.exp ((-1) * t)) -
        (fun t : ℝ ↦ α + β * t) by
    funext t
    unfold stationarityGap expPairDeriv1
    simp only [Pi.sub_apply]
    ring]
  change iteratedDeriv 5
      ((fun t : ℝ ↦ A * Real.exp (1 * t) - B * Real.exp ((-1) * t)) -
        (fun t : ℝ ↦ α + β * t)) x = _
  have hAB : ContDiffAt ℝ 5
      (fun t : ℝ ↦ A * Real.exp (1 * t) - B * Real.exp ((-1) * t)) x :=
    hA.sub hB
  rw [iteratedDeriv_sub hAB hlin]
  have hin := iteratedDeriv_sub hA hB
  change iteratedDeriv 5
      (fun t : ℝ ↦ A * Real.exp (1 * t) - B * Real.exp ((-1) * t)) x =
    iteratedDeriv 5 (fun t : ℝ ↦ A * Real.exp (1 * t)) x -
      iteratedDeriv 5 (fun t : ℝ ↦ B * Real.exp ((-1) * t)) x at hin
  rw [hin, hiA, hiB, iteratedDeriv_five_affine]
  unfold expPair
  ring

/-- The strict part of the three-coordinate sphere lemma: when the radius is
nonzero, a point with three distinct coordinates cannot maximize the symmetric
two-sided exponential objective.  This is the analytic core of Lemma 3 in the
cited proof. -/
theorem three_distinct_not_globalMax
    {A B x₁ x₂ x₃ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B)
    (h12 : x₁ < x₂) (h23 : x₂ < x₃)
    (hmax : ∀ u v z : ℝ,
      u + v + z = x₁ + x₂ + x₃ →
      u ^ 2 + v ^ 2 + z ^ 2 = x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 →
      expPair A B u + expPair A B v + expPair A B z ≤
        expPair A B x₁ + expPair A B x₂ + expPair A B x₃) : False := by
  have h12ne : x₁ ≠ x₂ := h12.ne
  have h13ne : x₁ ≠ x₃ := (h12.trans h23).ne
  have h23ne : x₂ ≠ x₃ := h23.ne
  let c := (x₁ + x₂ + x₃) / 3
  let a₁ := x₁ - c
  let a₂ := x₂ - c
  let a₃ := x₃ - c
  let e₁ := cubicNodeWeight x₁ x₂ x₃
  let e₂ := cubicNodeWeight x₂ x₁ x₃
  let e₃ := cubicNodeWeight x₃ x₁ x₂
  let R := a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2
  let E := e₁ ^ 2 + e₂ ^ 2 + e₃ ^ 2
  let L := Real.sqrt (R / E)
  let d₁ := L * e₁
  let d₂ := L * e₂
  let d₃ := L * e₃
  have ha : a₁ + a₂ + a₃ = 0 := by
    dsimp [a₁, a₂, a₃, c]
    exact centered_three_sum x₁ x₂ x₃
  have he : e₁ + e₂ + e₃ = 0 := by
    dsimp [e₁, e₂, e₃]
    exact cubicNodeWeights_sum_eq_zero h12ne h13ne h23ne
  have hae : a₁ * e₁ + a₂ * e₂ + a₃ * e₃ = 0 := by
    dsimp [a₁, a₂, a₃, c, e₁, e₂, e₃]
    exact centered_cubicNodeWeights_inner_eq_zero h12ne h13ne h23ne
  have hRpos : 0 < R := by
    dsimp [R, a₁, a₂, a₃, c]
    exact centered_three_sq_pos_of_ne h12ne
  have hEpos : 0 < E := by
    dsimp [E, e₁, e₂, e₃]
    exact cubicNodeWeights_sq_sum_pos h12ne h13ne
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.sqrt_pos.mpr (div_pos hRpos hEpos)
  have hLsq : L ^ 2 = R / E := by
    dsimp [L]
    exact Real.sq_sqrt (le_of_lt (div_pos hRpos hEpos))
  have hd : d₁ + d₂ + d₃ = 0 := by
    dsimp [d₁, d₂, d₃]
    linear_combination L * he
  have had : a₁ * d₁ + a₂ * d₂ + a₃ * d₃ = 0 := by
    dsimp [d₁, d₂, d₃]
    linear_combination L * hae
  have hnorm : d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2 =
      a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 := by
    calc
      _ = L ^ 2 * E := by dsimp [d₁, d₂, d₃, E]; ring
      _ = R := by rw [hLsq]; field_simp [hEpos.ne']
      _ = _ := by rfl
  let g := threePointCurveObjective A B c a₁ a₂ a₃ d₁ d₂ d₃
  have hglobal : ∀ t : ℝ, g t ≤ g 0 := by
    intro t
    have hsum := circleCoordinates_sum_eq (c := c) ha hd t
    have hsq := circleCoordinates_sq_sum_eq (c := c) ha hd had hnorm t
    have hsum' : circleCoordinate c a₁ d₁ t + circleCoordinate c a₂ d₂ t +
        circleCoordinate c a₃ d₃ t = x₁ + x₂ + x₃ := by
      rw [hsum]
      dsimp [c]
      ring
    have hsq' : circleCoordinate c a₁ d₁ t ^ 2 +
        circleCoordinate c a₂ d₂ t ^ 2 + circleCoordinate c a₃ d₃ t ^ 2 =
        x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 := by
      rw [hsq]
      dsimp [a₁, a₂, a₃]
      ring
    have hm := hmax (circleCoordinate c a₁ d₁ t)
      (circleCoordinate c a₂ d₂ t) (circleCoordinate c a₃ d₃ t) hsum' hsq'
    change threePointCurveObjective A B c a₁ a₂ a₃ d₁ d₂ d₃ t ≤ g 0
    rw [show g 0 = expPair A B x₁ + expPair A B x₂ + expPair A B x₃ by
      simp [g, threePointCurveObjective, circleCoordinate, a₁, a₂, a₃]]
    exact hm
  have hg0 := hasDerivAt_threePointCurveObjective
    A B c a₁ a₂ a₃ d₁ d₂ d₃ 0
  have hlocal : IsLocalMax g 0 := Filter.Eventually.of_forall hglobal
  have hfirst : threePointCurveDeriv1 A B c a₁ a₂ a₃ d₁ d₂ d₃ 0 = 0 := by
    exact hlocal.hasDerivAt_eq_zero hg0
  have hweighted :
      expPairDeriv1 A B x₁ * e₁ + expPairDeriv1 A B x₂ * e₂ +
        expPairDeriv1 A B x₃ * e₃ = 0 := by
    have hfactor : L *
        (expPairDeriv1 A B x₁ * e₁ + expPairDeriv1 A B x₂ * e₂ +
          expPairDeriv1 A B x₃ * e₃) = 0 := by
      convert hfirst using 1
      simp [threePointCurveDeriv1, circleCoordinate, circleCoordinateDeriv1,
        a₁, a₂, a₃, d₁, d₂, d₃]
      ring
    exact (mul_eq_zero.mp hfactor).resolve_left hLpos.ne'
  obtain ⟨α, β, hline1, hline2, hline3⟩ :=
    exists_affine_of_cubicNodeWeights_sum_eq_zero h12ne h13ne h23ne hweighted
  have hgDeriv : deriv g =
      threePointCurveDeriv1 A B c a₁ a₂ a₃ d₁ d₂ d₃ := by
    funext t
    exact (hasDerivAt_threePointCurveObjective
      A B c a₁ a₂ a₃ d₁ d₂ d₃ t).deriv
  have hsecondRaw : deriv (deriv g) 0 ≤ 0 :=
    second_deriv_nonpos_of_global_max hglobal (hg0.deriv.trans hfirst) hg0.continuousAt
  have hsecond : threePointCurveDeriv2 A B c a₁ a₂ a₃ d₁ d₂ d₃ 0 ≤ 0 := by
    rw [hgDeriv] at hsecondRaw
    rw [(hasDerivAt_threePointCurveDeriv1
      A B c a₁ a₂ a₃ d₁ d₂ d₃ 0).deriv] at hsecondRaw
    exact hsecondRaw
  have hweightedNonpos :
      (expPair A B x₁ - β) * e₁ ^ 2 +
        (expPair A B x₂ - β) * e₂ ^ 2 +
        (expPair A B x₃ - β) * e₃ ^ 2 ≤ 0 := by
    have hsumAffine :
        expPairDeriv1 A B x₁ * a₁ + expPairDeriv1 A B x₂ * a₂ +
          expPairDeriv1 A B x₃ * a₃ = β * R := by
      rw [hline1, hline2, hline3]
      have hxa : x₁ * a₁ + x₂ * a₂ + x₃ * a₃ = R := by
        dsimp [a₁, a₂, a₃, R]
        dsimp [c]
        ring
      linear_combination α * ha + β * hxa
    have hsecond' :
        L ^ 2 * (expPair A B x₁ * e₁ ^ 2 + expPair A B x₂ * e₂ ^ 2 +
          expPair A B x₃ * e₃ ^ 2) - β * R ≤ 0 := by
      have hca1 : c + a₁ = x₁ := by dsimp [a₁]; ring
      have hca2 : c + a₂ = x₂ := by dsimp [a₂]; ring
      have hca3 : c + a₃ = x₃ := by dsimp [a₃]; ring
      have hvalue : threePointCurveDeriv2 A B c a₁ a₂ a₃ d₁ d₂ d₃ 0 =
          L ^ 2 * (expPair A B x₁ * e₁ ^ 2 + expPair A B x₂ * e₂ ^ 2 +
            expPair A B x₃ * e₃ ^ 2) -
            (expPairDeriv1 A B x₁ * a₁ + expPairDeriv1 A B x₂ * a₂ +
              expPairDeriv1 A B x₃ * a₃) := by
        simp [threePointCurveDeriv2, circleCoordinate, circleCoordinateDeriv1,
          circleCoordinateDeriv2, hca1, hca2, hca3, d₁, d₂, d₃]
        ring
      rw [hvalue] at hsecond
      rw [hsumAffine] at hsecond
      exact hsecond
    have hLE : L ^ 2 * E = R := by
      rw [hLsq]
      field_simp [hEpos.ne']
    have hfactor : L ^ 2 *
        ((expPair A B x₁ - β) * e₁ ^ 2 +
          (expPair A B x₂ - β) * e₂ ^ 2 +
          (expPair A B x₃ - β) * e₃ ^ 2) ≤ 0 := by
      calc
        _ = L ^ 2 * (expPair A B x₁ * e₁ ^ 2 +
              expPair A B x₂ * e₂ ^ 2 + expPair A B x₃ * e₃ ^ 2) -
            β * R := by rw [← hLE]; dsimp [E]; ring
        _ ≤ 0 := hsecond'
    exact nonpos_of_mul_nonpos_right hfactor (sq_pos_of_pos hLpos)
  let h := stationarityGap A B α β
  have hh : ContDiff ℝ 5 h := contDiff_stationarityGap A B α β
  have hz1 : h x₁ = 0 := by dsimp [h, stationarityGap]; linarith
  have hz2 : h x₂ = 0 := by dsimp [h, stationarityGap]; linarith
  have hz3 : h x₃ = 0 := by dsimp [h, stationarityGap]; linarith
  have hfive : ∀ x : ℝ, 0 < iteratedDeriv 5 h x := by
    intro x
    rw [show iteratedDeriv 5 h x = expPair A B x by
      exact iteratedDeriv_five_stationarityGap A B α β x]
    unfold expPair
    have hex := Real.exp_pos x
    have hneg := Real.exp_pos (-x)
    by_cases hAz : A = 0
    · subst A
      have hBp : 0 < B := by simpa using hAB
      simpa using mul_pos hBp hneg
    · have hAp : 0 < A := lt_of_le_of_ne hA (fun hz ↦ hAz hz.symm)
      exact add_pos_of_pos_of_nonneg (mul_pos hAp hex) (mul_nonneg hB hneg.le)
  have hHermite := hermite_weighted_deriv_pos hh h12 h23 hz1 hz2 hz3 hfive
  have hd1 : deriv h x₁ = expPair A B x₁ - β :=
    (hasDerivAt_stationarityGap A B α β x₁).deriv
  have hd2 : deriv h x₂ = expPair A B x₂ - β :=
    (hasDerivAt_stationarityGap A B α β x₂).deriv
  have hd3 : deriv h x₃ = expPair A B x₃ - β :=
    (hasDerivAt_stationarityGap A B α β x₃).deriv
  rw [hd1, hd2, hd3] at hHermite
  have hpos : 0 <
      (expPair A B x₁ - β) * e₁ ^ 2 +
        (expPair A B x₂ - β) * e₂ ^ 2 +
        (expPair A B x₃ - β) * e₃ ^ 2 := by
    dsimp [e₁, e₂, e₃, cubicNodeWeight]
    rw [one_div_pow, one_div_pow, one_div_pow]
    simpa only [div_eq_mul_inv, one_mul] using hHermite
  linarith

/-- Order-free form of the strict three-point lemma. -/
theorem three_pairwiseDistinct_not_globalMax
    {A B x₁ x₂ x₃ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B)
    (h12ne : x₁ ≠ x₂) (h13ne : x₁ ≠ x₃) (h23ne : x₂ ≠ x₃)
    (hmax : ∀ u v z : ℝ,
      u + v + z = x₁ + x₂ + x₃ →
      u ^ 2 + v ^ 2 + z ^ 2 = x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 →
      expPair A B u + expPair A B v + expPair A B z ≤
        expPair A B x₁ + expPair A B x₂ + expPair A B x₃) : False := by
  have hordered (y₁ y₂ y₃ : ℝ) (hy12 : y₁ < y₂) (hy23 : y₂ < y₃)
      (hsum : y₁ + y₂ + y₃ = x₁ + x₂ + x₃)
      (hsq : y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 = x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)
      (hobj : expPair A B y₁ + expPair A B y₂ + expPair A B y₃ =
        expPair A B x₁ + expPair A B x₂ + expPair A B x₃) : False := by
    apply three_distinct_not_globalMax hA hB hAB hy12 hy23
    intro u v z hu hq
    rw [hobj]
    exact hmax u v z (hu.trans hsum) (hq.trans hsq)
  rcases lt_or_gt_of_ne h12ne with h12 | h21
  · rcases lt_or_gt_of_ne h13ne with h13 | h31
    · rcases lt_or_gt_of_ne h23ne with h23 | h32
      · exact hordered x₁ x₂ x₃ h12 h23 (by ring) (by ring) (by ring)
      · exact hordered x₁ x₃ x₂ h13 h32 (by ring) (by ring) (by ring)
    · exact hordered x₃ x₁ x₂ h31 h12 (by ring) (by ring) (by ring)
  · rcases lt_or_gt_of_ne h13ne with h13 | h31
    · exact hordered x₂ x₁ x₃ h21 h13 (by ring) (by ring) (by ring)
    · rcases lt_or_gt_of_ne h23ne with h23 | h32
      · exact hordered x₂ x₃ x₁ h23 h31 (by ring) (by ring) (by ring)
      · exact hordered x₃ x₂ x₁ h32 h21 (by ring) (by ring) (by ring)

/-- Every global maximizer of the three-coordinate exponential objective on
its fixed-sum, fixed-square section has a repeated coordinate. -/
theorem threePoint_globalMax_has_duplicate
    {A B x₁ x₂ x₃ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B)
    (hmax : ∀ u v z : ℝ,
      u + v + z = x₁ + x₂ + x₃ →
      u ^ 2 + v ^ 2 + z ^ 2 = x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 →
      expPair A B u + expPair A B v + expPair A B z ≤
        expPair A B x₁ + expPair A B x₂ + expPair A B x₃) :
    x₁ = x₂ ∨ x₁ = x₃ ∨ x₂ = x₃ := by
  by_contra hdistinct
  push_neg at hdistinct
  exact three_pairwiseDistinct_not_globalMax hA hB hAB
    hdistinct.1 hdistinct.2.1 hdistinct.2.2 hmax

end SharpSerfling.Analysis
