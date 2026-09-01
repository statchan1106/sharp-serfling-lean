import SharpSerfling.Hypergeometric.Representation
import SharpSerfling.Hypergeometric.Derivative
import SharpSerfling.Hypergeometric.Symmetries
import SharpSerfling.FiniteHoeffding
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace SharpSerfling.Hypergeometric

/-- Normalised success imbalance used in the universal derivative comparison. -/
noncomputable def imbalance (N K : ℕ) : ℝ :=
  |(N : ℝ) - 2 * (K : ℝ)| / (N : ℝ)

/-- Sample-size contribution to the linear tilt in the universal proof. -/
noncomputable def sampleTilt (N m : ℕ) : ℝ :=
  ((N : ℝ) - 2 * (m : ℝ)) / (2 * ((N : ℝ) - 2))

theorem one_sub_sq_le_exp_neg_sq (x : ℝ) :
    1 - x ^ 2 ≤ Real.exp (-x ^ 2) := by
  simpa only [neg_sq, sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-x ^ 2)

theorem neg_sq_add_mul_le_quarter_sq (x c t : ℝ) :
    -x ^ 2 + c * x * t ≤ c ^ 2 * t ^ 2 / 4 := by
  nlinarith [sq_nonneg (x - c * t / 2)]

theorem imbalance_nonneg (N K : ℕ) : 0 ≤ imbalance N K := by
  unfold imbalance
  positivity

theorem imbalance_le_one {N K : ℕ} (hN : 0 < N) (hK : K ≤ N) :
    imbalance N K ≤ 1 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hKr : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hK
  have habs : |(N : ℝ) - 2 * (K : ℝ)| ≤ (N : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [show 0 ≤ (K : ℝ) by positivity]
  unfold imbalance
  exact (div_le_one hNr).2 habs

/-- The variance-to-proxy ratio is exactly `2 (1 - x²)`. -/
theorem variance_div_hypergeomScale {N K m : ℕ}
    (hN : 2 ≤ N) (hm0 : 0 < m) (hmN : m < N) :
    variance N K m / SharpSerfling.hypergeomScale N m =
      2 * (1 - imbalance N K ^ 2) := by
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hN1r : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm0
  have hNmr : (N : ℝ) - (m : ℝ) ≠ 0 := by
    have : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
    linarith
  unfold variance SharpSerfling.hypergeomScale imbalance
  rw [div_pow, sq_abs]
  field_simp [hNr, hN1r, hmr, hNmr]
  ring

private theorem six_pow_mul_factorial_le_factorial_two_mul_add_one (n : ℕ) :
    6 ^ n * Nat.factorial n ≤ Nat.factorial (2 * n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hfactor : 6 * (n + 1) ≤ (2 * n + 2) * (2 * n + 3) := by nlinarith
      calc
        6 ^ (n + 1) * Nat.factorial (n + 1) =
            (6 * (n + 1)) * (6 ^ n * Nat.factorial n) := by
          rw [pow_succ, Nat.factorial_succ]
          ring
        _ ≤ ((2 * n + 2) * (2 * n + 3)) * Nat.factorial (2 * n + 1) :=
          Nat.mul_le_mul hfactor ih
        _ = Nat.factorial (2 * (n + 1) + 1) := by
          rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 by omega,
            Nat.factorial_succ (2 * n + 2),
            show 2 * n + 2 = (2 * n + 1) + 1 by omega,
            Nat.factorial_succ (2 * n + 1)]
          ring

/-- Power-series bound behind `2 sinh(t/2) / t ≤ exp(t²/24)`. -/
theorem sinh_le_mul_exp_sq_div_six {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.exp (x ^ 2 / 6) := by
  rw [Real.sinh_eq_tsum, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  rw [← tsum_mul_left]
  refine (Real.hasSum_sinh x).summable.tsum_le_tsum (fun n ↦ ?_)
    ((NormedSpace.expSeries_summable' (x ^ 2 / 6)).mul_left x)
  simp only [div_pow, smul_eq_mul, inv_mul_eq_div, div_div]
  have hpower : x ^ (2 * n + 1) = x * (x ^ 2) ^ n := by
    rw [pow_add, ← pow_mul]
    ring
  have hfac : (6 ^ n * Nat.factorial n : ℝ) ≤
      (Nat.factorial (2 * n + 1) : ℝ) := by
    exact_mod_cast six_pow_mul_factorial_le_factorial_two_mul_add_one n
  have hden : 0 < (6 ^ n * Nat.factorial n : ℝ) := by positivity
  rw [hpower]
  calc
    x * (x ^ 2) ^ n / (Nat.factorial (2 * n + 1) : ℝ) ≤
        (x * (x ^ 2) ^ n) / (6 ^ n * Nat.factorial n : ℝ) :=
      div_le_div_of_nonneg_left (mul_nonneg hx (by positivity)) hden hfac
    _ = x * ((x ^ 2) ^ n / ((6 : ℝ) ^ n * Nat.factorial n)) := by
      push_cast
      ring

theorem two_sinh_div_le_exp_sq_div_twentyFour {t : ℝ} (ht : 0 < t) :
    2 * Real.sinh (t / 2) / t ≤ Real.exp (t ^ 2 / 24) := by
  have hhalf : 0 ≤ t / 2 := by positivity
  have hs := sinh_le_mul_exp_sq_div_six hhalf
  have ht0 : t ≠ 0 := ne_of_gt ht
  rw [show (t / 2) ^ 2 / 6 = t ^ 2 / 24 by ring] at hs
  apply (div_le_iff₀ ht).2
  calc
    2 * Real.sinh (t / 2) ≤ 2 * ((t / 2) * Real.exp (t ^ 2 / 24)) := by nlinarith
    _ = Real.exp (t ^ 2 / 24) * t := by ring

/-- The centered hypergeometric count has exact uniform average zero. -/
theorem finiteAverage_centered_count_eq_zero {N K m : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (hm0 : 0 < m) :
    SharpSerfling.finiteAverage (fun s : Sample N m =>
      (count K s : ℝ) - center N K m) = 0 := by
  have hstein := binomialAverage_stein hK0 hKN hm0 (fun _ => (1 : ℝ))
  calc
    _ = binomialAverage N K m (fun i => (i : ℝ) - center N K m) :=
      finiteAverage_count_eq_binomialAverage (Nat.le_of_lt hKN) _
    _ = (N : ℝ)⁻¹ * binomialAverage N K m (fun _ => (0 : ℝ)) := by
      simpa using hstein
    _ = 0 := by simp [binomialAverage, binomialSum]

/-- The one-draw base case of the universal quadratic MGF bound. -/
theorem mgf_le_universal_one {N K : ℕ} (hN : 2 ≤ N) (hK : K ≤ N) (t : ℝ) :
    mgf N K 1 t ≤
      Real.exp (SharpSerfling.hypergeomScale N 1 * t ^ 2) := by
  have hOneN : 1 ≤ N := by omega
  by_cases hK0eq : K = 0
  · subst K
    rw [mgf_zeroSuccesses hOneN]
    apply Real.one_le_exp
    have hscale : 0 ≤ SharpSerfling.hypergeomScale N 1 := by
      unfold SharpSerfling.hypergeomScale
      norm_num only [Nat.cast_one]
      have hN1 : 0 < (N : ℝ) - 1 := by
        have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
        linarith
      exact div_nonneg (mul_nonneg (by positivity) hN1.le) (by positivity)
    exact mul_nonneg hscale (sq_nonneg t)
  by_cases hKNeq : K = N
  · subst K
    rw [mgf_allSuccesses (by omega) hOneN]
    apply Real.one_le_exp
    have hscale : 0 ≤ SharpSerfling.hypergeomScale N 1 := by
      unfold SharpSerfling.hypergeomScale
      norm_num only [Nat.cast_one]
      have hN1 : 0 < (N : ℝ) - 1 := by
        have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
        linarith
      exact div_nonneg (mul_nonneg (by positivity) hN1.le) (by positivity)
    exact mul_nonneg hscale (sq_nonneg t)
  have hK0 : 0 < K := Nat.pos_of_ne_zero hK0eq
  have hKN : K < N := by omega
  letI : Nonempty (Sample N 1) := sample_nonempty hOneN
  have hbound := SharpSerfling.finiteAverage_exp_le_of_mem_Icc_of_average_eq_zero
    (X := fun s : Sample N 1 => (count K s : ℝ) - center N K 1)
    (a := -center N K 1) (b := 1 - center N K 1)
    (fun s => by
      constructor
      · have hc : 0 ≤ (count K s : ℝ) := by positivity
        linarith
      · have hc : count K s ≤ 1 := count_le_sample s
        have hcR : (count K s : ℝ) ≤ 1 := by exact_mod_cast hc
        linarith)
    (finiteAverage_centered_count_eq_zero hK0 hKN (by omega)) t
  change SharpSerfling.finiteAverage (fun s : Sample N 1 =>
      Real.exp (t * ((count K s : ℝ) - center N K 1))) ≤ _
  rw [show SharpSerfling.hypergeomScale N 1 = (1 : ℝ) / 8 by
    unfold SharpSerfling.hypergeomScale
    norm_num only [Nat.cast_one]
    have hN1 : (N : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
      linarith
    field_simp [hN1]
    <;> ring]
  convert hbound using 1 <;> ring

theorem hypergeomScale_nonneg {N m : ℕ} (hN : 2 ≤ N) (hm : m ≤ N) :
    0 ≤ SharpSerfling.hypergeomScale N m := by
  have hmR : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm
  have hN1 : 0 < (N : ℝ) - 1 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  unfold SharpSerfling.hypergeomScale
  exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hmR)) (by positivity)

theorem mgf_zeroSample (N K : ℕ) (t : ℝ) : mgf N K 0 t = 1 := by
  letI : Nonempty (Sample N 0) := sample_nonempty (Nat.zero_le N)
  have hcount (s : Sample N 0) : count K s = 0 :=
    Nat.eq_zero_of_le_zero (count_le_sample s)
  simp [mgf, hcount, center, SharpSerfling.finiteAverage_one]

/-- Integrating a quadratic derivative envelope from zero. -/
theorem le_exp_quadratic_of_deriv_le {f : ℝ → ℝ} {b t : ℝ}
    (ht : 0 ≤ t) (hf : Differentiable ℝ f) (hzero : f 0 = 1)
    (hderiv : ∀ u, 0 < u → u < t →
      deriv f u ≤ 2 * b * u * Real.exp (b * u ^ 2)) :
    f t ≤ Real.exp (b * t ^ 2) := by
  let F : ℝ → ℝ := fun u => Real.exp (b * u ^ 2) - f u
  have hproxy (u : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (b * x ^ 2))
      (2 * b * u * Real.exp (b * u ^ 2)) u := by
    have hinner := ((hasDerivAt_pow 2 u).const_mul b)
    have hexp := hinner.exp
    convert hexp using 1 <;> norm_num <;> ring
  have hFdiff : Differentiable ℝ F := by
    intro u
    exact (hproxy u).differentiableAt.sub (hf u)
  have hmono : MonotoneOn F (Set.Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      hFdiff.continuous.continuousOn hFdiff.differentiableOn
    intro u hu
    dsimp only [F]
    change 0 ≤ deriv ((fun x : ℝ => Real.exp (b * x ^ 2)) - f) u
    rw [((hproxy u).sub (hf u).hasDerivAt).deriv]
    apply sub_nonneg.mpr
    have hu' : u ∈ Set.Ioo 0 t := by simpa only [interior_Icc] using hu
    exact hderiv u hu'.1 hu'.2
  have hFt := hmono (show 0 ∈ Set.Icc (0 : ℝ) t by exact ⟨le_rfl, ht⟩)
    (show t ∈ Set.Icc (0 : ℝ) t by exact ⟨ht, le_rfl⟩) ht
  dsimp [F] at hFt
  rw [hzero] at hFt
  norm_num at hFt ⊢
  linarith

/-- Abstract derivative envelope used in the universal induction. -/
theorem universal_derivative_envelope
    {b delta v r x c t : ℝ}
    (hb : 0 < b) (ht : 0 < t) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hc : 0 ≤ c)
    (hv : v = 2 * b * (1 - x ^ 2)) (hr : r ≤ c * x)
    (hgap : 1 / 24 + c ^ 2 / 4 ≤ delta) :
    2 * v * Real.exp (r * t) * Real.sinh (t / 2) *
        Real.exp ((b - delta) * t ^ 2) ≤
      2 * b * t * Real.exp (b * t ^ 2) := by
  have hxquad : 0 ≤ 1 - x ^ 2 := by nlinarith
  have hkernelProduct :
      (1 - x ^ 2) * (2 * Real.sinh (t / 2) / t) ≤
        Real.exp (-x ^ 2 + t ^ 2 / 24) := by
    have hsinh : 0 ≤ Real.sinh (t / 2) := by positivity
    have hratio : 0 ≤ 2 * Real.sinh (t / 2) / t :=
      div_nonneg (mul_nonneg (by norm_num) hsinh) ht.le
    calc
      _ ≤ Real.exp (-x ^ 2) * Real.exp (t ^ 2 / 24) := by
        exact mul_le_mul (one_sub_sq_le_exp_neg_sq x)
          (two_sinh_div_le_exp_sq_div_twentyFour ht) hratio (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]
  have hkernel :
      2 * (1 - x ^ 2) * Real.sinh (t / 2) ≤
        t * Real.exp (-x ^ 2 + t ^ 2 / 24) := by
    have hmul := mul_le_mul_of_nonneg_left hkernelProduct ht.le
    field_simp [ne_of_gt ht] at hmul
    convert hmul using 1 <;> ring
  have hrt : r * t ≤ c * x * t := mul_le_mul_of_nonneg_right hr ht.le
  have hcomplete := neg_sq_add_mul_le_quarter_sq x c t
  have hgapt := mul_le_mul_of_nonneg_right hgap (sq_nonneg t)
  have hexponent :
      (-x ^ 2 + t ^ 2 / 24) + r * t + (b - delta) * t ^ 2 ≤ b * t ^ 2 := by
    nlinarith
  have hexp :
      Real.exp ((-x ^ 2 + t ^ 2 / 24) + r * t + (b - delta) * t ^ 2) ≤
        Real.exp (b * t ^ 2) := Real.exp_le_exp.mpr hexponent
  have hexpCombine :
      Real.exp (-x ^ 2 + t ^ 2 / 24) * Real.exp (r * t) *
          Real.exp ((b - delta) * t ^ 2) =
        Real.exp ((-x ^ 2 + t ^ 2 / 24) + r * t + (b - delta) * t ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
  rw [hv]
  calc
    2 * (2 * b * (1 - x ^ 2)) * Real.exp (r * t) * Real.sinh (t / 2) *
        Real.exp ((b - delta) * t ^ 2) =
      2 * b * (2 * (1 - x ^ 2) * Real.sinh (t / 2)) *
        Real.exp (r * t) * Real.exp ((b - delta) * t ^ 2) := by ring
    _ ≤ 2 * b * (t * Real.exp (-x ^ 2 + t ^ 2 / 24)) *
        Real.exp (r * t) * Real.exp ((b - delta) * t ^ 2) := by
      gcongr <;> positivity
    _ = 2 * b * t * (Real.exp (-x ^ 2 + t ^ 2 / 24) * Real.exp (r * t) *
        Real.exp ((b - delta) * t ^ 2)) := by ring
    _ = 2 * b * t *
        Real.exp ((-x ^ 2 + t ^ 2 / 24) + r * t + (b - delta) * t ^ 2) := by
      rw [hexpCombine]
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

/-- Exact difference of successive quadratic proxy coefficients. -/
theorem hypergeomScale_sub_reduced {N m : ℕ} (hN : 4 ≤ N) (hm : 1 ≤ m) :
    SharpSerfling.hypergeomScale N m -
        SharpSerfling.hypergeomScale (N - 2) (m - 1) =
      (((N : ℝ) - 1) ^ 2 - 2 * (m : ℝ) * ((N : ℝ) - (m : ℝ))) /
        (8 * ((N : ℝ) - 1) * ((N : ℝ) - 3)) := by
  have h2N : 2 ≤ N := by omega
  rw [SharpSerfling.hypergeomScale, SharpSerfling.hypergeomScale,
    Nat.cast_sub h2N, Nat.cast_sub hm]
  norm_num only [Nat.cast_ofNat]
  have hdenRed : (N : ℝ) - 2 - 1 = (N : ℝ) - 3 := by ring
  rw [hdenRed]
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hN3 : (N : ℝ) - 3 ≠ 0 := by
    have : (3 : ℝ) < (N : ℝ) := by exact_mod_cast (show 3 < N by omega)
    linarith
  field_simp [hN1, hN3]
  ring

/-- Exact rational certificate for the final exponent in the universal induction. -/
theorem universalExponentGap_certificate {N m : ℕ} (hN : 4 ≤ N) :
    ((((N : ℝ) - 1) ^ 2 -
          2 * (m : ℝ) * ((N : ℝ) - (m : ℝ))) /
        (8 * ((N : ℝ) - 1) * ((N : ℝ) - 3))) -
        1 / 24 - sampleTilt N m ^ 2 / 4 =
      ((N : ℝ) * ((N : ℝ) - 4) * ((N : ℝ) - 2) ^ 2 +
          3 * ((N : ℝ) - 2 * (m : ℝ)) ^ 2) /
        (48 * ((N : ℝ) - 1) * ((N : ℝ) - 3) * ((N : ℝ) - 2) ^ 2) := by
  unfold sampleTilt
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hN2 : (N : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
    linarith
  have hN3 : (N : ℝ) - 3 ≠ 0 := by
    have : (3 : ℝ) < (N : ℝ) := by exact_mod_cast (show 3 < N by omega)
    linarith
  field_simp [hN1, hN2, hN3]
  ring

theorem universalExponentGap_nonneg {N m : ℕ}
    (hN : 4 ≤ N) (hm1 : 1 ≤ m) :
    1 / 24 + sampleTilt N m ^ 2 / 4 ≤
      SharpSerfling.hypergeomScale N m -
        SharpSerfling.hypergeomScale (N - 2) (m - 1) := by
  rw [hypergeomScale_sub_reduced hN hm1]
  have hcert := universalExponentGap_certificate (N := N) (m := m) hN
  have hNR : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN4 : 0 ≤ (N : ℝ) - 4 := by linarith
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hnum : 0 ≤
      (N : ℝ) * ((N : ℝ) - 4) * ((N : ℝ) - 2) ^ 2 +
        3 * ((N : ℝ) - 2 * (m : ℝ)) ^ 2 := by positivity
  have hden : 0 <
      48 * ((N : ℝ) - 1) * ((N : ℝ) - 3) * ((N : ℝ) - 2) ^ 2 := by
    have hN1 : 0 < (N : ℝ) - 1 := by linarith
    have hN2 : 0 < (N : ℝ) - 2 := by linarith
    have hN3 : 0 < (N : ℝ) - 3 := by linarith
    positivity
  have hfrac : 0 ≤
      ((N : ℝ) * ((N : ℝ) - 4) * ((N : ℝ) - 2) ^ 2 +
          3 * ((N : ℝ) - 2 * (m : ℝ)) ^ 2) /
        (48 * ((N : ℝ) - 1) * ((N : ℝ) - 3) * ((N : ℝ) - 2) ^ 2) :=
    div_nonneg hnum hden.le
  linarith

/-- The recursion tilt is bounded by the product of sample tilt and success imbalance. -/
theorem recursionTilt_le_sampleTilt_mul_imbalance {N K m : ℕ}
    (hN : 3 ≤ N) (hm : 2 * m ≤ N) :
    recursionTilt N K m ≤ sampleTilt N m * imbalance N K := by
  have hNr : 0 < (N : ℝ) := by positivity
  have hN2 : 0 < (N : ℝ) - 2 := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
    linarith
  have hsample : 0 ≤ sampleTilt N m := by
    unfold sampleTilt
    have hmR : 2 * (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm
    positivity
  have habs : (N : ℝ) - 2 * (K : ℝ) ≤
      |(N : ℝ) - 2 * (K : ℝ)| := le_abs_self _
  have heq : recursionTilt N K m = sampleTilt N m *
      (((N : ℝ) - 2 * (K : ℝ)) / (N : ℝ)) := by
    unfold recursionTilt sampleTilt
    field_simp
  rw [heq]
  unfold imbalance
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right habs hNr.le) hsample

/-- One induction step at the derivative level. -/
theorem deriv_mgf_le_universalProxy_of_reduced {N K m : ℕ}
    (hN : 4 ≤ N) (hK0 : 0 < K) (hKN : K < N)
    (hm2 : 2 ≤ m) (hmHalf : 2 * m ≤ N) {t : ℝ} (ht : 0 < t)
    (hred : mgf (N - 2) (K - 1) (m - 1) t ≤
      Real.exp (SharpSerfling.hypergeomScale (N - 2) (m - 1) * t ^ 2)) :
    deriv (mgf N K m) t ≤
      2 * SharpSerfling.hypergeomScale N m * t *
        Real.exp (SharpSerfling.hypergeomScale N m * t ^ 2) := by
  have hm0 : 0 < m := by omega
  have hmN : m < N := by omega
  have hKle : K ≤ N := Nat.le_of_lt hKN
  have hb : 0 < SharpSerfling.hypergeomScale N m := by
    unfold SharpSerfling.hypergeomScale
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
    have hmNR : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
    have hN1R : 0 < (N : ℝ) - 1 := by
      have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
      linarith
    positivity
  have hx0 : 0 ≤ imbalance N K := imbalance_nonneg N K
  have hx1 : imbalance N K ≤ 1 := imbalance_le_one (by omega) hKle
  have hc : 0 ≤ sampleTilt N m := by
    unfold sampleTilt
    have hmR : 2 * (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmHalf
    have hN2 : 0 < (N : ℝ) - 2 := by
      have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
      linarith
    positivity
  have hratio := variance_div_hypergeomScale (N := N) (K := K) (m := m)
    (by omega) hm0 hmN
  have hv : variance N K m =
      2 * SharpSerfling.hypergeomScale N m * (1 - imbalance N K ^ 2) := by
    have := (div_eq_iff (ne_of_gt hb)).mp hratio
    nlinarith
  have hxquad : 0 ≤ 1 - imbalance N K ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hx1) (by linarith : 0 ≤ 1 + imbalance N K)
    nlinarith
  have hvnonneg : 0 ≤ variance N K m := by
    rw [hv]
    exact mul_nonneg (mul_nonneg (by positivity) hb.le) hxquad
  have hr := recursionTilt_le_sampleTilt_mul_imbalance (N := N) (K := K) (m := m)
    (by omega) hmHalf
  have hgap := universalExponentGap_nonneg (N := N) (m := m) hN (by omega)
  rw [deriv_mgf_recursion (by omega) hK0 hKN hm0 hmN]
  calc
    2 * variance N K m * Real.exp (recursionTilt N K m * t) *
          Real.sinh (t / 2) * mgf (N - 2) (K - 1) (m - 1) t ≤
        2 * variance N K m * Real.exp (recursionTilt N K m * t) *
          Real.sinh (t / 2) *
            Real.exp (SharpSerfling.hypergeomScale (N - 2) (m - 1) * t ^ 2) := by
      apply mul_le_mul_of_nonneg_left hred
      have hsinh : 0 ≤ Real.sinh (t / 2) := by positivity
      positivity
    _ ≤ _ := by
      have henv := universal_derivative_envelope hb ht hx0 hx1 hc hv hr hgap
      convert henv using 1 <;> ring

/-- Universal quadratic MGF bound for `m ≤ N/2` and nonnegative arguments. -/
theorem mgf_le_universal_half_nonneg :
    ∀ m N K : ℕ, ∀ t : ℝ, 2 * m ≤ N → K ≤ N → 0 ≤ t →
      mgf N K m t ≤
        Real.exp (SharpSerfling.hypergeomScale N m * t ^ 2) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro N K t hmHalf hK ht
      by_cases hm0eq : m = 0
      · subst m
        simp [mgf_zeroSample, SharpSerfling.hypergeomScale]
      by_cases hm1eq : m = 1
      · subst m
        exact mgf_le_universal_one (by omega) hK t
      have hm2 : 2 ≤ m := by omega
      have hmN : m ≤ N := by omega
      have hN : 4 ≤ N := by omega
      by_cases hK0eq : K = 0
      · subst K
        rw [mgf_zeroSuccesses hmN]
        exact Real.one_le_exp
          (mul_nonneg (hypergeomScale_nonneg (by omega) hmN) (sq_nonneg t))
      by_cases hKNeq : K = N
      · subst K
        rw [mgf_allSuccesses (by omega) hmN]
        exact Real.one_le_exp
          (mul_nonneg (hypergeomScale_nonneg (by omega) hmN) (sq_nonneg t))
      have hK0 : 0 < K := Nat.pos_of_ne_zero hK0eq
      have hKN : K < N := by omega
      apply le_exp_quadratic_of_deriv_le ht
        (fun u => (hasDerivAt_mgf N K m u).differentiableAt)
        (mgf_zero_of_le N K m hmN)
      intro u hu hut
      apply deriv_mgf_le_universalProxy_of_reduced hN hK0 hKN hm2 hmHalf hu
      exact ih (m - 1) (by omega) (N - 2) (K - 1) u
        (by omega) (by omega) hu.le

/-- Universal quadratic MGF bound for `m ≤ N/2`, for all real arguments. -/
theorem mgf_le_universal_half {N K m : ℕ}
    (hmHalf : 2 * m ≤ N) (hK : K ≤ N) (t : ℝ) :
    mgf N K m t ≤
      Real.exp (SharpSerfling.hypergeomScale N m * t ^ 2) := by
  by_cases hN0 : N = 0
  · subst N
    have hm0 : m = 0 := by omega
    have hK0 : K = 0 := by omega
    subst m
    subst K
    simp [mgf_zeroSample, SharpSerfling.hypergeomScale]
  by_cases ht : 0 ≤ t
  · exact mgf_le_universal_half_nonneg m N K t hmHalf hK ht
  · have hneg : 0 ≤ -t := le_of_lt (neg_pos.mpr (lt_of_not_ge ht))
    have hKc : N - K ≤ N := Nat.sub_le N K
    have hbound := mgf_le_universal_half_nonneg m N (N - K) (-t)
      hmHalf hKc hneg
    rw [mgf_successComplement (Nat.pos_of_ne_zero hN0) hK (-t)] at hbound
    simpa only [neg_neg, neg_sq] using hbound

/-- Universal quadratic MGF bound, with the larger draw sizes supplied by sample
complementation. -/
theorem mgf_le_universal {N K m : ℕ} (hN : 2 ≤ N) (hK : K ≤ N)
    (hm : m ≤ N) (t : ℝ) :
    mgf N K m t ≤
      Real.exp (SharpSerfling.hypergeomScale N m * t ^ 2) := by
  by_cases hmHalf : 2 * m ≤ N
  · exact mgf_le_universal_half hmHalf hK t
  · have hcompHalf : 2 * (N - m) ≤ N := by omega
    have hbound := mgf_le_universal_half (N := N) (K := K) (m := N - m)
      hcompHalf hK (-t)
    rw [mgf_sampleComplement (by omega) hK hm (-t)] at hbound
    rw [SharpSerfling.hypergeomScale_symm N m hm] at hbound
    simpa only [neg_neg, neg_sq] using hbound

/-- Logarithmic form of the universal hypergeometric MGF bound. -/
theorem log_mgf_le_universal {N K m : ℕ} (hN : 2 ≤ N) (hK : K ≤ N)
    (hm : m ≤ N) (t : ℝ) :
    Real.log (mgf N K m t) ≤
      SharpSerfling.hypergeomScale N m * t ^ 2 := by
  exact (Real.log_le_iff_le_exp (mgf_pos hm t)).2
    (mgf_le_universal hN hK hm t)

/-- The parity-sharp theorem for even population sizes follows immediately from
the universal bound, since `κ_N = 1`. -/
theorem sharp_mgf_of_even {N K m : ℕ} (hN : 2 ≤ N) (hEven : Even N)
    (hK : K ≤ N) (hm : m ≤ N) (t : ℝ) :
    Real.log (mgf N K m t) ≤
      SharpSerfling.kappa N * SharpSerfling.hypergeomScale N m * t ^ 2 := by
  rw [SharpSerfling.kappa_of_even hEven, one_mul]
  exact log_mgf_le_universal hN hK hm t

end SharpSerfling.Hypergeometric
