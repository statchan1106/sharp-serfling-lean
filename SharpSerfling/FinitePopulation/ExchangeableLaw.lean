import SharpSerfling.FinitePopulation.Exchangeable

namespace SharpSerfling.FinitePopulation

open scoped BigOperators
open MeasureTheory

/-- Standard law-based definition of finite exchangeability: every
coordinate permutation has the same pushforward distribution. -/
def IsExchangeableInLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {N : ℕ} (X : Ω → Fin N → ℝ) : Prop :=
  ∀ π : Equiv.Perm (Fin N),
    Measure.map (fun ω ↦ fun j ↦ X ω (π j)) μ = Measure.map X μ

theorem measurable_vector {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j)) :
    Measurable X := by
  exact measurable_pi_lambda X fun j ↦ (hXmeas j).measurable

theorem integral_comp_perm_eq_of_exchangeableInLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ}
    (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (hEx : IsExchangeableInLaw μ X) (π : Equiv.Perm (Fin N))
    (f : (Fin N → ℝ) → ℝ) (hf : StronglyMeasurable f) :
    (∫ ω, f (fun j ↦ X ω (π j)) ∂μ) = ∫ ω, f (X ω) ∂μ := by
  have hXm : Measurable X := measurable_vector X hXmeas
  have hYm : Measurable (fun ω ↦ fun j ↦ X ω (π j)) := by
    exact measurable_pi_lambda _ fun j ↦ (hXmeas (π j)).measurable
  calc
    (∫ ω, f (fun j ↦ X ω (π j)) ∂μ) =
        ∫ x, f x ∂Measure.map (fun ω ↦ fun j ↦ X ω (π j)) μ := by
      rw [integral_map hYm.aemeasurable hf.aestronglyMeasurable]
    _ = ∫ x, f x ∂Measure.map X μ := by rw [hEx π]
    _ = ∫ ω, f (X ω) ∂μ := by
      rw [integral_map hXm.aemeasurable hf.aestronglyMeasurable]

/-- The conditional-permutation identity derived from standard equality in
law, rather than from expectation invariance over arbitrary observables. -/
theorem exchangeableMgf_eq_integral_mgf_inLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N n : ℕ} (hN : 0 < N)
    (hn : n ≤ N) {a b : ℝ} (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (hX : ∀ ω j, a ≤ X ω j ∧ X ω j ≤ b)
    (hEx : IsExchangeableInLaw μ X) (w : Fin n → ℝ) (lam : ℝ) :
    exchangeableMgf μ hn X w lam = ∫ ω, mgf hn (X ω) w lam ∂μ := by
  have hint (π : Equiv.Perm (Fin N)) :
      Integrable (fun ω ↦ Real.exp (lam * statistic hn (X ω) w π)) μ :=
    integrable_exp_statistic μ hN hn X hXmeas hX w lam π
  have hf : StronglyMeasurable
      (fun x : Fin N → ℝ ↦ Real.exp (lam * contrast hn x w)) := by
    unfold contrast statistic SharpSerfling.populationMean
    fun_prop
  have hinvariance (π : Equiv.Perm (Fin N)) :
      (∫ ω, Real.exp (lam * statistic hn (X ω) w π) ∂μ) =
        exchangeableMgf μ hn X w lam := by
    have hex := integral_comp_perm_eq_of_exchangeableInLaw
      μ X hXmeas hEx π _ hf
    rw [show (fun ω ↦ Real.exp (lam * contrast hn (fun j ↦ X ω (π j)) w)) =
        fun ω ↦ Real.exp (lam * statistic hn (X ω) w π) by
      funext ω
      rw [contrast_comp_perm]] at hex
    exact hex
  have hcommute := integral_finiteAverage μ hint
  rw [show (fun ω ↦ mgf hn (X ω) w lam) =
      fun ω ↦ SharpSerfling.finiteAverage
        (fun π : Equiv.Perm (Fin N) ↦
          Real.exp (lam * statistic hn (X ω) w π)) by
    funext ω
    rfl]
  rw [hcommute]
  symm
  calc
    SharpSerfling.finiteAverage
        (fun π : Equiv.Perm (Fin N) ↦
          ∫ ω, Real.exp (lam * statistic hn (X ω) w π) ∂μ) =
        SharpSerfling.finiteAverage
          (fun _π : Equiv.Perm (Fin N) ↦ exchangeableMgf μ hn X w lam) := by
      apply congrArg SharpSerfling.finiteAverage
      funext π
      exact hinvariance π
    _ = exchangeableMgf μ hn X w lam := SharpSerfling.finiteAverage_const _

/-- Manuscript weighted-exchangeable MGF inequality under the standard
law-based definition of exchangeability. -/
theorem weighted_exchangeable_mgf_inLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N n : ℕ} (hN : 2 ≤ N)
    (hn : n ≤ N) {a b : ℝ} (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (hX : ∀ ω j, a ≤ X ω j ∧ X ω j ≤ b)
    (hEx : IsExchangeableInLaw μ X) (w : Fin n → ℝ) (lam : ℝ) :
    Real.log (exchangeableMgf μ hn X w lam) ≤
      SharpSerfling.kappa N / 8 * SharpSerfling.rho N n w *
        (b - a) ^ 2 * lam ^ 2 := by
  let C : ℝ := SharpSerfling.kappa N / 8 * SharpSerfling.rho N n w *
    (b - a) ^ 2 * lam ^ 2
  have hint (π : Equiv.Perm (Fin N)) :
      Integrable (fun ω ↦ Real.exp (lam * statistic hn (X ω) w π)) μ :=
    integrable_exp_statistic μ (by omega) hn X hXmeas hX w lam π
  have hmgfInt : Integrable (fun ω ↦ mgf hn (X ω) w lam) μ := by
    change Integrable (fun ω ↦ SharpSerfling.finiteAverage
      (fun π : Equiv.Perm (Fin N) ↦
        Real.exp (lam * statistic hn (X ω) w π))) μ
    exact integrable_finiteAverage μ hint
  have hpoint (ω : Ω) : mgf hn (X ω) w lam ≤ Real.exp C := by
    apply (Real.log_le_iff_le_exp (mgf_pos hn (X ω) w lam)).mp
    dsimp [C]
    exact weighted_mgf N n hN hn a b (X ω) (hX ω) w lam
  have hIntLe : (∫ ω, mgf hn (X ω) w lam ∂μ) ≤ Real.exp C := by
    have h := integral_mono hmgfInt (integrable_const (Real.exp C)) hpoint
    simpa using h
  have hExp : exchangeableMgf μ hn X w lam ≤ Real.exp C := by
    rw [exchangeableMgf_eq_integral_mgf_inLaw μ (by omega) hn X hXmeas hX hEx w lam]
    exact hIntLe
  have hpos := exchangeableMgf_pos μ (by omega) hn X hXmeas hX w lam
  exact (Real.log_le_iff_le_exp hpos).2 hExp

theorem weighted_exchangeable_mgf_centeredNorm_inLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N n : ℕ} (hN : 2 ≤ N)
    (hn : n ≤ N) {a b : ℝ} (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (hX : ∀ ω j, a ≤ X ω j ∧ X ω j ≤ b)
    (hEx : IsExchangeableInLaw μ X) (w : Fin n → ℝ) (lam : ℝ) :
    Real.log (exchangeableMgf μ hn X w lam) ≤
      lam ^ 2 * (b - a) ^ 2 / 8 *
        (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) *
          sqNorm (centeredWeight hn w) := by
  have hmain := weighted_exchangeable_mgf_inLaw
    μ hN hn X hXmeas hX hEx w lam
  have hnorm := sum_sq_centeredWeight_eq_rho hN hn w
  change sqNorm (centeredWeight hn w) = _ at hnorm
  calc
    Real.log (exchangeableMgf μ hn X w lam) ≤
        SharpSerfling.kappa N / 8 * SharpSerfling.rho N n w *
          (b - a) ^ 2 * lam ^ 2 := hmain
    _ = lam ^ 2 * (b - a) ^ 2 / 8 *
        (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) *
          sqNorm (centeredWeight hn w) := by
      rw [hnorm]
      have hNR : (N : ℝ) ≠ 0 := by positivity
      have hNm1 : (N : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
        linarith
      field_simp [hNR, hNm1]

/-- Chernoff tail conclusion of the manuscript under the standard
law-based definition of exchangeability. -/
theorem weighted_exchangeable_tail_inLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N n : ℕ} (hN : 2 ≤ N)
    (hn : n ≤ N) {a b : ℝ} (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (hX : ∀ ω j, a ≤ X ω j ∧ X ω j ≤ b)
    (hEx : IsExchangeableInLaw μ X) (w : Fin n → ℝ)
    (hw : centeredWeight hn w ≠ fun _ ↦ 0) {u : ℝ} (hu : 0 < u) :
    exchangeableUpperTail μ hn X w u ≤
      Real.exp (-2 * u ^ 2 /
        ((b - a) ^ 2 *
          (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) *
            sqNorm (centeredWeight hn w))) := by
  let c : ℝ := b - a
  letI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hab : a ≤ b := by
    let j₀ : Fin N := ⟨0, by omega⟩
    let ω₀ : Ω := Classical.choice (nonempty_of_isProbabilityMeasure μ)
    exact (hX ω₀ j₀).1.trans (hX ω₀ j₀).2
  by_cases hc0 : c = 0
  · have habEq : a = b := by dsimp [c] at hc0; linarith
    have hXconst (ω : Ω) : X ω = fun _ ↦ a := by
      funext j
      have hj := hX ω j
      rw [← habEq] at hj
      linarith
    have hcontrast (ω : Ω) : contrast hn (X ω) w = 0 := by
      unfold contrast
      rw [hXconst, statistic_const (by omega) hn]
    unfold exchangeableUpperTail
    rw [show {ω | u ≤ contrast hn (X ω) w} = (∅ : Set Ω) by
      ext ω
      simp [hcontrast ω, not_le_of_gt hu]]
    dsimp [c] at hc0
    simp [hc0]
  have hcpos : 0 < c := by
    dsimp [c]
    apply sub_pos.mpr
    apply lt_of_le_of_ne hab
    intro heq
    apply hc0
    simp [c, heq]
  let D : ℝ := c ^ 2 *
    (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) *
      sqNorm (centeredWeight hn w)
  have hDpos : 0 < D := by
    dsimp [D]
    have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
      have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
      linarith
    exact mul_pos (mul_pos (sq_pos_of_pos hcpos)
      (div_pos (mul_pos (SharpSerfling.kappa_pos hN) (by positivity)) hNm1))
      (sqNorm_pos_of_ne_zero hw)
  let t : ℝ := 4 * u / D
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hint : Integrable (fun ω ↦ Real.exp (t * contrast hn (X ω) w)) μ := by
    have h := integrable_exp_statistic μ (by omega) hn X hXmeas hX w t
      (Equiv.refl (Fin N))
    simpa [contrast] using h
  have hmarkov := exchangeableUpperTail_le_chernoff μ hn X hXmeas w u t ht hint
  have hlog := weighted_exchangeable_mgf_centeredNorm_inLaw
    μ hN hn X hXmeas hX hEx w t
  have hmgf : exchangeableMgf μ hn X w t ≤ Real.exp (D / 8 * t ^ 2) := by
    apply Real.le_exp_of_log_le
    calc
      Real.log (exchangeableMgf μ hn X w t) ≤
          t ^ 2 * (b - a) ^ 2 / 8 *
            (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) *
              sqNorm (centeredWeight hn w) := hlog
      _ = D / 8 * t ^ 2 := by dsimp [D, c]; ring
  calc
    exchangeableUpperTail μ hn X w u ≤
        Real.exp (-t * u) * exchangeableMgf μ hn X w t := hmarkov
    _ ≤ Real.exp (-t * u) * Real.exp (D / 8 * t ^ 2) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = Real.exp (-2 * u ^ 2 /
        ((b - a) ^ 2 *
          (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) *
            sqNorm (centeredWeight hn w))) := by
      rw [← Real.exp_add]
      congr 1
      change -t * u + D / 8 * t ^ 2 = -2 * u ^ 2 / D
      dsimp [t]
      field_simp [hDpos.ne']
      ring

end SharpSerfling.FinitePopulation
