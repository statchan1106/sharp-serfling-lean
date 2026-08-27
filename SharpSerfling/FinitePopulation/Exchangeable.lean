import SharpSerfling.FinitePopulation.Serfling
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Notation

namespace SharpSerfling.FinitePopulation

open scoped BigOperators
open MeasureTheory

/-- The centered contrast of the first `n` coordinates of a fixed vector. -/
noncomputable def contrast {N n : ℕ} (hn : n ≤ N) (x : Fin N → ℝ)
    (w : Fin n → ℝ) : ℝ :=
  statistic hn x w (Equiv.refl (Fin N))

/-- MGF of a centered contrast on an arbitrary probability space. -/
noncomputable def exchangeableMgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {N n : ℕ} (hn : n ≤ N) (X : Ω → Fin N → ℝ)
    (w : Fin n → ℝ) (lam : ℝ) : ℝ :=
  ∫ ω, Real.exp (lam * contrast hn (X ω) w) ∂μ

/-- Expectation-invariance formulation of finite exchangeability.  It states
that every scalar observable has the same expectation after any coordinate
permutation. -/
def IsExchangeable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {N : ℕ} (X : Ω → Fin N → ℝ) : Prop :=
  ∀ (π : Equiv.Perm (Fin N)) (f : (Fin N → ℝ) → ℝ),
    (∫ ω, f (fun j ↦ X ω (π j)) ∂μ) = ∫ ω, f (X ω) ∂μ

theorem populationMean_comp_perm {N : ℕ} (x : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) :
    SharpSerfling.populationMean (fun j ↦ x (π j)) =
      SharpSerfling.populationMean x := by
  unfold SharpSerfling.populationMean
  rw [Equiv.sum_comp π x]

theorem contrast_comp_perm {N n : ℕ} (hn : n ≤ N) (x : Fin N → ℝ)
    (w : Fin n → ℝ) (π : Equiv.Perm (Fin N)) :
    contrast hn (fun j ↦ x (π j)) w = statistic hn x w π := by
  unfold contrast statistic
  rw [populationMean_comp_perm]
  simp

theorem stronglyMeasurable_statistic {Ω : Type*} [MeasurableSpace Ω]
    {N n : ℕ} (hn : n ≤ N) (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (w : Fin n → ℝ) (π : Equiv.Perm (Fin N)) :
    StronglyMeasurable (fun ω ↦ statistic hn (X ω) w π) := by
  unfold statistic SharpSerfling.populationMean
  fun_prop

theorem populationMean_mem_Icc {N : ℕ} (hN : 0 < N) {a b : ℝ}
    (x : Fin N → ℝ) (hx : ∀ j, a ≤ x j ∧ x j ≤ b) :
    a ≤ SharpSerfling.populationMean x ∧ SharpSerfling.populationMean x ≤ b := by
  unfold SharpSerfling.populationMean
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · rw [le_div_iff₀ hNR]
    calc
      a * (N : ℝ) = ∑ _j : Fin N, a := by simp [mul_comm]
      _ ≤ ∑ j, x j := Finset.sum_le_sum fun j hj ↦ (hx j).1
  · rw [div_le_iff₀ hNR]
    calc
      (∑ j, x j) ≤ ∑ _j : Fin N, b := Finset.sum_le_sum fun j hj ↦ (hx j).2
      _ = b * (N : ℝ) := by simp [mul_comm]

theorem abs_statistic_le {N n : ℕ} (hN : 0 < N) (hn : n ≤ N)
    {a b : ℝ} (x : Fin N → ℝ) (hx : ∀ j, a ≤ x j ∧ x j ≤ b)
    (w : Fin n → ℝ) (π : Equiv.Perm (Fin N)) :
    |statistic hn x w π| ≤ (∑ i, |w i|) * (b - a) := by
  have hmean := populationMean_mem_Icc hN x hx
  unfold statistic
  calc
    |∑ i, w i * (x (π (Fin.castLE hn i)) - SharpSerfling.populationMean x)| ≤
        ∑ i, |w i * (x (π (Fin.castLE hn i)) - SharpSerfling.populationMean x)| := by
      simpa using Finset.abs_sum_le_sum_abs
        (fun i : Fin n ↦ w i *
          (x (π (Fin.castLE hn i)) - SharpSerfling.populationMean x)) Finset.univ
    _ ≤ ∑ i, |w i| * (b - a) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [abs_le]
      constructor <;> linarith [(hx (π (Fin.castLE hn i))).1,
        (hx (π (Fin.castLE hn i))).2, hmean.1, hmean.2]
    _ = (∑ i, |w i|) * (b - a) := by rw [Finset.sum_mul]

theorem integrable_exp_statistic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {N n : ℕ} (hN : 0 < N)
    (hn : n ≤ N) {a b : ℝ} (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (hX : ∀ ω j, a ≤ X ω j ∧ X ω j ≤ b)
    (w : Fin n → ℝ) (lam : ℝ) (π : Equiv.Perm (Fin N)) :
    Integrable (fun ω ↦ Real.exp (lam * statistic hn (X ω) w π)) μ := by
  have hmeas : StronglyMeasurable
      (fun ω ↦ Real.exp (lam * statistic hn (X ω) w π)) := by
    have hs := stronglyMeasurable_statistic hn X hXmeas w π
    exact Real.continuous_exp.comp_stronglyMeasurable (hs.const_mul lam)
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    (Real.exp (|lam| * ((∑ i, |w i|) * (b - a))))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    lam * statistic hn (X ω) w π ≤ |lam * statistic hn (X ω) w π| := le_abs_self _
    _ = |lam| * |statistic hn (X ω) w π| := abs_mul _ _
    _ ≤ |lam| * ((∑ i, |w i|) * (b - a)) :=
      mul_le_mul_of_nonneg_left (abs_statistic_le hN hn (X ω) (hX ω) w π)
        (abs_nonneg lam)

theorem integral_finiteAverage {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (μ : Measure Ω) {f : ι → Ω → ℝ}
    (hf : ∀ i, Integrable (f i) μ) :
    (∫ ω, SharpSerfling.finiteAverage (fun i ↦ f i ω) ∂μ) =
      SharpSerfling.finiteAverage (fun i ↦ ∫ ω, f i ω ∂μ) := by
  unfold SharpSerfling.finiteAverage
  rw [integral_div]
  rw [integral_finsetSum Finset.univ fun i hi ↦ hf i]

theorem integrable_finiteAverage {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (μ : Measure Ω) {f : ι → Ω → ℝ}
    (hf : ∀ i, Integrable (f i) μ) :
    Integrable (fun ω ↦ SharpSerfling.finiteAverage (fun i ↦ f i ω)) μ := by
  unfold SharpSerfling.finiteAverage
  exact (integrable_finsetSum Finset.univ fun i hi ↦ hf i).div_const _

/-- Exchangeability identifies the observed contrast MGF with the expectation
of the conditional permutation MGF. -/
theorem exchangeableMgf_eq_integral_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N n : ℕ} (hN : 0 < N)
    (hn : n ≤ N) {a b : ℝ} (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (hX : ∀ ω j, a ≤ X ω j ∧ X ω j ≤ b)
    (hEx : IsExchangeable μ X) (w : Fin n → ℝ) (lam : ℝ) :
    exchangeableMgf μ hn X w lam = ∫ ω, mgf hn (X ω) w lam ∂μ := by
  have hint (π : Equiv.Perm (Fin N)) :
      Integrable (fun ω ↦ Real.exp (lam * statistic hn (X ω) w π)) μ :=
    integrable_exp_statistic μ hN hn X hXmeas hX w lam π
  have hinvariance (π : Equiv.Perm (Fin N)) :
      (∫ ω, Real.exp (lam * statistic hn (X ω) w π) ∂μ) =
        exchangeableMgf μ hn X w lam := by
    have hex := hEx π (fun x ↦ Real.exp (lam * contrast hn x w))
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

theorem exchangeableMgf_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N n : ℕ} (hN : 0 < N)
    (hn : n ≤ N) {a b : ℝ} (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (hX : ∀ ω j, a ≤ X ω j ∧ X ω j ≤ b)
    (w : Fin n → ℝ) (lam : ℝ) : 0 < exchangeableMgf μ hn X w lam := by
  have hint := integrable_exp_statistic μ hN hn X hXmeas hX w lam
    (Equiv.refl (Fin N))
  unfold exchangeableMgf
  apply integral_exp_pos
  simpa [contrast] using hint

/-- MGF inequality in manuscript Corollary `cor:weighted-exchangeable`, in
the equivalent `rho` normalization. -/
theorem weighted_exchangeable_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N n : ℕ} (hN : 2 ≤ N)
    (hn : n ≤ N) {a b : ℝ} (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (hX : ∀ ω j, a ≤ X ω j ∧ X ω j ≤ b)
    (hEx : IsExchangeable μ X) (w : Fin n → ℝ) (lam : ℝ) :
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
    rw [exchangeableMgf_eq_integral_mgf μ (by omega) hn X hXmeas hX hEx w lam]
    exact hIntLe
  have hpos := exchangeableMgf_pos μ (by omega) hn X hXmeas hX w lam
  exact (Real.log_le_iff_le_exp hpos).2 hExp

/-- The same exchangeable MGF bound with the manuscript's
`Cstar * ‖w°‖²` normalization. -/
theorem weighted_exchangeable_mgf_centeredNorm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N n : ℕ} (hN : 2 ≤ N)
    (hn : n ≤ N) {a b : ℝ} (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (hX : ∀ ω j, a ≤ X ω j ∧ X ω j ≤ b)
    (hEx : IsExchangeable μ X) (w : Fin n → ℝ) (lam : ℝ) :
    Real.log (exchangeableMgf μ hn X w lam) ≤
      lam ^ 2 * (b - a) ^ 2 / 8 *
        (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) *
          sqNorm (centeredWeight hn w) := by
  have hmain := weighted_exchangeable_mgf μ hN hn X hXmeas hX hEx w lam
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

theorem stronglyMeasurable_contrast {Ω : Type*} [MeasurableSpace Ω]
    {N n : ℕ} (hn : n ≤ N) (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (w : Fin n → ℝ) :
    StronglyMeasurable (fun ω ↦ contrast hn (X ω) w) := by
  simpa [contrast] using stronglyMeasurable_statistic hn X hXmeas w
    (Equiv.refl (Fin N))

theorem sum_zeroPad_mul_function {N n : ℕ} (hn : n ≤ N)
    (w : Fin n → ℝ) (f : Fin N → ℝ) :
    ∑ j, zeroPad hn w j * f j = ∑ i, w i * f (Fin.castLE hn i) := by
  rw [show (∑ j, zeroPad hn w j * f j) =
      ∑ j, zeroPad hn (fun i ↦ w i * f (Fin.castLE hn i)) j by
    apply Finset.sum_congr rfl
    intro j hj
    exact zeroPad_mul hn w f j]
  exact sum_zeroPad hn _

/-- The statistic is the inner product of the centered zero-padded weights
with the permuted population. -/
theorem statistic_eq_centeredWeight_dot {N n : ℕ} (hN : 0 < N)
    (hn : n ≤ N) (x : Fin N → ℝ) (w : Fin n → ℝ)
    (π : Equiv.Perm (Fin N)) :
    statistic hn x w π = ∑ j, centeredWeight hn w j * x (π j) := by
  have hsumperm : ∑ j, x (π j) = ∑ j, x j := Equiv.sum_comp π x
  unfold statistic centeredWeight SharpSerfling.populationMean
  simp_rw [mul_sub, sub_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_zeroPad_mul_function]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hsumperm]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hNR]

theorem contrast_eq_centeredWeight_dot {N n : ℕ} (hN : 0 < N)
    (hn : n ≤ N) (x : Fin N → ℝ) (w : Fin n → ℝ) :
    contrast hn x w = ∑ j, centeredWeight hn w j * x j := by
  unfold contrast
  simpa using statistic_eq_centeredWeight_dot hN hn x w (Equiv.refl (Fin N))

theorem contrast_eq_zero_of_centeredWeight_eq_zero {N n : ℕ} (hN : 0 < N)
    (hn : n ≤ N) (x : Fin N → ℝ) (w : Fin n → ℝ)
    (hw : centeredWeight hn w = fun _ ↦ 0) : contrast hn x w = 0 := by
  rw [contrast_eq_centeredWeight_dot hN hn, hw]
  simp

/-- Probability of the upper-tail event for the centered exchangeable
contrast. -/
noncomputable def exchangeableUpperTail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {N n : ℕ} (hn : n ≤ N) (X : Ω → Fin N → ℝ)
    (w : Fin n → ℝ) (u : ℝ) : ℝ :=
  μ.real {ω | u ≤ contrast hn (X ω) w}

theorem exchangeableUpperTail_le_chernoff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {N n : ℕ} (hn : n ≤ N) (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (w : Fin n → ℝ) (u t : ℝ) (ht : 0 ≤ t)
    (hint : Integrable (fun ω ↦ Real.exp (t * contrast hn (X ω) w)) μ) :
    exchangeableUpperTail μ hn X w u ≤
      Real.exp (-t * u) * exchangeableMgf μ hn X w t := by
  let s : Set Ω := {ω | u ≤ contrast hn (X ω) w}
  have hs : MeasurableSet s :=
    stronglyMeasurable_const.measurableSet_le
      (stronglyMeasurable_contrast hn X hXmeas w)
  have hind : Integrable (s.indicator fun _ ↦ (1 : ℝ)) μ :=
    (integrable_const 1).indicator hs
  have hright : Integrable
      (fun ω ↦ Real.exp (-t * u) * Real.exp (t * contrast hn (X ω) w)) μ :=
    hint.const_mul _
  have hle : (fun ω ↦ s.indicator (fun _ ↦ (1 : ℝ)) ω) ≤
      fun ω ↦ Real.exp (-t * u) * Real.exp (t * contrast hn (X ω) w) := by
    intro ω
    change s.indicator (fun _ ↦ (1 : ℝ)) ω ≤
      Real.exp (-t * u) * Real.exp (t * contrast hn (X ω) w)
    by_cases hω : ω ∈ s
    · rw [Set.indicator_of_mem hω, ← Real.exp_add]
      apply Real.one_le_exp
      dsimp [s] at hω
      nlinarith
    · rw [Set.indicator_of_notMem hω]
      positivity
  have hInt := integral_mono hind hright hle
  unfold exchangeableUpperTail exchangeableMgf
  rw [← integral_indicator_one hs]
  calc
    (∫ ω, s.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) ≤
        ∫ ω, Real.exp (-t * u) * Real.exp (t * contrast hn (X ω) w) ∂μ := hInt
    _ = Real.exp (-t * u) *
        ∫ ω, Real.exp (t * contrast hn (X ω) w) ∂μ := integral_const_mul _ _

theorem sqNorm_pos_of_ne_zero {N : ℕ} {y : Fin N → ℝ}
    (hy : y ≠ fun _ ↦ 0) : 0 < sqNorm y := by
  have hex : ∃ i, y i ≠ 0 := by
    by_contra h
    push Not at h
    apply hy
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  unfold sqNorm
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hi)
    (Finset.single_le_sum (fun j hj ↦ sq_nonneg (y j)) (Finset.mem_univ i))

/-- Chernoff tail part of manuscript Corollary `cor:weighted-exchangeable`. -/
theorem weighted_exchangeable_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N n : ℕ} (hN : 2 ≤ N)
    (hn : n ≤ N) {a b : ℝ} (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (hX : ∀ ω j, a ≤ X ω j ∧ X ω j ≤ b)
    (hEx : IsExchangeable μ X) (w : Fin n → ℝ)
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
  have hlog := weighted_exchangeable_mgf_centeredNorm μ hN hn X hXmeas hX hEx w t
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

/-- Degenerate clause of manuscript Corollary `cor:weighted-exchangeable`:
if `w° = 0`, the contrast vanishes pointwise. -/
theorem exchangeable_contrast_eq_zero_of_centeredWeight_eq_zero
    {Ω : Type*} {N n : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (X : Ω → Fin N → ℝ) (w : Fin n → ℝ)
    (hw : centeredWeight hn w = fun _ ↦ 0) :
    ∀ ω, contrast hn (X ω) w = 0 := by
  intro ω
  exact contrast_eq_zero_of_centeredWeight_eq_zero hN hn (X ω) w hw

end SharpSerfling.FinitePopulation
