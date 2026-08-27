import SharpSerfling.FinitePopulation.Optimality
import SharpSerfling.FinitePopulation.ExchangeableLaw

namespace SharpSerfling.FinitePopulation

open MeasureTheory

/-- The uniform random permutation construction is exchangeable in the
standard pushforward-law sense. -/
theorem isExchangeableInLaw_uniformPermutation {N : ℕ} (x : Fin N → ℝ) :
    letI : MeasurableSpace (Equiv.Perm (Fin N)) := ⊤
    IsExchangeableInLaw
      (PMF.uniformOfFintype (Equiv.Perm (Fin N))).toMeasure
      (fun σ j ↦ x (σ j)) := by
  classical
  letI : MeasurableSpace (Equiv.Perm (Fin N)) := ⊤
  intro π
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply Measurable.of_discrete hs,
    Measure.map_apply Measurable.of_discrete hs,
    PMF.toMeasure_uniformOfFintype_apply _ (by simp),
    PMF.toMeasure_uniformOfFintype_apply _ (by simp)]
  let e : Equiv.Perm (Fin N) ≃ Equiv.Perm (Fin N) := Equiv.mulRight π
  let es : {σ : Equiv.Perm (Fin N) // (fun j ↦ x (σ (π j))) ∈ s} ≃
      {σ : Equiv.Perm (Fin N) // (fun j ↦ x (σ j)) ∈ s} := {
    toFun σ := ⟨e σ, by simpa [e] using σ.property⟩
    invFun σ := ⟨e.symm σ, by simpa [e] using σ.property⟩
    left_inv σ := by ext; simp [e]
    right_inv σ := by ext; simp [e]
  }
  congr 1
  exact_mod_cast Fintype.card_congr es

/-- Candidate coefficient for all bounded exchangeable laws, using the
standard equality-in-distribution definition. -/
def ExchangeableInLawUniformCoefficient (N : ℕ) (c : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) (hn : n ≤ N)
    (a b : ℝ) (X : Ω → Fin N → ℝ),
    (∀ j, StronglyMeasurable (fun ω ↦ X ω j)) →
    (∀ ω j, a ≤ X ω j ∧ X ω j ≤ b) →
    IsExchangeableInLaw μ X →
    ∀ (w : Fin n → ℝ) (lam : ℝ),
    Real.log (exchangeableMgf μ hn X w lam) ≤
      lam ^ 2 * (b - a) ^ 2 / 8 *
        (c * (N : ℝ) / ((N : ℝ) - 1)) * sqNorm (centeredWeight hn w)

theorem exchangeableInLawUniformCoefficient_kappa {N : ℕ} (hN : 2 ≤ N) :
    ExchangeableInLawUniformCoefficient N (SharpSerfling.kappa N) := by
  intro Ω mΩ μ hμ n hn a b X hXmeas hX hEx w lam
  exact weighted_exchangeable_mgf_centeredNorm_inLaw
    μ hN hn X hXmeas hX hEx w lam

theorem weightedUniform_of_exchangeableInLawUniform {N : ℕ} (hN : 2 ≤ N)
    {c : ℝ} (hc : ExchangeableInLawUniformCoefficient N c) :
    WeightedUniformCoefficient N c := by
  intro n hn a b x hx w lam
  let Ω := Equiv.Perm (Fin N)
  letI : MeasurableSpace Ω := ⊤
  let μ : Measure Ω := (PMF.uniformOfFintype Ω).toMeasure
  have hmeas : ∀ j, StronglyMeasurable (fun σ : Ω ↦ x (σ j)) := by
    intro j
    exact StronglyMeasurable.of_discrete
  have hrange : ∀ (σ : Ω) j, a ≤ x (σ j) ∧ x (σ j) ≤ b := by
    intro σ j
    exact hx (σ j)
  have hEx : IsExchangeableInLaw μ (fun σ j ↦ x (σ j)) :=
    isExchangeableInLaw_uniformPermutation x
  have hbound := hc Ω μ n hn a b (fun σ j ↦ x (σ j))
    hmeas hrange hEx w lam
  rw [exchangeableMgf_uniformPermutation hn x w lam] at hbound
  have hnorm := sum_sq_centeredWeight_eq_rho hN hn w
  change sqNorm (centeredWeight hn w) = _ at hnorm
  calc
    Real.log (mgf hn x w lam) ≤
        lam ^ 2 * (b - a) ^ 2 / 8 * (c * (N : ℝ) / ((N : ℝ) - 1)) *
          sqNorm (centeredWeight hn w) := hbound
    _ = c / 8 * SharpSerfling.rho N n w * (b - a) ^ 2 * lam ^ 2 := by
      rw [hnorm]
      have hNR : (N : ℝ) ≠ 0 := by positivity
      have hNm1 : (N : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
        linarith
      field_simp [hNR, hNm1]

/-- Exact validity and minimality of the exchangeable multiplier under the
standard equality-in-law definition. -/
theorem exchangeableInLaw_sharp_constant {N : ℕ} (hN : 2 ≤ N) :
    ExchangeableInLawUniformCoefficient N (SharpSerfling.kappa N) ∧
      ∀ c : ℝ, ExchangeableInLawUniformCoefficient N c →
        SharpSerfling.kappa N ≤ c := by
  constructor
  · exact exchangeableInLawUniformCoefficient_kappa hN
  · intro c hc
    exact (finitePopulation_sharp_constant hN).2 c
      (weightedUniform_of_exchangeableInLawUniform hN hc)

/-- Candidate coefficient in the literal `C * ‖w°‖²` normalization of
Corollary 2. -/
def ExchangeableInLawCoefficient (N : ℕ) (C : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) (hn : n ≤ N)
    (a b : ℝ) (X : Ω → Fin N → ℝ),
    (∀ j, StronglyMeasurable (fun ω ↦ X ω j)) →
    (∀ ω j, a ≤ X ω j ∧ X ω j ≤ b) →
    IsExchangeableInLaw μ X →
    ∀ (w : Fin n → ℝ) (lam : ℝ),
    Real.log (exchangeableMgf μ hn X w lam) ≤
      lam ^ 2 * (b - a) ^ 2 / 8 * C * sqNorm (centeredWeight hn w)

theorem exchangeableInLawCoefficient_sharp_value {N : ℕ} (hN : 2 ≤ N) :
    ExchangeableInLawCoefficient N
      (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) := by
  intro Ω mΩ μ hμ n hn a b X hXmeas hX hEx w lam
  exact weighted_exchangeable_mgf_centeredNorm_inLaw
    μ hN hn X hXmeas hX hEx w lam

theorem exchangeableInLawUniform_of_coefficient {N : ℕ} (hN : 2 ≤ N)
    {C : ℝ} (hC : ExchangeableInLawCoefficient N C) :
    ExchangeableInLawUniformCoefficient N
      (C * ((N : ℝ) - 1) / (N : ℝ)) := by
  intro Ω mΩ μ hμ n hn a b X hXmeas hX hEx w lam
  have hbound := hC Ω μ n hn a b X hXmeas hX hEx w lam
  convert hbound using 1
  have hNR : (N : ℝ) ≠ 0 := by positivity
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  field_simp [hNR, hNm1]

/-- Corollary 2 with the manuscript's literal optimal coefficient
`C_N^star = κ_N N/(N-1)`. -/
theorem exchangeableInLaw_Cstar_sharp_constant {N : ℕ} (hN : 2 ≤ N) :
    ExchangeableInLawCoefficient N
        (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) ∧
      ∀ C : ℝ, ExchangeableInLawCoefficient N C →
        SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1) ≤ C := by
  constructor
  · exact exchangeableInLawCoefficient_sharp_value hN
  · intro C hC
    have hk : SharpSerfling.kappa N ≤
        C * ((N : ℝ) - 1) / (N : ℝ) :=
      (exchangeableInLaw_sharp_constant hN).2 _
        (exchangeableInLawUniform_of_coefficient hN hC)
    have hNR : 0 < (N : ℝ) := by positivity
    have hNm1 : 0 < (N : ℝ) - 1 := by
      have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
      linarith
    calc
      SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1) ≤
          (C * ((N : ℝ) - 1) / (N : ℝ)) * (N : ℝ) /
            ((N : ℝ) - 1) := by
        gcongr
      _ = C := by field_simp [ne_of_gt hNR, ne_of_gt hNm1]

end SharpSerfling.FinitePopulation
