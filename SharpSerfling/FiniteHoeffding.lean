import SharpSerfling.FiniteAverage
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

namespace SharpSerfling

open MeasureTheory ProbabilityTheory

/-- Integration against the uniform probability measure on a nonempty finite type
is the explicit finite average used throughout this development. -/
theorem integral_uniformOfFintype_eq_finiteAverage
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    letI : MeasurableSpace Ω := ⊤
    ∫ x, f x ∂(PMF.uniformOfFintype Ω).toMeasure = finiteAverage f := by
  letI : MeasurableSpace Ω := ⊤
  rw [MeasureTheory.integral_fintype (MeasureTheory.Integrable.of_finite)]
  simp only [Measure.real_def, PMF.toMeasure_uniformOfFintype_apply,
    MeasurableSet.singleton, Fintype.card_unique, Nat.cast_one, one_div,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, finiteAverage]
  rw [← Finset.mul_sum]
  ring

/-- Hoeffding's lemma for the explicit uniform average on a finite type. -/
theorem finiteAverage_exp_le_of_mem_Icc_of_average_eq_zero
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ)
    {a b : ℝ} (hX : ∀ ω, X ω ∈ Set.Icc a b)
    (hmean : finiteAverage X = 0) (t : ℝ) :
    finiteAverage (fun ω => Real.exp (t * X ω)) ≤
      Real.exp ((b - a) ^ 2 * t ^ 2 / 8) := by
  letI : MeasurableSpace Ω := ⊤
  let μ : Measure Ω := (PMF.uniformOfFintype Ω).toMeasure
  have huniform (f : Ω → ℝ) : ∫ x, f x ∂μ = finiteAverage f := by
    exact integral_uniformOfFintype_eq_finiteAverage f
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := μ) (X := X) AEMeasurable.of_discrete (Filter.Eventually.of_forall hX)
    (by rw [huniform, hmean])
  have hbound := hsub.mgf_le t
  rw [ProbabilityTheory.mgf, huniform] at hbound
  convert hbound using 1
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have hab : a ≤ b := (hX ω).1.trans (hX ω).2
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat]
  rw [Real.nnnorm_of_nonneg (sub_nonneg.mpr hab)]
  simp only [NNReal.coe_mk]
  ring

end SharpSerfling
