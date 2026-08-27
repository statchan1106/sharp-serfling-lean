import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

namespace SharpSerfling.Analysis

open Set

/-- Rolle's theorem applied between two zeroes of an iterated derivative. -/
theorem exists_next_iteratedDeriv_eq_zero {f : ℝ → ℝ} {n : ℕ} {a b : ℝ}
    (hf : ContDiff ℝ (n + 1) f) (hab : a < b)
    (ha : iteratedDeriv n f a = 0) (hb : iteratedDeriv n f b = 0) :
    ∃ c ∈ Ioo a b, iteratedDeriv (n + 1) f c = 0 := by
  have hc : Continuous (iteratedDeriv n f) :=
    hf.continuous_iteratedDeriv n (by norm_num)
  obtain ⟨c, hcI, hcd⟩ :=
    exists_deriv_eq_zero hab hc.continuousOn (ha.trans hb.symm)
  refine ⟨c, hcI, ?_⟩
  rwa [iteratedDeriv_succ]

/-- A `C⁵` function with three ordered double zeroes has a zero of its fifth
derivative strictly between the outer zeroes.  This is the repeated-Rolle
step in the Hermite interpolation sign lemma. -/
theorem exists_iteratedDeriv_five_eq_zero_of_three_double_roots
    {f : ℝ → ℝ} (hf : ContDiff ℝ 5 f)
    {x₁ x₂ x₃ : ℝ} (h12 : x₁ < x₂) (h23 : x₂ < x₃)
    (hf1 : f x₁ = 0) (hf2 : f x₂ = 0) (hf3 : f x₃ = 0)
    (hdf1 : iteratedDeriv 1 f x₁ = 0)
    (hdf2 : iteratedDeriv 1 f x₂ = 0)
    (hdf3 : iteratedDeriv 1 f x₃ = 0) :
    ∃ ξ ∈ Ioo x₁ x₃, iteratedDeriv 5 f ξ = 0 := by
  have hf1c : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hf2c : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hf3c : ContDiff ℝ 3 f := hf.of_le (by norm_num)
  have hf4c : ContDiff ℝ 4 f := hf.of_le (by norm_num)
  obtain ⟨a, haI, ha⟩ :=
    exists_next_iteratedDeriv_eq_zero hf1c h12
      (by simpa only [iteratedDeriv_zero] using hf1)
      (by simpa only [iteratedDeriv_zero] using hf2)
  obtain ⟨b, hbI, hb⟩ :=
    exists_next_iteratedDeriv_eq_zero hf1c h23
      (by simpa only [iteratedDeriv_zero] using hf2)
      (by simpa only [iteratedDeriv_zero] using hf3)
  obtain ⟨c₁, hc1I, hc1⟩ :=
    exists_next_iteratedDeriv_eq_zero hf2c haI.1 hdf1 ha
  obtain ⟨c₂, hc2I, hc2⟩ :=
    exists_next_iteratedDeriv_eq_zero hf2c haI.2 ha hdf2
  obtain ⟨c₃, hc3I, hc3⟩ :=
    exists_next_iteratedDeriv_eq_zero hf2c hbI.1 hdf2 hb
  obtain ⟨c₄, hc4I, hc4⟩ :=
    exists_next_iteratedDeriv_eq_zero hf2c hbI.2 hb hdf3
  obtain ⟨d₁, hd1I, hd1⟩ :=
    exists_next_iteratedDeriv_eq_zero hf3c (hc1I.2.trans hc2I.1) hc1 hc2
  obtain ⟨d₂, hd2I, hd2⟩ :=
    exists_next_iteratedDeriv_eq_zero hf3c (hc2I.2.trans hc3I.1) hc2 hc3
  obtain ⟨d₃, hd3I, hd3⟩ :=
    exists_next_iteratedDeriv_eq_zero hf3c (hc3I.2.trans hc4I.1) hc3 hc4
  obtain ⟨e₁, he1I, he1⟩ :=
    exists_next_iteratedDeriv_eq_zero hf4c (hd1I.2.trans hd2I.1) hd1 hd2
  obtain ⟨e₂, he2I, he2⟩ :=
    exists_next_iteratedDeriv_eq_zero hf4c (hd2I.2.trans hd3I.1) hd2 hd3
  obtain ⟨ξ, hξI, hξ⟩ :=
    exists_next_iteratedDeriv_eq_zero hf (he1I.2.trans he2I.1) he1 he2
  refine ⟨ξ, ⟨?_, ?_⟩, hξ⟩
  · exact hc1I.1.trans (hd1I.1.trans (he1I.1.trans hξI.1))
  · exact hξI.2.trans (he2I.2.trans (hd3I.2.trans hc4I.2))

end SharpSerfling.Analysis
