import SharpSerfling.Hypergeometric.Definitions
import Mathlib.Analysis.Calculus.Deriv.Add

namespace SharpSerfling.Hypergeometric

open scoped BigOperators

/-- Termwise differentiation of the explicit finite hypergeometric MGF. -/
theorem hasDerivAt_mgf (N K m : ℕ) (t : ℝ) :
    HasDerivAt (mgf N K m)
      (SharpSerfling.finiteAverage fun s : Sample N m =>
        ((count K s : ℝ) - center N K m) *
          Real.exp (t * ((count K s : ℝ) - center N K m))) t := by
  have hs (s : Sample N m) :
      HasDerivAt (fun u : ℝ => Real.exp (u * ((count K s : ℝ) - center N K m)))
        (((count K s : ℝ) - center N K m) *
          Real.exp (t * ((count K s : ℝ) - center N K m))) t := by
    simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
      hasDerivAt_exp_smul_const' ((count K s : ℝ) - center N K m) t
  change HasDerivAt
    (fun u : ℝ => (∑ s : Sample N m,
      Real.exp (u * ((count K s : ℝ) - center N K m))) /
        (Fintype.card (Sample N m) : ℝ))
    ((∑ s : Sample N m, ((count K s : ℝ) - center N K m) *
      Real.exp (t * ((count K s : ℝ) - center N K m))) /
        (Fintype.card (Sample N m) : ℝ)) t
  exact (HasDerivAt.fun_sum fun s (_ : s ∈ Finset.univ) => hs s).div_const
    (Fintype.card (Sample N m) : ℝ)

theorem deriv_mgf (N K m : ℕ) (t : ℝ) :
    deriv (mgf N K m) t =
      SharpSerfling.finiteAverage fun s : Sample N m =>
        ((count K s : ℝ) - center N K m) *
          Real.exp (t * ((count K s : ℝ) - center N K m)) :=
  (hasDerivAt_mgf N K m t).deriv

end SharpSerfling.Hypergeometric
