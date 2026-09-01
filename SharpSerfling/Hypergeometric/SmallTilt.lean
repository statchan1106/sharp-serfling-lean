import SharpSerfling.Hypergeometric.Variance
import SharpSerfling.Hypergeometric.Variational
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace SharpSerfling.Hypergeometric

open scoped BigOperators
open Filter Topology Set

noncomputable def centeredMoment1 (N K m : ℕ) (t : ℝ) : ℝ :=
  SharpSerfling.finiteAverage fun s : Sample N m ↦
    ((count K s : ℝ) - center N K m) *
      Real.exp (t * ((count K s : ℝ) - center N K m))

noncomputable def centeredMoment2 (N K m : ℕ) (t : ℝ) : ℝ :=
  SharpSerfling.finiteAverage fun s : Sample N m ↦
    ((count K s : ℝ) - center N K m) ^ 2 *
      Real.exp (t * ((count K s : ℝ) - center N K m))

theorem hasDerivAt_centeredMoment1 (N K m : ℕ) (t : ℝ) :
    HasDerivAt (centeredMoment1 N K m) (centeredMoment2 N K m t) t := by
  have hs (s : Sample N m) :
      HasDerivAt
        (fun u : ℝ ↦ ((count K s : ℝ) - center N K m) *
          Real.exp (u * ((count K s : ℝ) - center N K m)))
        (((count K s : ℝ) - center N K m) ^ 2 *
          Real.exp (t * ((count K s : ℝ) - center N K m))) t := by
    have he : HasDerivAt
        (fun u : ℝ ↦ Real.exp
          (u * ((count K s : ℝ) - center N K m)))
        (((count K s : ℝ) - center N K m) *
          Real.exp (t * ((count K s : ℝ) - center N K m))) t := by
      simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
        hasDerivAt_exp_smul_const'
          ((count K s : ℝ) - center N K m) t
    simpa [pow_two, mul_assoc] using
      he.const_mul ((count K s : ℝ) - center N K m)
  unfold centeredMoment1 centeredMoment2 SharpSerfling.finiteAverage
  exact (HasDerivAt.fun_sum fun s (_ : s ∈ Finset.univ) ↦ hs s).div_const
    (Fintype.card (Sample N m) : ℝ)

theorem hasDerivAt_log_mgf {N K m : ℕ} (hm : m ≤ N) (t : ℝ) :
    HasDerivAt (fun u ↦ Real.log (mgf N K m u))
      (centeredMoment1 N K m t / mgf N K m t) t := by
  have hm' := hasDerivAt_mgf N K m t
  have hpos := mgf_pos (N := N) (K := K) hm t
  simpa [centeredMoment1] using hm'.log (ne_of_gt hpos)

theorem centeredMoment1_zero {N K m : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (hm0 : 0 < m) :
    centeredMoment1 N K m 0 = 0 := by
  simpa [centeredMoment1] using
    finiteAverage_centered_count_eq_zero hK0 hKN hm0

theorem centeredMoment2_zero (N K m : ℕ) :
    centeredMoment2 N K m 0 = actualVariance N K m := by
  simp [centeredMoment2, actualVariance]

theorem deriv_log_mgf_zero {N K m : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (hm0 : 0 < m) (hmN : m < N) :
    deriv (fun u ↦ Real.log (mgf N K m u)) 0 = 0 := by
  rw [(hasDerivAt_log_mgf (Nat.le_of_lt hmN) 0).deriv,
    centeredMoment1_zero hK0 hKN hm0, zero_div]

theorem second_deriv_log_mgf_zero {N K m : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (hm0 : 0 < m) (hmN : m < N) :
    deriv (deriv (fun u ↦ Real.log (mgf N K m u))) 0 =
      variance N K m := by
  have hderiv :
      deriv (fun u ↦ Real.log (mgf N K m u)) =
        fun t ↦ centeredMoment1 N K m t / mgf N K m t := by
    funext t
    exact (hasDerivAt_log_mgf (Nat.le_of_lt hmN) t).deriv
  rw [hderiv]
  have hquot := (hasDerivAt_centeredMoment1 N K m 0).div
    (hasDerivAt_mgf N K m 0)
    (ne_of_gt (mgf_pos (N := N) (K := K) (Nat.le_of_lt hmN) 0))
  change deriv (centeredMoment1 N K m / mgf N K m) 0 = variance N K m
  rw [hquot.deriv, centeredMoment1_zero hK0 hKN hm0,
    centeredMoment2_zero, mgf_zero_of_le N K m (Nat.le_of_lt hmN)]
  norm_num
  exact actualVariance_eq_variance_of_interior hK0 hKN hm0 hmN

theorem contDiff_log_mgf_two {N K m : ℕ} (hm : m ≤ N) :
    ContDiff ℝ 2 (fun t ↦ Real.log (mgf N K m t)) := by
  have hmgf : ContDiff ℝ 2 (mgf N K m) := by
    unfold mgf SharpSerfling.finiteAverage
    fun_prop
  exact hmgf.log (fun t ↦ ne_of_gt (mgf_pos (N := N) (K := K) hm t))

theorem taylorWithinEval_log_mgf_two_zero {N K m : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (hm0 : 0 < m) (hmN : m < N) (t : ℝ) :
    taylorWithinEval (fun u ↦ Real.log (mgf N K m u)) 2 Set.univ 0 t =
      variance N K m / 2 * t ^ 2 := by
  rw [show 2 = 1 + 1 by omega, taylorWithinEval_succ,
    taylorWithinEval_succ, taylor_within_zero_eval]
  rw [mgf_zero_of_le N K m (Nat.le_of_lt hmN), Real.log_one]
  simp only [zero_add, Nat.cast_one, Nat.factorial_zero, mul_one, inv_one,
    sub_zero, one_mul, one_smul, Nat.cast_ofNat, Nat.factorial_one,
    iteratedDerivWithin_univ, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [deriv_log_mgf_zero hK0 hKN hm0 hmN,
    second_deriv_log_mgf_zero hK0 hKN hm0 hmN]
  norm_num
  ring

/-- General small-tilt limit: the normalized log-MGF ratio converges to
one half of the variance-to-proxy ratio. -/
theorem tendsto_normalizedLogMgf_zero {N K m : ℕ}
    (hK0 : 0 < K) (hKN : K < N) (hm0 : 0 < m) (hmN : m < N) :
    Tendsto (normalizedLogMgf N K m) (nhdsWithin 0 {0}ᶜ)
      (nhds (variance N K m /
        (2 * SharpSerfling.hypergeomScale N m))) := by
  let f : ℝ → ℝ := fun t ↦ Real.log (mgf N K m t)
  have htaylor := Real.taylor_tendsto (f := f) (n := 2)
    convex_univ (mem_univ (0 : ℝ))
    (contDiff_log_mgf_two (Nat.le_of_lt hmN)).contDiffOn
  have htaylor' : Tendsto
      (fun t ↦ (f t - variance N K m / 2 * t ^ 2) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have htaylor0 : Tendsto
        (fun t ↦ (f t - taylorWithinEval f 2 Set.univ 0 t) / t ^ 2)
        (nhds 0) (nhds 0) := by
      simpa only [nhdsWithin_univ, sub_zero] using htaylor
    have hmono : Tendsto
        (fun t ↦ (f t - taylorWithinEval f 2 Set.univ 0 t) / t ^ 2)
        (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
      htaylor0.mono_left inf_le_left
    have htpoly (t : ℝ) :
        taylorWithinEval f 2 Set.univ 0 t =
          variance N K m / 2 * t ^ 2 := by
      dsimp [f]
      exact taylorWithinEval_log_mgf_two_zero hK0 hKN hm0 hmN t
    simpa only [htpoly] using hmono
  have hconst : Tendsto (fun _ : ℝ ↦ variance N K m / 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (variance N K m / 2)) := tendsto_const_nhds
  have hadd := htaylor'.add hconst
  have hratio : Tendsto (fun t ↦ f t / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (variance N K m / 2)) := by
    have hadd' : Tendsto
        (fun x ↦ (f x - variance N K m / 2 * x ^ 2) / x ^ 2 +
          variance N K m / 2)
        (nhdsWithin 0 {0}ᶜ) (nhds (variance N K m / 2)) := by
      simpa only [zero_add] using hadd
    apply hadd'.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    field_simp [ht0]
    ring
  have hdiv := hratio.div_const (SharpSerfling.hypergeomScale N m)
  have hfun : normalizedLogMgf N K m =
      fun t ↦ (f t / t ^ 2) / SharpSerfling.hypergeomScale N m := by
    funext t
    unfold normalizedLogMgf
    dsimp [f]
    ring
  have hval : variance N K m /
      (2 * SharpSerfling.hypergeomScale N m) =
        (variance N K m / 2) / SharpSerfling.hypergeomScale N m := by ring
  rw [hfun, hval]
  exact hdiv

/-- The fixed-`m` equality case asserted in Proposition 1 for even `N`:
at the central number of marked items, the ratio tends to one as `t → 0`
through nonzero values, for every nontrivial draw size. -/
theorem tendsto_normalizedLogMgf_even_central {q m : ℕ} (hq : 0 < q)
    (hm0 : 1 ≤ m) (hmN : m ≤ 2 * q - 1) :
    Tendsto (normalizedLogMgf (2 * q) q m) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have hlim := tendsto_normalizedLogMgf_zero
    (N := 2 * q) (K := q) (m := m) (by omega) (by omega) (by omega) (by omega)
  have hval : variance (2 * q) q m /
      (2 * SharpSerfling.hypergeomScale (2 * q) m) = 1 := by
    have hv := variance_div_hypergeomScale (N := 2 * q) (K := q) (m := m)
      (by omega) (by omega) (by omega)
    have himb : imbalance (2 * q) q = 0 := by
      unfold imbalance
      push_cast
      rw [show 2 * (q : ℝ) - 2 * (q : ℝ) = 0 by ring, abs_zero, zero_div]
    rw [himb] at hv
    norm_num at hv
    have hscale : SharpSerfling.hypergeomScale (2 * q) m ≠ 0 :=
      ne_of_gt (hypergeomScale_pos_of_nontrivial (by omega) hm0 hmN)
    calc
      variance (2 * q) q m /
          (2 * SharpSerfling.hypergeomScale (2 * q) m) =
        (variance (2 * q) q m /
          SharpSerfling.hypergeomScale (2 * q) m) / 2 := by
            field_simp [hscale]
      _ = 1 := by rw [hv]; norm_num
  simpa [hval] using hlim

end SharpSerfling.Hypergeometric
