import SharpSerfling.Certificates.CentralParameters
import SharpSerfling.Hypergeometric.Symmetries

namespace SharpSerfling.Hypergeometric

/-- Simultaneous odd-population induction once its one- and two-draw base
cases have been supplied.  All recursive slices, including the hard central
one, are discharged internally. -/
theorem odd_mgf_le_half_nonneg_of_bases
    (hone : ∀ {N K : ℕ} {t : ℝ}, 3 ≤ N → Odd N → K ≤ N →
      mgf N K 1 t ≤ Real.exp (oddProxyScale N 1 * t ^ 2 / 2))
    (htwo : ∀ {N : ℕ} {t : ℝ}, 5 ≤ N → Odd N →
      mgf N ((N - 1) / 2) 2 t ≤ Real.exp (oddProxyScale N 2 * t ^ 2 / 2)) :
    ∀ m N K : ℕ, ∀ t : ℝ, 3 ≤ N → Odd N →
      m ≤ (N - 1) / 2 → K ≤ N → 0 ≤ t →
      mgf N K m t ≤ Real.exp (oddProxyScale N m * t ^ 2 / 2) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro N K t hN hOdd hmHalf hK ht
      by_cases hm0eq : m = 0
      · subst m
        simp [mgf_zeroSample, oddProxyScale]
      by_cases hm1eq : m = 1
      · subst m
        exact hone hN hOdd hK
      have hm2 : 2 ≤ m := by omega
      have hm0 : 0 < m := by omega
      have hmN : m < N := by omega
      have hN5 : 5 ≤ N := by omega
      by_cases hK0eq : K = 0
      · subst K
        rw [mgf_zeroSuccesses (by omega)]
        exact Real.one_le_exp
          (mul_nonneg
            (mul_nonneg (oddProxyScale_pos (by omega) hm0 hmN).le (sq_nonneg t))
            (by norm_num))
      by_cases hKNeq : K = N
      · subst K
        rw [mgf_allSuccesses (by omega) (by omega)]
        exact Real.one_le_exp
          (mul_nonneg
            (mul_nonneg (oddProxyScale_pos (by omega) hm0 hmN).le (sq_nonneg t))
            (by norm_num))
      have hK0 : 0 < K := Nat.pos_of_ne_zero hK0eq
      have hKN : K < N := lt_of_le_of_ne hK hKNeq
      have hOddRed : Odd (N - 2) := by
        obtain ⟨q, hq⟩ := hOdd
        use q - 1
        omega
      have hred : ∀ u : ℝ, 0 ≤ u →
          mgf (N - 2) (K - 1) (m - 1) u ≤
            Real.exp (oddProxyScale (N - 2) (m - 1) * u ^ 2 / 2) := by
        intro u hu
        exact ih (m - 1) (by omega) (N - 2) (K - 1) u (by omega) hOddRed
          (by omega) (by omega) hu
      by_cases hLower : K = (N - 1) / 2
      · subst K
        by_cases hm2eq : m = 2
        · subst m
          exact htwo hN5 hOdd
        · have hm3 : 3 ≤ m := by omega
          exact mgf_le_oddProxy_lowerNearest_of_reduced (by omega) hOdd hm3 hmHalf hred ht
      by_cases hUpper : K = (N + 1) / 2
      · subst K
        exact mgf_le_oddProxy_upperNearest_of_reduced hN5 hOdd hm2
          hmHalf hred ht
      have hfar : 3 / (N : ℝ) ≤ imbalance N K :=
        imbalance_far_of_ne_nearest hN hOdd hK hLower hUpper
      exact mgf_le_oddProxy_noncentral_of_reduced hN5 hOdd hK0 hKN
        hm2 hmHalf hfar hred ht

/-- Extension of the half-sample induction to all real tilts. -/
theorem odd_mgf_le_half_of_bases
    (hone : ∀ {N K : ℕ} {t : ℝ}, 3 ≤ N → Odd N → K ≤ N →
      mgf N K 1 t ≤ Real.exp (oddProxyScale N 1 * t ^ 2 / 2))
    (htwo : ∀ {N : ℕ} {t : ℝ}, 5 ≤ N → Odd N →
      mgf N ((N - 1) / 2) 2 t ≤ Real.exp (oddProxyScale N 2 * t ^ 2 / 2))
    {N K m : ℕ} (hN : 3 ≤ N) (hOdd : Odd N)
    (hmHalf : m ≤ (N - 1) / 2) (hK : K ≤ N) (t : ℝ) :
    mgf N K m t ≤ Real.exp (oddProxyScale N m * t ^ 2 / 2) := by
  by_cases ht : 0 ≤ t
  · exact odd_mgf_le_half_nonneg_of_bases hone htwo m N K t hN hOdd hmHalf hK ht
  · have hbound := odd_mgf_le_half_nonneg_of_bases hone htwo m N (N - K) (-t)
      hN hOdd hmHalf (Nat.sub_le N K) (by linarith)
    rw [mgf_successComplement (by omega) hK (-t)] at hbound
    simpa only [neg_neg, neg_sq] using hbound

/-- Full odd-population sharp MGF reduction, with only the explicit one- and
two-draw analytic base cases left as inputs. -/
theorem odd_mgf_le_of_bases
    (hone : ∀ {N K : ℕ} {t : ℝ}, 3 ≤ N → Odd N → K ≤ N →
      mgf N K 1 t ≤ Real.exp (oddProxyScale N 1 * t ^ 2 / 2))
    (htwo : ∀ {N : ℕ} {t : ℝ}, 5 ≤ N → Odd N →
      mgf N ((N - 1) / 2) 2 t ≤ Real.exp (oddProxyScale N 2 * t ^ 2 / 2))
    {N K m : ℕ} (hN : 3 ≤ N) (hOdd : Odd N)
    (hK : K ≤ N) (hm : m ≤ N) (t : ℝ) :
    mgf N K m t ≤ Real.exp (oddProxyScale N m * t ^ 2 / 2) := by
  by_cases hmHalf : m ≤ (N - 1) / 2
  · exact odd_mgf_le_half_of_bases hone htwo hN hOdd hmHalf hK t
  · have hcompHalf : N - m ≤ (N - 1) / 2 := by
      obtain ⟨q, hq⟩ := hOdd
      omega
    have hbound := odd_mgf_le_half_of_bases hone htwo hN hOdd hcompHalf hK (-t)
    rw [mgf_sampleComplement (by omega) hK hm (-t)] at hbound
    rw [oddProxyScale_symm hm] at hbound
    simpa only [neg_neg, neg_sq] using hbound

end SharpSerfling.Hypergeometric
