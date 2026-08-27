import SharpSerfling.Hypergeometric.Universal
import SharpSerfling.Certificates.Polynomial
import SharpSerfling.Analysis.SingleCrossing
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace SharpSerfling.Hypergeometric

open scoped BigOperators

/-- The logarithmic increment governing the sharp odd-population constant. -/
noncomputable def oddLogIncrement (N : ℕ) : ℝ :=
  Real.log (((N : ℝ) + 1) / ((N : ℝ) - 1))

/-- Twice the quadratic exponent coefficient in the odd-population proxy. -/
noncomputable def oddProxyScale (N m : ℕ) : ℝ :=
  SharpSerfling.kappa N *
    ((m : ℝ) * ((N : ℝ) - (m : ℝ)) / (4 * ((N : ℝ) - 1)))

noncomputable def oddAlpha (N m : ℕ) : ℝ :=
  ((N : ℝ) - 2 * (m : ℝ)) / ((N : ℝ) - 2)

noncomputable def oddGamma (N m : ℕ) : ℝ :=
  oddProxyScale N m - oddProxyScale (N - 2) (m - 1) - 1 / 12

noncomputable def centralEta (N : ℕ) : ℝ :=
  (((N : ℝ) ^ 2 - 1) * oddLogIncrement N) / (2 * (N : ℝ))

noncomputable def centralDeficit (N : ℕ) : ℝ :=
  -Real.log (centralEta N)

noncomputable def centralUpperRoot (N m : ℕ) : ℝ :=
  _root_.SharpSerfling.Analysis.hardCentralUpperRoot
    (centralDeficit N) (oddAlpha N m / (2 * (N : ℝ))) (oddGamma N m)

/-- The four numerical conclusions required from the manuscript's
central-parameter lemma at the larger crossing root. -/
structure CentralParameterCertificate (N m : ℕ) : Prop where
  a_lt_c : centralDeficit N <
    oddGamma N m * centralUpperRoot N m ^ 2 / 2
  c_lt_d : oddGamma N m * centralUpperRoot N m ^ 2 / 2 <
    oddProxyScale N m * centralUpperRoot N m ^ 2 / 2
  c_le_two_a : oddGamma N m * centralUpperRoot N m ^ 2 / 2 ≤
    2 * centralDeficit N
  singleCrossing : centralDeficit N ^ 3 +
      (oddGamma N m * centralUpperRoot N m ^ 2 / 2) *
        (oddProxyScale N m * centralUpperRoot N m ^ 2 / 2) ^ 2 *
          Real.exp (oddProxyScale N m * centralUpperRoot N m ^ 2 / 2) ≤
    (2 * centralDeficit N -
        oddGamma N m * centralUpperRoot N m ^ 2 / 2) *
      (oddProxyScale N m * centralUpperRoot N m ^ 2 / 2 -
        oddGamma N m * centralUpperRoot N m ^ 2 / 2)

/-- The odd proxy scale is twice `kappa` times the universal exponent scale. -/
theorem oddProxyScale_eq_two_mul (N m : ℕ) :
    oddProxyScale N m =
      2 * SharpSerfling.kappa N * SharpSerfling.hypergeomScale N m := by
  unfold oddProxyScale SharpSerfling.hypergeomScale
  simp only [div_eq_mul_inv, mul_inv]
  norm_num
  ring

theorem oddProxyScale_symm {N m : ℕ} (hm : m ≤ N) :
    oddProxyScale N (N - m) = oddProxyScale N m := by
  unfold oddProxyScale
  rw [Nat.cast_sub hm]
  ring

/-- The sample tilt used in the recursion is one half of the odd parameter. -/
theorem sampleTilt_eq_oddAlpha_div_two (N m : ℕ) :
    sampleTilt N m = oddAlpha N m / 2 := by
  unfold sampleTilt oddAlpha
  simp only [div_eq_mul_inv, mul_inv]
  norm_num
  ring

theorem oddProxyScale_pos {N m : ℕ}
    (hN : 2 ≤ N) (hm0 : 0 < m) (hmN : m < N) :
    0 < oddProxyScale N m := by
  rw [oddProxyScale_eq_two_mul]
  have hscale : 0 < SharpSerfling.hypergeomScale N m := by
    unfold SharpSerfling.hypergeomScale
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
    have hmNR : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
    have hN1 : 0 < (N : ℝ) - 1 := by
      have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
      linarith
    positivity
  exact mul_pos (mul_pos (by norm_num) (SharpSerfling.kappa_pos hN)) hscale

theorem oddAlpha_pos {N m : ℕ}
    (hN : 5 ≤ N) (hmHalf : m ≤ (N - 1) / 2) :
    0 < oddAlpha N m := by
  unfold oddAlpha
  have hmBound : 2 * m ≤ N - 1 := by omega
  have hmBoundR : 2 * (m : ℝ) ≤ (N : ℝ) - 1 := by
    have hcast : ((2 * m : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast hmBound
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega)] at hcast
    norm_num at hcast ⊢
    exact hcast
  have hden : 0 < (N : ℝ) - 2 := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
    linarith
  exact div_pos (by linarith) hden

/-- Exact variance-to-sharp-proxy factorization. -/
theorem variance_eq_oddProxyScale_mul {N K m : ℕ}
    (hN : 2 ≤ N) (hm0 : 0 < m) (hmN : m < N) :
    variance N K m = oddProxyScale N m *
      ((1 / SharpSerfling.kappa N) * (1 - imbalance N K ^ 2)) := by
  have hscale : 0 < SharpSerfling.hypergeomScale N m := by
    unfold SharpSerfling.hypergeomScale
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
    have hmNR : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
    have hN1 : 0 < (N : ℝ) - 1 := by
      have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
      linarith
    positivity
  have hratio := variance_div_hypergeomScale (N := N) (K := K) (m := m)
    hN hm0 hmN
  have hv : variance N K m =
      2 * (1 - imbalance N K ^ 2) * SharpSerfling.hypergeomScale N m :=
    (div_eq_iff (ne_of_gt hscale)).mp hratio
  rw [hv, oddProxyScale_eq_two_mul]
  field_simp [ne_of_gt (SharpSerfling.kappa_pos hN)]

theorem oddLogIncrement_eq_scaled_log {N : ℕ} (hN : 0 < N) :
    oddLogIncrement N =
      Real.log ((1 + (1 : ℝ) / N) / (1 - (1 : ℝ) / N)) := by
  unfold oddLogIncrement
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  congr 1
  field_simp [hNr]

theorem kappa_odd_upper {N : ℕ} (hN : 3 ≤ N) (hOdd : Odd N) :
    SharpSerfling.kappa N ≤ 1 := by
  have hnotEven : ¬Even N := Nat.not_even_iff_odd.mpr hOdd
  have hNr : 0 < (N : ℝ) := by positivity
  have hx0 : 0 ≤ (1 : ℝ) / N := by positivity
  have hx1 : (1 : ℝ) / N < 1 := by
    rw [div_lt_one hNr]
    exact_mod_cast (show 1 < N by omega)
  have hseries := Real.sum_range_le_log_div hx0 hx1 1
  norm_num at hseries
  have hlog : 2 / (N : ℝ) ≤ oddLogIncrement N := by
    rw [oddLogIncrement_eq_scaled_log (by omega)]
    calc
      2 / (N : ℝ) = 2 * (N : ℝ)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 2 * (1 / 2 * Real.log ((1 + (N : ℝ)⁻¹) / (1 - (N : ℝ)⁻¹))) :=
        mul_le_mul_of_nonneg_left hseries (by norm_num)
      _ = Real.log ((1 + 1 / (N : ℝ)) / (1 - 1 / (N : ℝ))) := by
        rw [one_div]
        ring
  have hlogPos : 0 < oddLogIncrement N :=
    lt_of_lt_of_le (by positivity : 0 < 2 / (N : ℝ)) hlog
  rw [SharpSerfling.kappa_of_not_even hnotEven]
  change 2 / ((N : ℝ) * oddLogIncrement N) ≤ 1
  rw [div_le_one (mul_pos hNr hlogPos)]
  have := mul_le_mul_of_nonneg_left hlog hNr.le
  calc
    2 = (N : ℝ) * (2 / (N : ℝ)) := by field_simp [ne_of_gt hNr]
    _ ≤ (N : ℝ) * oddLogIncrement N := this

/-- For an odd population the sharp multiplier is strictly smaller than one,
as stated after Theorem 1 in the manuscript. -/
theorem kappa_odd_lt_one {N : ℕ} (hN : 3 ≤ N) (hOdd : Odd N) :
    SharpSerfling.kappa N < 1 := by
  have hnotEven : ¬Even N := Nat.not_even_iff_odd.mpr hOdd
  have hNr : 0 < (N : ℝ) := by positivity
  have hx0 : 0 ≤ (1 : ℝ) / N := by positivity
  have hx1 : (1 : ℝ) / N < 1 := by
    rw [div_lt_one hNr]
    exact_mod_cast (show 1 < N by omega)
  have hseries := Real.sum_range_le_log_div hx0 hx1 2
  norm_num [Finset.sum_range_succ] at hseries
  have hstrict : (N : ℝ)⁻¹ <
      1 / 2 * Real.log ((1 + (N : ℝ)⁻¹) / (1 - (N : ℝ)⁻¹)) :=
    lt_of_lt_of_le (lt_add_of_pos_right _ (by positivity)) hseries
  have hlog : 2 / (N : ℝ) < oddLogIncrement N := by
    rw [oddLogIncrement_eq_scaled_log (by omega)]
    have hcalc : 2 * (N : ℝ)⁻¹ <
        Real.log ((1 + (N : ℝ)⁻¹) / (1 - (N : ℝ)⁻¹)) := by
      calc
        2 * (N : ℝ)⁻¹ <
            2 * (1 / 2 * Real.log ((1 + (N : ℝ)⁻¹) / (1 - (N : ℝ)⁻¹))) :=
          mul_lt_mul_of_pos_left hstrict (by norm_num)
        _ = Real.log ((1 + (N : ℝ)⁻¹) / (1 - (N : ℝ)⁻¹)) := by ring
    simpa only [one_div, div_eq_mul_inv, one_mul] using hcalc
  have hlogPos : 0 < oddLogIncrement N :=
    lt_trans (by positivity : 0 < 2 / (N : ℝ)) hlog
  rw [SharpSerfling.kappa_of_not_even hnotEven]
  change 2 / ((N : ℝ) * oddLogIncrement N) < 1
  rw [div_lt_one (mul_pos hNr hlogPos)]
  calc
    2 = (N : ℝ) * (2 / (N : ℝ)) := by field_simp [ne_of_gt hNr]
    _ < (N : ℝ) * oddLogIncrement N :=
      mul_lt_mul_of_pos_left hlog hNr

/-- The parity-independent upper bound used in the Serfling correction
comparison. -/
theorem kappa_le_one {N : ℕ} (hN : 2 ≤ N) :
    SharpSerfling.kappa N ≤ 1 := by
  by_cases hEven : Even N
  · rw [SharpSerfling.kappa_of_even hEven]
  · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
    obtain ⟨q, hq⟩ := hOdd
    exact kappa_odd_upper (by omega) ⟨q, hq⟩

theorem half_log_div_le_sharp_rational {x : ℝ}
    (hx0 : 0 ≤ x) (hx13 : x ≤ 1 / 3) :
    1 / 2 * Real.log ((1 + x) / (1 - x)) ≤ x / (1 - x ^ 2 / 2) := by
  have hx1 : x < 1 := lt_of_le_of_lt hx13 (by norm_num)
  have hseries := Real.log_div_le_sum_range_add hx0 hx1 2
  norm_num [Finset.sum_range_succ] at hseries
  have hxSq : x ^ 2 ≤ 1 / 9 := by nlinarith
  have hpoly : 0 ≤ 2 * x ^ 4 - 6 * x ^ 2 + 1 := by
    have hx4 : 0 ≤ x ^ 4 := by positivity
    nlinarith
  have hden1 : 0 < 1 - x ^ 2 := by nlinarith [sq_nonneg x]
  have hden2 : 0 < 1 - x ^ 2 / 2 := by nlinarith [sq_nonneg x]
  calc
    _ ≤ x + x ^ 3 / 3 + x ^ 5 / (1 - x ^ 2) := hseries
    _ ≤ x / (1 - x ^ 2 / 2) := by
      rw [le_div_iff₀ hden2]
      field_simp [ne_of_gt hden1]
      nlinarith [mul_nonneg hx0 hpoly]

theorem kappa_odd_lower {N : ℕ} (hN : 3 ≤ N) (hOdd : Odd N) :
    1 - 1 / (2 * (N : ℝ) ^ 2) ≤ SharpSerfling.kappa N := by
  have hnotEven : ¬Even N := Nat.not_even_iff_odd.mpr hOdd
  have hNr : 0 < (N : ℝ) := by positivity
  have hx0 : 0 ≤ (1 : ℝ) / N := by positivity
  have hx13 : (1 : ℝ) / N ≤ 1 / 3 := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hN)
  have hhalf := half_log_div_le_sharp_rational hx0 hx13
  have hlogUpper : oddLogIncrement N ≤
      (2 / (N : ℝ)) / (1 - 1 / (2 * (N : ℝ) ^ 2)) := by
    rw [oddLogIncrement_eq_scaled_log (by omega)]
    have htwice := mul_le_mul_of_nonneg_left hhalf (by norm_num : (0 : ℝ) ≤ 2)
    have htwice' : Real.log ((1 + (1 : ℝ) / N) / (1 - (1 : ℝ) / N)) ≤
        2 * ((1 / (N : ℝ)) / (1 - (1 / (N : ℝ)) ^ 2 / 2)) := by
      nlinarith
    calc
      _ ≤ _ := htwice'
      _ = _ := by
        field_simp [ne_of_gt hNr]
  have hfactorPos : 0 < 1 - 1 / (2 * (N : ℝ) ^ 2) := by
    rw [sub_pos, div_lt_one (by positivity : 0 < 2 * (N : ℝ) ^ 2)]
    have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [sq_nonneg ((N : ℝ) - 3)]
  have hlogPos : 0 < oddLogIncrement N := by
    have hlow := Real.sum_range_le_log_div hx0
      (lt_of_le_of_lt hx13 (by norm_num)) 1
    norm_num at hlow
    rw [oddLogIncrement_eq_scaled_log (by omega)]
    have hpositive : 0 < 2 * ((N : ℝ)⁻¹) := by positivity
    exact lt_of_lt_of_le hpositive <| calc
      2 * ((N : ℝ)⁻¹) ≤
          2 * (1 / 2 * Real.log ((1 + (N : ℝ)⁻¹) / (1 - (N : ℝ)⁻¹))) :=
        mul_le_mul_of_nonneg_left hlow (by norm_num)
      _ = Real.log ((1 + 1 / (N : ℝ)) / (1 - 1 / (N : ℝ))) := by
        rw [one_div]
        ring
  rw [SharpSerfling.kappa_of_not_even hnotEven]
  change 1 - 1 / (2 * (N : ℝ) ^ 2) ≤ 2 / ((N : ℝ) * oddLogIncrement N)
  rw [le_div_iff₀ (mul_pos hNr hlogPos)]
  have hmul := mul_le_mul_of_nonneg_left hlogUpper
    (mul_nonneg hNr.le hfactorPos.le)
  have hpolyPos : 0 < 2 * (N : ℝ) ^ 2 - 1 := by
    have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [sq_nonneg ((N : ℝ) - 3)]
  calc
    (1 - 1 / (2 * (N : ℝ) ^ 2)) * ((N : ℝ) * oddLogIncrement N) =
        ((N : ℝ) * (1 - 1 / (2 * (N : ℝ) ^ 2))) * oddLogIncrement N := by ring
    _ ≤ ((N : ℝ) * (1 - 1 / (2 * (N : ℝ) ^ 2))) *
        ((2 / (N : ℝ)) / (1 - 1 / (2 * (N : ℝ) ^ 2))) := hmul
    _ = 2 := by
      let A : ℝ := 1 - 1 / (2 * (N : ℝ) ^ 2)
      have hA : A ≠ 0 := by exact ne_of_gt hfactorPos
      change ((N : ℝ) * A) * ((2 / (N : ℝ)) / A) = 2
      field_simp [ne_of_gt hNr, hA]

private theorem odd_sub_two {N : ℕ} (hN : 2 ≤ N) (hOdd : Odd N) : Odd (N - 2) := by
  obtain ⟨q, hq⟩ := hOdd
  refine ⟨q - 1, ?_⟩
  omega

private theorem oddGamma_ge_basicApprox {N m : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (hm1 : 1 ≤ m) (hmN : m ≤ N - 1) :
    (1 - 1 / (2 * (N : ℝ) ^ 2)) *
          ((m : ℝ) * ((N : ℝ) - (m : ℝ)) / (4 * ((N : ℝ) - 1))) -
        ((m : ℝ) - 1) * ((N : ℝ) - (m : ℝ) - 1) /
          (4 * ((N : ℝ) - 3)) - 1 / 12 ≤
      oddGamma N m := by
  have hN2 : 2 ≤ N := by omega
  have hOddRed : Odd (N - 2) := odd_sub_two hN2 hOdd
  have hkN := kappa_odd_lower (by omega) hOdd
  have hkRed := kappa_odd_upper (N := N - 2) (by omega) hOddRed
  have hmR : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast (hmN.trans (Nat.sub_le N 1))
  have hA : 0 ≤ (m : ℝ) * ((N : ℝ) - (m : ℝ)) /
      (4 * ((N : ℝ) - 1)) := by
    have hN1 : 0 < (N : ℝ) - 1 := by
      have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
      linarith
    positivity
  have hB : 0 ≤ ((m : ℝ) - 1) * ((N : ℝ) - (m : ℝ) - 1) /
      (4 * ((N : ℝ) - 3)) := by
    have hmR1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm1
    have hmNm1 : (m : ℝ) ≤ (N : ℝ) - 1 := by
      have hcast : (m : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hmN
      rw [Nat.cast_sub (by omega)] at hcast
      norm_num at hcast ⊢
      exact hcast
    have hN3 : 0 < (N : ℝ) - 3 := by
      have : (3 : ℝ) < (N : ℝ) := by exact_mod_cast (show 3 < N by omega)
      linarith
    have hNmOne : 1 ≤ (N : ℝ) - (m : ℝ) := by linarith
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hmR1) (sub_nonneg.mpr hNmOne))
      (mul_nonneg (by norm_num) hN3.le)
  have hcurrent := mul_le_mul_of_nonneg_right hkN hA
  have hreduced := mul_le_mul_of_nonneg_right hkRed hB
  unfold oddGamma oddProxyScale
  rw [Nat.cast_sub hN2, Nat.cast_sub hm1]
  norm_num only [Nat.cast_ofNat]
  ring_nf at hcurrent hreduced ⊢
  nlinarith

theorem oddGamma_ge_alpha_sq_div_six {N m : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (hm2 : 2 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2) :
    oddAlpha N m ^ 2 / 6 ≤ oddGamma N m := by
  have hmN : m ≤ N - 1 := by omega
  have hlower := oddGamma_ge_basicApprox hN hOdd (by omega) hmN
  let u : ℝ := (m : ℝ) - 1
  have hNR : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hu1 : 1 ≤ u := by
    dsimp [u]
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    linarith
  have huN : u ≤ ((N : ℝ) - 3) / 2 := by
    have hmBound : 2 * m ≤ N - 1 := by omega
    have hmBoundR : 2 * (m : ℝ) ≤ (N : ℝ) - 1 := by
      have hcast : ((2 * m : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hmBound
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega)] at hcast
      norm_num at hcast ⊢
      exact hcast
    dsimp [u]
    linarith
  have hP := SharpSerfling.Certificates.P0_nonneg hNR hu1 huN
  have hden : 0 <
      24 * (N : ℝ) ^ 2 * ((N : ℝ) - 3) * ((N : ℝ) - 2) ^ 2 *
        ((N : ℝ) - 1) := by
    have hN1 : 0 < (N : ℝ) - 1 := by linarith
    have hN2 : 0 < (N : ℝ) - 2 := by linarith
    have hN3 : 0 < (N : ℝ) - 3 := by linarith
    positivity
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hN2 : (N : ℝ) - 2 ≠ 0 := by linarith
  have hN3 : (N : ℝ) - 3 ≠ 0 := by linarith
  have hcert : 0 ≤
      (1 - 1 / (2 * (N : ℝ) ^ 2)) *
          ((m : ℝ) * ((N : ℝ) - (m : ℝ)) / (4 * ((N : ℝ) - 1))) -
        ((m : ℝ) - 1) * ((N : ℝ) - (m : ℝ) - 1) /
          (4 * ((N : ℝ) - 3)) - 1 / 12 - oddAlpha N m ^ 2 / 6 := by
    rw [show
      (1 - 1 / (2 * (N : ℝ) ^ 2)) *
            ((m : ℝ) * ((N : ℝ) - (m : ℝ)) / (4 * ((N : ℝ) - 1))) -
          ((m : ℝ) - 1) * ((N : ℝ) - (m : ℝ) - 1) /
            (4 * ((N : ℝ) - 3)) - 1 / 12 - oddAlpha N m ^ 2 / 6 =
        SharpSerfling.Certificates.P0 (N : ℝ) u /
          (24 * (N : ℝ) ^ 2 * ((N : ℝ) - 3) * ((N : ℝ) - 2) ^ 2 *
            ((N : ℝ) - 1)) by
      unfold oddAlpha SharpSerfling.Certificates.P0 u
      field_simp [hN0, hN1, hN2, hN3]
      ring]
    exact div_nonneg hP hden.le
  linarith

theorem oddGamma_pos {N m : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (hm2 : 2 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2) : 0 < oddGamma N m := by
  have hgap := oddGamma_ge_alpha_sq_div_six hN hOdd hm2 hmHalf
  have hmBound : 2 * m ≤ N - 1 := by omega
  have hmBoundR : 2 * (m : ℝ) ≤ (N : ℝ) - 1 := by
    have hcast : ((2 * m : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hmBound
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega)] at hcast
    norm_num at hcast ⊢
    exact hcast
  have hN2 : 0 < (N : ℝ) - 2 := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
    linarith
  have hAlpha : 0 < oddAlpha N m := by
    unfold oddAlpha
    apply div_pos
    · linarith
    · exact hN2
  exact lt_of_lt_of_le (by positivity : 0 < oddAlpha N m ^ 2 / 6) hgap

theorem oddGamma_ge_alpha_sq_add_u_div_twelve {N m : ℕ}
    (hN : 7 ≤ N) (hOdd : Odd N) (hm3 : 3 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2) :
    oddAlpha N m ^ 2 / 6 + ((m : ℝ) - 1) / (12 * (N : ℝ)) ≤
      oddGamma N m := by
  have hmN : m ≤ N - 1 := by omega
  have hlower := oddGamma_ge_basicApprox (by omega) hOdd (by omega) hmN
  let u : ℝ := (m : ℝ) - 1
  have hNR : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hu2 : 2 ≤ u := by
    dsimp [u]
    have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
    linarith
  have huN : u ≤ ((N : ℝ) - 3) / 2 := by
    have hmBound : 2 * m ≤ N - 1 := by omega
    have hcast : ((2 * m : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hmBound
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega)] at hcast
    norm_num at hcast ⊢
    dsimp [u]
    linarith
  have hP := SharpSerfling.Certificates.P12_nonneg hNR hu2 huN
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hN1pos : 0 < (N : ℝ) - 1 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hN2pos : 0 < (N : ℝ) - 2 := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
    linarith
  have hN3pos : 0 < (N : ℝ) - 3 := by
    have : (3 : ℝ) < (N : ℝ) := by exact_mod_cast (show 3 < N by omega)
    linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := ne_of_gt hN1pos
  have hN2 : (N : ℝ) - 2 ≠ 0 := ne_of_gt hN2pos
  have hN3 : (N : ℝ) - 3 ≠ 0 := ne_of_gt hN3pos
  have hden : 0 <
      24 * (N : ℝ) ^ 2 * ((N : ℝ) - 3) * ((N : ℝ) - 2) ^ 2 *
        ((N : ℝ) - 1) := by positivity
  have hcert : 0 ≤
      (1 - 1 / (2 * (N : ℝ) ^ 2)) *
          ((m : ℝ) * ((N : ℝ) - (m : ℝ)) / (4 * ((N : ℝ) - 1))) -
        ((m : ℝ) - 1) * ((N : ℝ) - (m : ℝ) - 1) /
          (4 * ((N : ℝ) - 3)) - 1 / 12 - oddAlpha N m ^ 2 / 6 -
          u / (12 * (N : ℝ)) := by
    rw [show
      (1 - 1 / (2 * (N : ℝ) ^ 2)) *
            ((m : ℝ) * ((N : ℝ) - (m : ℝ)) / (4 * ((N : ℝ) - 1))) -
          ((m : ℝ) - 1) * ((N : ℝ) - (m : ℝ) - 1) /
            (4 * ((N : ℝ) - 3)) - 1 / 12 - oddAlpha N m ^ 2 / 6 -
            u / (12 * (N : ℝ)) =
        SharpSerfling.Certificates.P12 (N : ℝ) u /
          (24 * (N : ℝ) ^ 2 * ((N : ℝ) - 3) * ((N : ℝ) - 2) ^ 2 *
            ((N : ℝ) - 1)) by
      unfold oddAlpha SharpSerfling.Certificates.P12 u
      field_simp [hN0, hN1, hN2, hN3]
      ring]
    exact div_nonneg hP hden.le
  dsimp [u] at hcert
  linarith

theorem oddGamma_ge_alpha_sq_add_u_div_seven {N m : ℕ}
    (hN : 15 ≤ N) (hOdd : Odd N) (hm3 : 3 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (huN : (m : ℝ) - 1 ≤ (N : ℝ) / 7) :
    oddAlpha N m ^ 2 / 6 + ((m : ℝ) - 1) / (7 * (N : ℝ)) ≤
      oddGamma N m := by
  have hmN : m ≤ N - 1 := by omega
  have hlower := oddGamma_ge_basicApprox (by omega) hOdd (by omega) hmN
  let u : ℝ := (m : ℝ) - 1
  have hNR : (15 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hu2 : 2 ≤ u := by
    dsimp [u]
    have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
    linarith
  have hP := SharpSerfling.Certificates.P7_nonneg hNR hu2 (by simpa [u] using huN)
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hN1pos : 0 < (N : ℝ) - 1 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hN2pos : 0 < (N : ℝ) - 2 := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
    linarith
  have hN3pos : 0 < (N : ℝ) - 3 := by
    have : (3 : ℝ) < (N : ℝ) := by exact_mod_cast (show 3 < N by omega)
    linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := ne_of_gt hN1pos
  have hN2 : (N : ℝ) - 2 ≠ 0 := ne_of_gt hN2pos
  have hN3 : (N : ℝ) - 3 ≠ 0 := ne_of_gt hN3pos
  have hden : 0 <
      168 * (N : ℝ) ^ 2 * ((N : ℝ) - 3) * ((N : ℝ) - 2) ^ 2 *
        ((N : ℝ) - 1) := by positivity
  have hcert : 0 ≤
      (1 - 1 / (2 * (N : ℝ) ^ 2)) *
          ((m : ℝ) * ((N : ℝ) - (m : ℝ)) / (4 * ((N : ℝ) - 1))) -
        ((m : ℝ) - 1) * ((N : ℝ) - (m : ℝ) - 1) /
          (4 * ((N : ℝ) - 3)) - 1 / 12 - oddAlpha N m ^ 2 / 6 -
          u / (7 * (N : ℝ)) := by
    rw [show
      (1 - 1 / (2 * (N : ℝ) ^ 2)) *
            ((m : ℝ) * ((N : ℝ) - (m : ℝ)) / (4 * ((N : ℝ) - 1))) -
          ((m : ℝ) - 1) * ((N : ℝ) - (m : ℝ) - 1) /
            (4 * ((N : ℝ) - 3)) - 1 / 12 - oddAlpha N m ^ 2 / 6 -
            u / (7 * (N : ℝ)) =
        SharpSerfling.Certificates.P7 (N : ℝ) u /
          (168 * (N : ℝ) ^ 2 * ((N : ℝ) - 3) * ((N : ℝ) - 2) ^ 2 *
            ((N : ℝ) - 1)) by
      unfold oddAlpha SharpSerfling.Certificates.P7 u
      field_simp [hN0, hN1, hN2, hN3]
      ring]
    exact div_nonneg hP hden.le
  dsimp [u] at hcert
  linarith

theorem oddGamma_le_one_sixth {N m : ℕ}
    (hN : 7 ≤ N) (hOdd : Odd N) (hm3 : 3 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2) :
    oddGamma N m ≤ 1 / 6 := by
  have hN2 : 2 ≤ N := by omega
  have hm1 : 1 ≤ m := by omega
  have hmN : m ≤ N - 1 := by omega
  have hOddRed : Odd (N - 2) := odd_sub_two hN2 hOdd
  have hkN := kappa_odd_upper (by omega) hOdd
  have hkRed := kappa_odd_lower (N := N - 2) (by omega) hOddRed
  rw [Nat.cast_sub hN2] at hkRed
  norm_num only [Nat.cast_ofNat] at hkRed
  have hmR : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast (hmN.trans (Nat.sub_le N 1))
  have hA : 0 ≤ (m : ℝ) * ((N : ℝ) - (m : ℝ)) /
      (4 * ((N : ℝ) - 1)) := by
    have hN1 : 0 < (N : ℝ) - 1 := by
      have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
      linarith
    positivity
  have hmR1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmNm1 : (m : ℝ) ≤ (N : ℝ) - 1 := by
    have hcast : (m : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hmN
    rw [Nat.cast_sub (by omega)] at hcast
    norm_num at hcast ⊢
    exact hcast
  have hN3pos : 0 < (N : ℝ) - 3 := by
    have : (3 : ℝ) < (N : ℝ) := by exact_mod_cast (show 3 < N by omega)
    linarith
  have hNmOne : 1 ≤ (N : ℝ) - (m : ℝ) := by linarith
  have hB : 0 ≤ ((m : ℝ) - 1) * ((N : ℝ) - (m : ℝ) - 1) /
      (4 * ((N : ℝ) - 3)) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hmR1) (sub_nonneg.mpr hNmOne))
      (mul_nonneg (by norm_num) hN3pos.le)
  have hcurrent := mul_le_mul_of_nonneg_right hkN hA
  have hreduced := mul_le_mul_of_nonneg_right hkRed hB
  have hgammaUpper : oddGamma N m ≤
      (m : ℝ) * ((N : ℝ) - (m : ℝ)) / (4 * ((N : ℝ) - 1)) -
        (1 - 1 / (2 * ((N : ℝ) - 2) ^ 2)) *
          (((m : ℝ) - 1) * ((N : ℝ) - (m : ℝ) - 1) /
            (4 * ((N : ℝ) - 3))) - 1 / 12 := by
    unfold oddGamma oddProxyScale
    rw [Nat.cast_sub hN2, Nat.cast_sub hm1]
    norm_num only [Nat.cast_ofNat]
    ring_nf at hcurrent hreduced ⊢
    nlinarith
  let u : ℝ := (m : ℝ) - 1
  have hu0 : 0 ≤ u := by
    dsimp [u]
    linarith
  have huUpper : u ≤ ((N : ℝ) - 3) / 2 := by
    have hmBound : 2 * m ≤ N - 1 := by omega
    have hcast : ((2 * m : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hmBound
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega)] at hcast
    norm_num at hcast ⊢
    dsimp [u]
    linarith
  have hneg : - (N : ℝ) + u + 2 ≤ 0 := by linarith
  have hpoly : 0 < 4 * (N : ℝ) ^ 2 - 17 * (N : ℝ) + 17 := by
    let x : ℝ := (N : ℝ) - 7
    have hx : 0 ≤ x := by
      dsimp [x]
      have : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hrepr : (N : ℝ) = x + 7 := by dsimp [x]; ring
    rw [hrepr]
    ring_nf
    positivity
  have hN1pos : 0 < (N : ℝ) - 1 := by linarith
  have hN2pos : 0 < (N : ℝ) - 2 := by linarith
  have hden : 0 <
      8 * ((N : ℝ) - 3) * ((N : ℝ) - 2) ^ 2 * ((N : ℝ) - 1) := by
    positivity
  have hfrac :
      u * (- (N : ℝ) + u + 2) *
          (4 * (N : ℝ) ^ 2 - 17 * (N : ℝ) + 17) /
          (8 * ((N : ℝ) - 3) * ((N : ℝ) - 2) ^ 2 * ((N : ℝ) - 1)) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hu0 hneg) hpoly.le)
      hden.le
  have hN1 : (N : ℝ) - 1 ≠ 0 := ne_of_gt hN1pos
  have hN2r : (N : ℝ) - 2 ≠ 0 := ne_of_gt hN2pos
  have hN3 : (N : ℝ) - 3 ≠ 0 := ne_of_gt hN3pos
  have hid :
      (m : ℝ) * ((N : ℝ) - (m : ℝ)) / (4 * ((N : ℝ) - 1)) -
          (1 - 1 / (2 * ((N : ℝ) - 2) ^ 2)) *
            (((m : ℝ) - 1) * ((N : ℝ) - (m : ℝ) - 1) /
              (4 * ((N : ℝ) - 3))) - 1 / 12 - 1 / 6 =
        u * (- (N : ℝ) + u + 2) *
          (4 * (N : ℝ) ^ 2 - 17 * (N : ℝ) + 17) /
          (8 * ((N : ℝ) - 3) * ((N : ℝ) - 2) ^ 2 * ((N : ℝ) - 1)) := by
    dsimp [u]
    field_simp [hN1, hN2r, hN3]
    ring
  linarith

private theorem etaExpression_upper {x : ℝ} (hx0 : 0 < x) (hx13 : x ≤ 1 / 3) :
    (1 - x ^ 2) *
        ((1 / 2 * Real.log ((1 + x) / (1 - x))) / x) ≤
      1 - 2 * x ^ 2 / 3 := by
  have hx1 : x < 1 := lt_of_le_of_lt hx13 (by norm_num)
  have hlog := Real.log_div_le_sum_range_add hx0.le hx1 3
  norm_num [Finset.sum_range_succ] at hlog
  have hxSq : x ^ 2 ≤ 1 / 9 := by nlinarith
  have hden : 0 < 1 - x ^ 2 := by nlinarith [sq_nonneg x]
  have hfactor : 0 ≤ (1 - x ^ 2) / x := div_nonneg hden.le hx0.le
  have hmul := mul_le_mul_of_nonneg_left hlog hfactor
  calc
    (1 - x ^ 2) * ((1 / 2 * Real.log ((1 + x) / (1 - x))) / x) =
        ((1 - x ^ 2) / x) *
          (1 / 2 * Real.log ((1 + x) / (1 - x))) := by ring
    _ ≤ ((1 - x ^ 2) / x) *
        (x + x ^ 3 / 3 + x ^ 5 / 5 + x ^ 7 / (1 - x ^ 2)) := hmul
    _ ≤ 1 - 2 * x ^ 2 / 3 := by
      field_simp [ne_of_gt hx0, ne_of_gt hden]
      nlinarith [sq_nonneg (x ^ 2), mul_nonneg (sq_nonneg x)
        (sub_nonneg.mpr hxSq)]

private theorem etaExpression_lower {x : ℝ} (hx0 : 0 < x) (hx13 : x ≤ 1 / 3) :
    1 - (2 * x ^ 2 / 3 + 2 * x ^ 4 / (15 * (1 - x ^ 2))) ≤
      (1 - x ^ 2) *
        ((1 / 2 * Real.log ((1 + x) / (1 - x))) / x) := by
  have hx1 : x < 1 := lt_of_le_of_lt hx13 (by norm_num)
  have hlog := Real.sum_range_le_log_div hx0.le hx1 4
  norm_num [Finset.sum_range_succ] at hlog
  have hxSq : x ^ 2 ≤ 1 / 9 := by nlinarith
  have hden : 0 < 1 - x ^ 2 := by nlinarith [sq_nonneg x]
  have hfactor : 0 ≤ (1 - x ^ 2) / x := div_nonneg hden.le hx0.le
  have hmul := mul_le_mul_of_nonneg_left hlog hfactor
  calc
    1 - (2 * x ^ 2 / 3 + 2 * x ^ 4 / (15 * (1 - x ^ 2))) ≤
        ((1 - x ^ 2) / x) *
          (x + x ^ 3 / 3 + x ^ 5 / 5 + x ^ 7 / 7) := by
      field_simp [ne_of_gt hx0, ne_of_gt hden]
      have hpoly : 0 ≤ 15 * x ^ 4 - 9 * x ^ 2 + 8 := by
        nlinarith [sq_nonneg (x ^ 2)]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg x)) hpoly]
    _ ≤ ((1 - x ^ 2) / x) *
        (1 / 2 * Real.log ((1 + x) / (1 - x))) := hmul
    _ = (1 - x ^ 2) *
        ((1 / 2 * Real.log ((1 + x) / (1 - x))) / x) := by ring

theorem centralEta_eq_etaExpression {N : ℕ} (hN : 0 < N) :
    centralEta N =
      (1 - ((1 : ℝ) / N) ^ 2) *
        ((1 / 2 * Real.log
          ((1 + (1 : ℝ) / N) / (1 - (1 : ℝ) / N))) / ((1 : ℝ) / N)) := by
  rw [centralEta, oddLogIncrement_eq_scaled_log hN]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hNr]

theorem centralDeficit_bounds {N : ℕ} (hN : 3 ≤ N) :
    2 / (3 * (N : ℝ) ^ 2) ≤ centralDeficit N ∧
      centralDeficit N ≤ 3 / (4 * (N : ℝ) ^ 2) := by
  let x : ℝ := 1 / (N : ℝ)
  let z : ℝ := x ^ 2
  let U : ℝ := 2 * z / 3 + 2 * z ^ 2 / (15 * (1 - z))
  have hNr : 0 < (N : ℝ) := by positivity
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx13 : x ≤ 1 / 3 := by
    dsimp [x]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hN)
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz19 : z ≤ 1 / 9 := by
    dsimp [z]
    nlinarith
  have hz1 : z < 1 := lt_of_le_of_lt hz19 (by norm_num)
  have hEtaEq : centralEta N =
      (1 - x ^ 2) *
        ((1 / 2 * Real.log ((1 + x) / (1 - x))) / x) := by
    simpa [x] using centralEta_eq_etaExpression (N := N) (by omega)
  have hEtaUpper : centralEta N ≤ 1 - 2 * z / 3 := by
    rw [hEtaEq]
    simpa [z] using etaExpression_upper hx0 hx13
  have hEtaLower : 1 - U ≤ centralEta N := by
    rw [hEtaEq]
    convert etaExpression_lower hx0 hx13 using 1 <;> simp [z, U] <;> ring
  have hU0 : 0 ≤ U := by
    dsimp [U]
    exact add_nonneg (div_nonneg (mul_nonneg (by norm_num) hz0) (by norm_num))
      (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg z))
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hz1.le)))
  have hU_lt_one : U < 1 := by
    have hden : 0 < 1 - z := sub_pos.mpr hz1
    have hzSq : z ^ 2 ≤ 1 / 81 := by nlinarith [sq_nonneg z]
    have hterm : 2 * z ^ 2 / (15 * (1 - z)) ≤ 1 / 10 := by
      rw [div_le_iff₀ (mul_pos (by norm_num) hden)]
      nlinarith
    have hfirst : 2 * z / 3 ≤ 2 / 27 := by nlinarith
    dsimp [U]
    linarith
  have hEtaPos : 0 < centralEta N :=
    lt_of_lt_of_le (sub_pos.mpr hU_lt_one) hEtaLower
  constructor
  · unfold centralDeficit
    have hlog := Real.log_le_sub_one_of_pos hEtaPos
    have hy : 2 * z / 3 ≤ 1 - centralEta N := by linarith
    have hzEq : z = 1 / (N : ℝ) ^ 2 := by
      dsimp [z, x]
      field_simp [ne_of_gt hNr]
    calc
      2 / (3 * (N : ℝ) ^ 2) = 2 * z / 3 := by rw [hzEq]; ring
      _ ≤ 1 - centralEta N := hy
      _ ≤ -Real.log (centralEta N) := by linarith
  · unfold centralDeficit
    have hlog := Real.one_sub_inv_le_log_of_pos hEtaPos
    have hy0 : 0 ≤ 1 - centralEta N := by
      have : 0 ≤ 2 * z / 3 := by positivity
      linarith
    have hyU : 1 - centralEta N ≤ U := by linarith
    have hdenEta : 0 < centralEta N := hEtaPos
    have hdenU : 0 < 1 - U := sub_pos.mpr hU_lt_one
    have hfrac : (1 - centralEta N) / centralEta N ≤ U / (1 - U) := by
      exact div_le_div₀ hU0 hyU hdenU hEtaLower
    have hUz : U / (1 - U) ≤ 3 * z / 4 := by
      have hdenZ : 0 < 1 - z := sub_pos.mpr hz1
      have hpolyDen : 0 < 8 * z ^ 2 - 25 * z + 15 := by
        nlinarith [sq_nonneg z]
      have hz18 : z < 1 / 8 := lt_of_le_of_lt hz19 (by norm_num)
      have hleft : 3 * z - 5 ≤ 0 := by linarith
      have hright : 8 * z - 1 ≤ 0 := by linarith
      have hfirstProduct : z * (3 * z - 5) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hz0 hleft
      have hnum : 0 ≤ z * (3 * z - 5) * (8 * z - 1) :=
        mul_nonneg_of_nonpos_of_nonpos hfirstProduct hright
      have hp1 : 15 - z * 25 + z ^ 2 * 8 ≠ 0 := by
        have : 0 < 15 - z * 25 + z ^ 2 * 8 := by nlinarith
        exact ne_of_gt this
      have hp3 : 45 - z * 75 + z ^ 2 * 24 ≠ 0 := by
        have : 0 < 45 - z * 75 + z ^ 2 * 24 := by nlinarith
        exact ne_of_gt this
      have hD1 : 3 * 15 * (1 - z) - z * 2 * (15 * (1 - z) + 3 * z) ≠ 0 := by
        have : 3 * 15 * (1 - z) - z * 2 * (15 * (1 - z) + 3 * z) =
            3 * (8 * z ^ 2 - 25 * z + 15) := by ring
        rw [this]
        positivity
      have hD2 : z * (z * 8 - 25) + 15 ≠ 0 := by
        have : z * (z * 8 - 25) + 15 = 8 * z ^ 2 - 25 * z + 15 := by ring
        rw [this]
        exact ne_of_gt hpolyDen
      have hidentity :
          3 * z / 4 - U / (1 - U) =
            z * (3 * z - 5) * (8 * z - 1) /
              (4 * (8 * z ^ 2 - 25 * z + 15)) := by
        dsimp [U]
        field_simp [ne_of_gt hdenZ, ne_of_gt hdenU, ne_of_gt hpolyDen, hp1, hp3]
        field_simp [hD1, hD2]
        ring
      rw [← sub_nonneg, hidentity]
      exact div_nonneg hnum (mul_nonneg (by norm_num) hpolyDen.le)
    have hnegLog : -Real.log (centralEta N) ≤
        (1 - centralEta N) / centralEta N := by
      calc
        -Real.log (centralEta N) ≤ -(1 - (centralEta N)⁻¹) := neg_le_neg hlog
        _ = (1 - centralEta N) / centralEta N := by
          field_simp [ne_of_gt hEtaPos]
          ring
    have hzEq : z = 1 / (N : ℝ) ^ 2 := by
      dsimp [z, x]
      field_simp [ne_of_gt hNr]
    calc
      -Real.log (centralEta N) ≤ 3 * z / 4 := hnegLog.trans (hfrac.trans hUz)
      _ = 3 / (4 * (N : ℝ) ^ 2) := by rw [hzEq]; ring

theorem centralDeficit_pos {N : ℕ} (hN : 3 ≤ N) :
    0 < centralDeficit N := by
  have hlower := (centralDeficit_bounds hN).1
  exact lt_of_lt_of_le (by positivity : 0 < 2 / (3 * (N : ℝ) ^ 2)) hlower

theorem centralEta_pos {N : ℕ} (hN : 3 ≤ N) : 0 < centralEta N := by
  have hNr : 0 < (N : ℝ) := by positivity
  have hNm1 : 0 < (N : ℝ) - 1 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hratio : 1 < ((N : ℝ) + 1) / ((N : ℝ) - 1) := by
    rw [one_lt_div hNm1]
    linarith
  unfold centralEta oddLogIncrement
  have hsquare : 0 < (N : ℝ) ^ 2 - 1 := by
    have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [sq_nonneg ((N : ℝ) - 3)]
  exact div_pos (mul_pos hsquare (Real.log_pos hratio)) (mul_pos (by norm_num) hNr)

theorem centralEta_le_one {N : ℕ} (hN : 3 ≤ N) : centralEta N ≤ 1 := by
  have hbounds := (centralDeficit_bounds hN).1
  have hpositive : 0 < 2 / (3 * (N : ℝ) ^ 2) := by positivity
  have hlog : Real.log (centralEta N) ≤ 0 := by
    unfold centralDeficit at hbounds
    linarith
  exact (Real.log_nonpos_iff (centralEta_pos hN).le).mp hlog

/-- The prefactor on either nearest-balanced odd slice is exactly `eta_N`. -/
theorem centralFactor_eq_eta {N : ℕ} (hN : 3 ≤ N) (hOdd : Odd N) :
    (1 / SharpSerfling.kappa N) * (1 - (1 / (N : ℝ)) ^ 2) = centralEta N := by
  have hnotEven : ¬Even N := Nat.not_even_iff_odd.mpr hOdd
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hNm1 : 0 < (N : ℝ) - 1 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hratio : 1 < ((N : ℝ) + 1) / ((N : ℝ) - 1) := by
    rw [one_lt_div hNm1]
    linarith
  have hlog : Real.log (((N : ℝ) + 1) / ((N : ℝ) - 1)) ≠ 0 :=
    ne_of_gt (Real.log_pos hratio)
  rw [SharpSerfling.kappa_of_not_even hnotEven]
  unfold centralEta oddLogIncrement
  field_simp [hNr, hlog]

private theorem odd_upper_nearest_twice {N : ℕ} (hOdd : Odd N) :
    2 * ((N + 1) / 2) = N + 1 := by
  obtain ⟨q, hq⟩ := hOdd
  omega

private theorem odd_lower_nearest_twice {N : ℕ} (hN : 1 ≤ N) (hOdd : Odd N) :
    2 * ((N - 1) / 2) = N - 1 := by
  obtain ⟨q, hq⟩ := hOdd
  omega

theorem imbalance_upperNearest {N : ℕ} (hN : 3 ≤ N) (hOdd : Odd N) :
    imbalance N ((N + 1) / 2) = 1 / (N : ℝ) := by
  have htwice := odd_upper_nearest_twice hOdd
  have hcast : 2 * (((N + 1) / 2 : ℕ) : ℝ) = (N : ℝ) + 1 := by
    exact_mod_cast htwice
  unfold imbalance
  rw [show (N : ℝ) - 2 * (((N + 1) / 2 : ℕ) : ℝ) = -1 by linarith]
  norm_num

theorem imbalance_lowerNearest {N : ℕ} (hN : 3 ≤ N) (hOdd : Odd N) :
    imbalance N ((N - 1) / 2) = 1 / (N : ℝ) := by
  have htwice := odd_lower_nearest_twice (by omega) hOdd
  have hcast : 2 * (((N - 1) / 2 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    have hcast0 : (2 * ((N - 1) / 2 : ℕ) : ℝ) = ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast htwice
    rw [Nat.cast_sub (by omega)] at hcast0
    norm_num at hcast0 ⊢
    exact hcast0
  unfold imbalance
  rw [show (N : ℝ) - 2 * (((N - 1) / 2 : ℕ) : ℝ) = 1 by linarith]
  norm_num

/-- On the odd lattice, every success count except the two nearest-balanced
counts is at normalized distance at least `3/N` from balance. -/
theorem imbalance_far_of_ne_nearest {N K : ℕ}
    (hN : 3 ≤ N) (hOdd : Odd N) (hK : K ≤ N)
    (hLower : K ≠ (N - 1) / 2) (hUpper : K ≠ (N + 1) / 2) :
    3 / (N : ℝ) ≤ imbalance N K := by
  have hlowTwice := odd_lower_nearest_twice (by omega) hOdd
  have huppTwice := odd_upper_nearest_twice hOdd
  have hNr : 0 < (N : ℝ) := by positivity
  rcases le_total (2 * K) N with hleft | hright
  · have hgapNat : 3 ≤ N - 2 * K := by
      have hKLow : K ≤ (N - 1) / 2 := by omega
      have hKStrict : K < (N - 1) / 2 := lt_of_le_of_ne hKLow hLower
      omega
    have hgap : (3 : ℝ) ≤ (N : ℝ) - 2 * (K : ℝ) := by
      have hcast : (3 : ℝ) ≤ ((N - 2 * K : ℕ) : ℝ) := by exact_mod_cast hgapNat
      rw [Nat.cast_sub hleft] at hcast
      norm_num at hcast ⊢
      exact hcast
    have hnonneg : 0 ≤ (N : ℝ) - 2 * (K : ℝ) := by linarith
    unfold imbalance
    rw [abs_of_nonneg hnonneg]
    rw [div_le_div_iff₀ hNr hNr]
    nlinarith
  · have hgapNat : 3 ≤ 2 * K - N := by
      have hKUpp : (N + 1) / 2 ≤ K := by omega
      have hKStrict : (N + 1) / 2 < K := lt_of_le_of_ne hKUpp (Ne.symm hUpper)
      omega
    have hgap : (3 : ℝ) ≤ 2 * (K : ℝ) - (N : ℝ) := by
      have hcast : (3 : ℝ) ≤ ((2 * K - N : ℕ) : ℝ) := by exact_mod_cast hgapNat
      rw [Nat.cast_sub hright] at hcast
      norm_num at hcast ⊢
      exact hcast
    have hnonpos : (N : ℝ) - 2 * (K : ℝ) ≤ 0 := by linarith
    unfold imbalance
    rw [abs_of_nonpos hnonpos]
    rw [div_le_div_iff₀ hNr hNr]
    nlinarith

theorem recursionTilt_upperNearest {N m : ℕ} (hN : 3 ≤ N) (hOdd : Odd N) :
    recursionTilt N ((N + 1) / 2) m =
      -oddAlpha N m / (2 * (N : ℝ)) := by
  have htwice := odd_upper_nearest_twice hOdd
  have hcast : 2 * (((N + 1) / 2 : ℕ) : ℝ) = (N : ℝ) + 1 := by
    exact_mod_cast htwice
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hN2 : (N : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
    linarith
  unfold recursionTilt oddAlpha
  rw [show (N : ℝ) - 2 * (((N + 1) / 2 : ℕ) : ℝ) = -1 by linarith]
  field_simp [hNr, hN2]

theorem recursionTilt_lowerNearest {N m : ℕ} (hN : 3 ≤ N) (hOdd : Odd N) :
    recursionTilt N ((N - 1) / 2) m =
      oddAlpha N m / (2 * (N : ℝ)) := by
  have htwice := odd_lower_nearest_twice (by omega) hOdd
  have hcast : 2 * (((N - 1) / 2 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    have hcast0 : (2 * ((N - 1) / 2 : ℕ) : ℝ) = ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast htwice
    rw [Nat.cast_sub (by omega)] at hcast0
    norm_num at hcast0 ⊢
    exact hcast0
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hN2 : (N : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
    linarith
  unfold recursionTilt oddAlpha
  rw [show (N : ℝ) - 2 * (((N - 1) / 2 : ℕ) : ℝ) = 1 by linarith]
  field_simp [hNr, hN2]

theorem centralEta_eq_exp_neg_deficit {N : ℕ} (hN : 3 ≤ N) :
    centralEta N = Real.exp (-centralDeficit N) := by
  unfold centralDeficit
  rw [neg_neg, Real.exp_log (centralEta_pos hN)]

theorem variance_lowerNearest_eq_eta {N m : ℕ}
    (hN : 3 ≤ N) (hOdd : Odd N) (hm0 : 0 < m) (hmN : m < N) :
    variance N ((N - 1) / 2) m = oddProxyScale N m * centralEta N := by
  rw [variance_eq_oddProxyScale_mul (by omega) hm0 hmN,
    imbalance_lowerNearest hN hOdd, centralFactor_eq_eta hN hOdd]

theorem oddUpperNearestEnvelope {N m : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (hm2 : 2 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2) {t : ℝ} (ht : 0 ≤ t) :
    (1 / SharpSerfling.kappa N) *
        (1 - imbalance N ((N + 1) / 2) ^ 2) *
          Real.exp (-(oddGamma N m) * t ^ 2 / 2) ≤ 1 := by
  have hgamma : 0 < oddGamma N m := oddGamma_pos hN hOdd hm2 hmHalf
  have hexp : Real.exp (-(oddGamma N m) * t ^ 2 / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg t]
  rw [imbalance_upperNearest (by omega) hOdd, centralFactor_eq_eta (by omega) hOdd]
  exact (mul_le_mul_of_nonneg_left hexp (centralEta_pos (by omega)).le).trans
    (by simpa using centralEta_le_one (N := N) (by omega))

/-- Pointwise exponential envelope for every odd-population slice at least three
lattice steps away from balance. -/
theorem oddNoncentralEnvelope {N : ℕ} (hN : 5 ≤ N) (hOdd : Odd N)
    {delta alpha gamma t : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hdeltaFar : 3 / (N : ℝ) ≤ delta) (halpha : 0 < alpha)
    (ht : 0 ≤ t) (hgamma : alpha ^ 2 / 6 ≤ gamma) :
    (1 / SharpSerfling.kappa N) * (1 - delta ^ 2) *
        Real.exp (alpha * delta * t / 2 - gamma * t ^ 2 / 2) ≤ 1 := by
  have hkPos := SharpSerfling.kappa_pos (N := N) (by omega)
  have hkLower := kappa_odd_lower (N := N) (by omega) hOdd
  have hdeltaSq : 0 ≤ 1 - delta ^ 2 := by nlinarith
  have hquad :
      alpha * delta * t / 2 - gamma * t ^ 2 / 2 ≤ 3 * delta ^ 2 / 4 := by
    have hgammaMul := mul_le_mul_of_nonneg_right hgamma (sq_nonneg t)
    have hsquare := sq_nonneg (alpha * t - 3 * delta)
    nlinarith
  have hkernel :
      (1 - delta ^ 2) *
          Real.exp (alpha * delta * t / 2 - gamma * t ^ 2 / 2) ≤
        Real.exp (-delta ^ 2 / 4) := by
    calc
      _ ≤ Real.exp (-delta ^ 2) * Real.exp (3 * delta ^ 2 / 4) := by
        exact mul_le_mul (one_sub_sq_le_exp_neg_sq delta)
          (Real.exp_le_exp.mpr hquad) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (-delta ^ 2 / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hNr : 0 < (N : ℝ) := by positivity
  have hdeltaLowerSq : 9 / (N : ℝ) ^ 2 ≤ delta ^ 2 := by
    have := (sq_le_sq₀ (by positivity : 0 ≤ 3 / (N : ℝ)) hdelta0).2 hdeltaFar
    norm_num [div_pow] at this ⊢
    exact this
  let a : ℝ := 1 / (2 * (N : ℝ) ^ 2)
  let q : ℝ := delta ^ 2 / 4
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a < 1 := by
    dsimp [a]
    rw [div_lt_one (by positivity : 0 < 2 * (N : ℝ) ^ 2)]
    have hNR : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [sq_nonneg ((N : ℝ) - 5)]
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqLower : 9 / (4 * (N : ℝ) ^ 2) ≤ q := by
    dsimp [q]
    calc
      9 / (4 * (N : ℝ) ^ 2) = (9 / (N : ℝ) ^ 2) / 4 := by
        field_simp [ne_of_gt hNr]
      _ ≤ delta ^ 2 / 4 := div_le_div_of_nonneg_right hdeltaLowerSq (by norm_num)
  have hproduct : 1 ≤ (1 - a) * Real.exp q := by
    have hexp := Real.add_one_le_exp q
    have hqUpper : q ≤ 1 / 4 := by
      dsimp [q]
      nlinarith [sq_nonneg (1 - delta), sq_nonneg (1 + delta)]
    have hqa : 9 * a / 2 ≤ q := by
      dsimp [a]
      calc
        9 * (1 / (2 * (N : ℝ) ^ 2)) / 2 = 9 / (4 * (N : ℝ) ^ 2) := by
          field_simp [ne_of_gt hNr] <;> norm_num
        _ ≤ q := hqLower
    have hmul := mul_le_mul_of_nonneg_left hexp (sub_nonneg.mpr ha1.le)
    calc
      1 ≤ (1 - a) * (1 + q) := by
        have haq : a * q ≤ a / 4 := by
          exact (mul_le_mul_of_nonneg_left hqUpper ha0).trans_eq (by ring)
        nlinarith
      _ ≤ (1 - a) * Real.exp q := by simpa [add_comm] using hmul
  have hexpNeg : Real.exp (-q) ≤ 1 - a := by
    rw [Real.exp_neg]
    have hdiv : 1 / Real.exp q ≤ 1 - a := by
      rw [div_le_iff₀ (Real.exp_pos q)]
      simpa [mul_comm] using hproduct
    simpa only [one_div] using hdiv
  have hexpKappa : Real.exp (-delta ^ 2 / 4) ≤ SharpSerfling.kappa N := by
    calc
      Real.exp (-delta ^ 2 / 4) = Real.exp (-q) := by
        congr 1
        dsimp [q]
        ring
      _ ≤ 1 - a := hexpNeg
      _ ≤ SharpSerfling.kappa N := hkLower
  calc
    (1 / SharpSerfling.kappa N) * (1 - delta ^ 2) *
        Real.exp (alpha * delta * t / 2 - gamma * t ^ 2 / 2) =
      ((1 - delta ^ 2) *
        Real.exp (alpha * delta * t / 2 - gamma * t ^ 2 / 2)) /
          SharpSerfling.kappa N := by ring
    _ ≤ Real.exp (-delta ^ 2 / 4) / SharpSerfling.kappa N :=
      div_le_div_of_nonneg_right hkernel hkPos.le
    _ ≤ 1 := (div_le_one hkPos).2 hexpKappa

/-- Analytic form of the noncentral derivative comparison.  This separates
the elementary exponential envelope from the hypergeometric identities. -/
theorem oddDerivativeEnvelope {N : ℕ} {S Sred delta v r alpha gamma t : ℝ}
    (hS : 0 < S) (ht : 0 < t) (hv0 : 0 ≤ v)
    (hv : v = S * ((1 / SharpSerfling.kappa N) * (1 - delta ^ 2)))
    (hr : r ≤ alpha * delta / 2)
    (hgamma : gamma = S - Sred - 1 / 12)
    (henv : (1 / SharpSerfling.kappa N) * (1 - delta ^ 2) *
        Real.exp (alpha * delta * t / 2 - gamma * t ^ 2 / 2) ≤ 1) :
    2 * v * Real.exp (r * t) * Real.sinh (t / 2) *
        Real.exp (Sred * t ^ 2 / 2) ≤
      S * t * Real.exp (S * t ^ 2 / 2) := by
  have hsinh : 2 * Real.sinh (t / 2) ≤ t * Real.exp (t ^ 2 / 24) := by
    have h := mul_le_mul_of_nonneg_right
      (two_sinh_div_le_exp_sq_div_twentyFour ht) ht.le
    field_simp [ne_of_gt ht] at h
    simpa [mul_assoc] using h
  have hexpR : Real.exp (r * t) ≤ Real.exp (alpha * delta * t / 2) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hr ht.le
    nlinarith
  have hexpEq :
      Real.exp (alpha * delta * t / 2) * Real.exp (t ^ 2 / 24) *
          Real.exp (Sred * t ^ 2 / 2) =
        Real.exp (S * t ^ 2 / 2) *
          Real.exp (alpha * delta * t / 2 - gamma * t ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hgamma]
    ring
  calc
    2 * v * Real.exp (r * t) * Real.sinh (t / 2) *
          Real.exp (Sred * t ^ 2 / 2) =
        v * Real.exp (r * t) * (2 * Real.sinh (t / 2)) *
          Real.exp (Sred * t ^ 2 / 2) := by ring
    _ ≤ v * Real.exp (alpha * delta * t / 2) *
          (t * Real.exp (t ^ 2 / 24)) * Real.exp (Sred * t ^ 2 / 2) := by
      gcongr <;> positivity
    _ = S * t * Real.exp (S * t ^ 2 / 2) *
          ((1 / SharpSerfling.kappa N) * (1 - delta ^ 2) *
            Real.exp (alpha * delta * t / 2 - gamma * t ^ 2 / 2)) := by
      rw [hv]
      calc
        S * ((1 / SharpSerfling.kappa N) * (1 - delta ^ 2)) *
              Real.exp (alpha * delta * t / 2) *
              (t * Real.exp (t ^ 2 / 24)) * Real.exp (Sred * t ^ 2 / 2) =
            S * ((1 / SharpSerfling.kappa N) * (1 - delta ^ 2)) * t *
              (Real.exp (alpha * delta * t / 2) * Real.exp (t ^ 2 / 24) *
                Real.exp (Sred * t ^ 2 / 2)) := by ring
        _ = S * ((1 / SharpSerfling.kappa N) * (1 - delta ^ 2)) * t *
              (Real.exp (S * t ^ 2 / 2) *
                Real.exp (alpha * delta * t / 2 - gamma * t ^ 2 / 2)) := by
              rw [hexpEq]
        _ = S * t * Real.exp (S * t ^ 2 / 2) *
              ((1 / SharpSerfling.kappa N) * (1 - delta ^ 2) *
                Real.exp (alpha * delta * t / 2 - gamma * t ^ 2 / 2)) := by ring
    _ ≤ S * t * Real.exp (S * t ^ 2 / 2) * 1 := by
      exact mul_le_mul_of_nonneg_left henv (by positivity)
    _ = S * t * Real.exp (S * t ^ 2 / 2) := by ring

/-- The sharp odd-population induction step for every slice whose success
count is at least three lattice units away from balance. -/
theorem deriv_mgf_le_oddProxy_of_reduced_noncentral {N K m : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (hK0 : 0 < K) (hKN : K < N)
    (hm2 : 2 ≤ m) (hmHalf : m ≤ (N - 1) / 2)
    (hfar : 3 / (N : ℝ) ≤ imbalance N K) {t : ℝ} (ht : 0 < t)
    (hred : mgf (N - 2) (K - 1) (m - 1) t ≤
      Real.exp (oddProxyScale (N - 2) (m - 1) * t ^ 2 / 2)) :
    deriv (mgf N K m) t ≤
      oddProxyScale N m * t * Real.exp (oddProxyScale N m * t ^ 2 / 2) := by
  have hm0 : 0 < m := by omega
  have hmN : m < N := by omega
  have hKle : K ≤ N := Nat.le_of_lt hKN
  have hmTwice : 2 * m ≤ N := by omega
  have hS : 0 < oddProxyScale N m := oddProxyScale_pos (by omega) hm0 hmN
  have hx0 : 0 ≤ imbalance N K := imbalance_nonneg N K
  have hx1 : imbalance N K ≤ 1 := imbalance_le_one (by omega) hKle
  have hfactor : 0 ≤
      (1 / SharpSerfling.kappa N) * (1 - imbalance N K ^ 2) := by
    have hsquare : 0 ≤ 1 - imbalance N K ^ 2 := by
      nlinarith [sq_nonneg (1 - imbalance N K), sq_nonneg (1 + imbalance N K)]
    exact mul_nonneg (div_nonneg (by norm_num) (SharpSerfling.kappa_pos (by omega)).le)
      hsquare
  have hv := variance_eq_oddProxyScale_mul (N := N) (K := K) (m := m)
    (by omega) hm0 hmN
  have hv0 : 0 ≤ variance N K m := by rw [hv]; exact mul_nonneg hS.le hfactor
  have halpha : 0 < oddAlpha N m := by
    unfold oddAlpha
    have hmBound : 2 * m ≤ N - 1 := by omega
    have hmBoundR : 2 * (m : ℝ) ≤ (N : ℝ) - 1 := by
      have hcast : ((2 * m : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
        exact_mod_cast hmBound
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega)] at hcast
      norm_num at hcast ⊢
      exact hcast
    have hden : 0 < (N : ℝ) - 2 := by
      have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
      linarith
    exact div_pos (by linarith) hden
  have hr0 := recursionTilt_le_sampleTilt_mul_imbalance
    (N := N) (K := K) (m := m) (by omega) hmTwice
  have hr : recursionTilt N K m ≤ oddAlpha N m * imbalance N K / 2 := by
    rw [sampleTilt_eq_oddAlpha_div_two] at hr0
    nlinarith
  have hgamma := oddGamma_ge_alpha_sq_div_six hN hOdd hm2 hmHalf
  have henv := oddNoncentralEnvelope hN hOdd hx0 hx1 hfar halpha ht.le hgamma
  rw [deriv_mgf_recursion (by omega) hK0 hKN hm0 hmN]
  calc
    2 * variance N K m * Real.exp (recursionTilt N K m * t) *
          Real.sinh (t / 2) * mgf (N - 2) (K - 1) (m - 1) t ≤
        2 * variance N K m * Real.exp (recursionTilt N K m * t) *
          Real.sinh (t / 2) *
            Real.exp (oddProxyScale (N - 2) (m - 1) * t ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_left hred (by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by positivity) hv0) (Real.exp_pos _).le)
          (by positivity))
    _ ≤ _ := by
      exact oddDerivativeEnvelope hS ht hv0 hv hr rfl henv

/-- Sharp derivative domination on the nearest-balanced slice with negative
recursion tilt.  The opposite nearest-balanced slice is the unique hard one. -/
theorem deriv_mgf_le_oddProxy_of_reduced_upperNearest {N m : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (hm2 : 2 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2) {t : ℝ} (ht : 0 < t)
    (hred : mgf (N - 2) (((N + 1) / 2) - 1) (m - 1) t ≤
      Real.exp (oddProxyScale (N - 2) (m - 1) * t ^ 2 / 2)) :
    deriv (mgf N ((N + 1) / 2) m) t ≤
      oddProxyScale N m * t * Real.exp (oddProxyScale N m * t ^ 2 / 2) := by
  let K : ℕ := (N + 1) / 2
  have htwice := odd_upper_nearest_twice hOdd
  have hK0 : 0 < K := by dsimp [K]; omega
  have hKN : K < N := by dsimp [K]; omega
  have hm0 : 0 < m := by omega
  have hmN : m < N := by omega
  have hS : 0 < oddProxyScale N m := oddProxyScale_pos (by omega) hm0 hmN
  have hx0 : 0 ≤ imbalance N K := imbalance_nonneg N K
  have hx1 : imbalance N K ≤ 1 :=
    imbalance_le_one (by omega) (Nat.le_of_lt hKN)
  have hfactor : 0 ≤
      (1 / SharpSerfling.kappa N) * (1 - imbalance N K ^ 2) := by
    have hsquare : 0 ≤ 1 - imbalance N K ^ 2 := by
      nlinarith [sq_nonneg (1 - imbalance N K), sq_nonneg (1 + imbalance N K)]
    exact mul_nonneg (div_nonneg (by norm_num) (SharpSerfling.kappa_pos (by omega)).le)
      hsquare
  have hv := variance_eq_oddProxyScale_mul (N := N) (K := K) (m := m)
    (by omega) hm0 hmN
  have hv0 : 0 ≤ variance N K m := by rw [hv]; exact mul_nonneg hS.le hfactor
  have hmBound : 2 * m ≤ N - 1 := by omega
  have hmBoundR : 2 * (m : ℝ) ≤ (N : ℝ) - 1 := by
    have hcast : ((2 * m : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast hmBound
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega)] at hcast
    norm_num at hcast ⊢
    exact hcast
  have halpha : 0 < oddAlpha N m := by
    unfold oddAlpha
    have hden : 0 < (N : ℝ) - 2 := by
      have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
      linarith
    exact div_pos (by linarith) hden
  have hr : recursionTilt N K m ≤ (0 : ℝ) * imbalance N K / 2 := by
    dsimp [K]
    rw [recursionTilt_upperNearest (by omega) hOdd]
    simp only [zero_mul, zero_div]
    have hNr : 0 < (N : ℝ) := by positivity
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr halpha.le)
      (mul_nonneg (by norm_num) hNr.le)
  have henv0 := oddUpperNearestEnvelope hN hOdd hm2 hmHalf ht.le
  have henv :
      (1 / SharpSerfling.kappa N) * (1 - imbalance N K ^ 2) *
        Real.exp ((0 : ℝ) * imbalance N K * t / 2 - oddGamma N m * t ^ 2 / 2) ≤
          1 := by
    dsimp [K]
    convert henv0 using 1 <;> ring
  rw [show mgf N ((N + 1) / 2) m = mgf N K m by rfl]
  rw [deriv_mgf_recursion (by omega) hK0 hKN hm0 hmN]
  calc
    2 * variance N K m * Real.exp (recursionTilt N K m * t) *
          Real.sinh (t / 2) * mgf (N - 2) (K - 1) (m - 1) t ≤
        2 * variance N K m * Real.exp (recursionTilt N K m * t) *
          Real.sinh (t / 2) *
            Real.exp (oddProxyScale (N - 2) (m - 1) * t ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_left hred (by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by positivity) hv0) (Real.exp_pos _).le)
          (by positivity))
    _ ≤ _ := by
      exact oddDerivativeEnvelope hS ht hv0 hv hr rfl henv

/-- On the positive-tilt nearest-balanced slice, the recursion and the
elementary `sinh` estimate reduce the derivative to the hard-central
exponential envelope.  This is the precise input integrated by
`hardCentralQ`. -/
theorem deriv_mgf_le_hardCentral_of_reduced {N m : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (hm2 : 2 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2) {t : ℝ} (ht : 0 < t)
    (hred : mgf (N - 2) (((N - 1) / 2) - 1) (m - 1) t ≤
      Real.exp (oddProxyScale (N - 2) (m - 1) * t ^ 2 / 2)) :
    deriv (mgf N ((N - 1) / 2) m) t ≤
      variance N ((N - 1) / 2) m * t *
        Real.exp (recursionTilt N ((N - 1) / 2) m * t +
          (oddProxyScale (N - 2) (m - 1) + 1 / 12) * t ^ 2 / 2) := by
  let K : ℕ := (N - 1) / 2
  have hK0 : 0 < K := by dsimp [K]; omega
  have hKN : K < N := by dsimp [K]; omega
  have hm0 : 0 < m := by omega
  have hmN : m < N := by omega
  have hv0 : 0 ≤ variance N K m := by
    rw [show variance N K m = oddProxyScale N m * centralEta N by
      dsimp [K]
      exact variance_lowerNearest_eq_eta (by omega) hOdd hm0 hmN]
    exact mul_nonneg
      (oddProxyScale_pos (by omega) hm0 hmN).le (centralEta_pos (by omega)).le
  have hsinh : 2 * Real.sinh (t / 2) ≤ t * Real.exp (t ^ 2 / 24) := by
    have h := mul_le_mul_of_nonneg_right
      (two_sinh_div_le_exp_sq_div_twentyFour ht) ht.le
    field_simp [ne_of_gt ht] at h
    simpa [mul_assoc] using h
  rw [show mgf N ((N - 1) / 2) m = mgf N K m by rfl]
  rw [deriv_mgf_recursion (by omega) hK0 hKN hm0 hmN]
  calc
    2 * variance N K m * Real.exp (recursionTilt N K m * t) *
          Real.sinh (t / 2) * mgf (N - 2) (K - 1) (m - 1) t ≤
        2 * variance N K m * Real.exp (recursionTilt N K m * t) *
          Real.sinh (t / 2) *
            Real.exp (oddProxyScale (N - 2) (m - 1) * t ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_left hred (by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by positivity) hv0) (Real.exp_pos _).le)
          (by positivity))
    _ ≤ variance N K m * Real.exp (recursionTilt N K m * t) *
          (t * Real.exp (t ^ 2 / 24)) *
            Real.exp (oddProxyScale (N - 2) (m - 1) * t ^ 2 / 2) := by
      have hmul :
          variance N K m * Real.exp (recursionTilt N K m * t) *
              (2 * Real.sinh (t / 2)) ≤
            variance N K m * Real.exp (recursionTilt N K m * t) *
              (t * Real.exp (t ^ 2 / 24)) :=
        mul_le_mul_of_nonneg_left hsinh
          (mul_nonneg hv0 (Real.exp_pos (recursionTilt N K m * t)).le)
      have htail : 0 ≤
          Real.exp (oddProxyScale (N - 2) (m - 1) * t ^ 2 / 2) :=
        (Real.exp_pos _).le
      calc
        2 * variance N K m * Real.exp (recursionTilt N K m * t) *
              Real.sinh (t / 2) *
                Real.exp (oddProxyScale (N - 2) (m - 1) * t ^ 2 / 2) =
            (variance N K m * Real.exp (recursionTilt N K m * t) *
              (2 * Real.sinh (t / 2))) *
                Real.exp (oddProxyScale (N - 2) (m - 1) * t ^ 2 / 2) := by ring
        _ ≤ (variance N K m * Real.exp (recursionTilt N K m * t) *
              (t * Real.exp (t ^ 2 / 24))) *
                Real.exp (oddProxyScale (N - 2) (m - 1) * t ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right hmul htail
        _ = _ := by ring
    _ = variance N K m * t *
        Real.exp (recursionTilt N K m * t +
          (oddProxyScale (N - 2) (m - 1) + 1 / 12) * t ^ 2 / 2) := by
      calc
        variance N K m * Real.exp (recursionTilt N K m * t) *
              (t * Real.exp (t ^ 2 / 24)) *
                Real.exp (oddProxyScale (N - 2) (m - 1) * t ^ 2 / 2) =
            variance N K m * t *
              (Real.exp (recursionTilt N K m * t) *
                Real.exp (t ^ 2 / 24) *
                Real.exp (oddProxyScale (N - 2) (m - 1) * t ^ 2 / 2)) := by ring
        _ = variance N K m * t *
              Real.exp (recursionTilt N K m * t + t ^ 2 / 24 +
                oddProxyScale (N - 2) (m - 1) * t ^ 2 / 2) := by
          rw [← Real.exp_add, ← Real.exp_add]
        _ = _ := by
          congr 2
          ring

/-- Integration bridge for the hard central slice: a pointwise derivative
envelope plus nonnegativity of the accumulated difference `hardCentralQ`
implies the desired quadratic MGF bound. -/
theorem mgf_le_exp_of_deriv_le_hardCentralQ {N K m : ℕ}
    {S v r B t : ℝ} (hK0 : 0 < K) (hKN : K < N)
    (hm0 : 0 < m) (hmN : m ≤ N) (ht : 0 ≤ t)
    (hderiv : ∀ u : ℝ, 0 < u → u ≤ t →
      deriv (mgf N K m) u ≤ v * u * Real.exp (r * u + B * u ^ 2 / 2))
    (hQ : 0 ≤ _root_.SharpSerfling.Analysis.hardCentralQ S v r B t) :
    mgf N K m t ≤ Real.exp (S * t ^ 2 / 2) := by
  let E : ℝ → ℝ := fun u ↦ v * u * Real.exp (r * u + B * u ^ 2 / 2)
  have hderivContinuous : Continuous (deriv (mgf N K m)) := by
    rw [show deriv (mgf N K m) = fun u ↦
        SharpSerfling.finiteAverage fun s : Sample N m ↦
          ((count K s : ℝ) - center N K m) *
            Real.exp (u * ((count K s : ℝ) - center N K m)) by
      funext u
      exact deriv_mgf N K m u]
    unfold SharpSerfling.finiteAverage
    fun_prop
  have hEContinuous : Continuous E := by
    dsimp [E]
    fun_prop
  have hFTC : (∫ u in (0 : ℝ)..t, deriv (mgf N K m) u) =
      mgf N K m t - mgf N K m 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun u _ ↦ (hasDerivAt_mgf N K m u).differentiableAt)
      (hderivContinuous.intervalIntegrable 0 t)
  have hmono : (∫ u in (0 : ℝ)..t, deriv (mgf N K m) u) ≤
      ∫ u in (0 : ℝ)..t, E u := by
    apply intervalIntegral.integral_mono_on ht
      (hderivContinuous.intervalIntegrable 0 t)
      (hEContinuous.intervalIntegrable 0 t)
    intro u hu
    rcases hu.1.eq_or_lt with rfl | hu0
    · have hzero : deriv (mgf N K m) 0 = 0 := by
        rw [deriv_mgf]
        simpa using finiteAverage_centered_count_eq_zero
          (N := N) (K := K) (m := m) hK0 hKN hm0
      rw [hzero]
      dsimp [E]
      norm_num
    · exact hderiv u hu0 hu.2
  rw [mgf_zero_of_le N K m hmN] at hFTC
  unfold _root_.SharpSerfling.Analysis.hardCentralQ at hQ
  dsimp [E] at hmono
  linarith

/-- Exact specialization of the single-crossing endpoint theorem to the
positive-tilt nearest-balanced odd hypergeometric slice.  The remaining
hypotheses are precisely the manuscript's central-parameter inequalities
and its final polynomial certificate. -/
theorem hardCentralQ_lowerNearest_nonneg {N m : ℕ} {beta : ℝ}
    (hN : 5 ≤ N) (hOdd : Odd N) (hm2 : 2 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (hroot : (oddAlpha N m / (2 * (N : ℝ))) * beta =
      centralDeficit N + oddGamma N m * beta ^ 2 / 2)
    (ha : 0 < centralDeficit N)
    (hac : centralDeficit N < oddGamma N m * beta ^ 2 / 2)
    (hcd : oddGamma N m * beta ^ 2 / 2 <
      oddProxyScale N m * beta ^ 2 / 2)
    (hc2 : oddGamma N m * beta ^ 2 / 2 ≤ 2 * centralDeficit N)
    (hcertificate : centralDeficit N ^ 3 +
        (oddGamma N m * beta ^ 2 / 2) *
          (oddProxyScale N m * beta ^ 2 / 2) ^ 2 *
            Real.exp (oddProxyScale N m * beta ^ 2 / 2) ≤
      (2 * centralDeficit N - oddGamma N m * beta ^ 2 / 2) *
        (oddProxyScale N m * beta ^ 2 / 2 -
          oddGamma N m * beta ^ 2 / 2)) :
    0 ≤ _root_.SharpSerfling.Analysis.hardCentralQ
      (oddProxyScale N m) (variance N ((N - 1) / 2) m)
      (recursionTilt N ((N - 1) / 2) m)
      (oddProxyScale (N - 2) (m - 1) + 1 / 12) beta := by
  have hm0 : 0 < m := by omega
  have hmN : m < N := by omega
  have hv : variance N ((N - 1) / 2) m =
      oddProxyScale N m * Real.exp (-centralDeficit N) := by
    rw [variance_lowerNearest_eq_eta (by omega) hOdd hm0 hmN,
      centralEta_eq_exp_neg_deficit (by omega)]
  have hgamma : oddGamma N m =
      oddProxyScale N m -
        (oddProxyScale (N - 2) (m - 1) + 1 / 12) := by
    unfold oddGamma
    ring
  have hr : recursionTilt N ((N - 1) / 2) m =
      oddAlpha N m / (2 * (N : ℝ)) :=
    recursionTilt_lowerNearest (by omega) hOdd
  apply _root_.SharpSerfling.Analysis.hardCentralQ_endpoint_nonneg
    (oddProxyScale_pos (by omega) hm0 hmN) hv hgamma
  · rwa [hr]
  · exact ha
  · exact hac
  · exact hcd
  · exact hc2
  · exact hcertificate

/-- The full accumulated comparison on the hard central slice, conditional
only on the crossing inequality and the manuscript's parameter certificate
at the larger root. -/
theorem hardCentralQ_lowerNearest_all_nonneg_of_crossing_certificate
    {N m : ℕ}
    (hN : 7 ≤ N) (hOdd : Odd N) (hm3 : 3 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (hcross : 2 * oddGamma N m * centralDeficit N <
      (oddAlpha N m / (2 * (N : ℝ))) ^ 2)
    (hac : centralDeficit N <
      oddGamma N m * centralUpperRoot N m ^ 2 / 2)
    (hcd : oddGamma N m * centralUpperRoot N m ^ 2 / 2 <
      oddProxyScale N m * centralUpperRoot N m ^ 2 / 2)
    (hc2 : oddGamma N m * centralUpperRoot N m ^ 2 / 2 ≤
      2 * centralDeficit N)
    (hcertificate : centralDeficit N ^ 3 +
        (oddGamma N m * centralUpperRoot N m ^ 2 / 2) *
          (oddProxyScale N m * centralUpperRoot N m ^ 2 / 2) ^ 2 *
            Real.exp (oddProxyScale N m * centralUpperRoot N m ^ 2 / 2) ≤
      (2 * centralDeficit N -
          oddGamma N m * centralUpperRoot N m ^ 2 / 2) *
        (oddProxyScale N m * centralUpperRoot N m ^ 2 / 2 -
          oddGamma N m * centralUpperRoot N m ^ 2 / 2))
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ _root_.SharpSerfling.Analysis.hardCentralQ
      (oddProxyScale N m) (variance N ((N - 1) / 2) m)
      (recursionTilt N ((N - 1) / 2) m)
      (oddProxyScale (N - 2) (m - 1) + 1 / 12) t := by
  have hm0 : 0 < m := by omega
  have hmN : m < N := by omega
  have ha : 0 < centralDeficit N := centralDeficit_pos (by omega)
  have halpha : 0 < oddAlpha N m := oddAlpha_pos (by omega) hmHalf
  have hgammaPos : 0 < oddGamma N m := oddGamma_pos (by omega) hOdd (by omega) hmHalf
  have hrEq : recursionTilt N ((N - 1) / 2) m =
      oddAlpha N m / (2 * (N : ℝ)) :=
    recursionTilt_lowerNearest (by omega) hOdd
  have hrPos : 0 < recursionTilt N ((N - 1) / 2) m := by
    rw [hrEq]
    positivity
  have hv : variance N ((N - 1) / 2) m =
      oddProxyScale N m * Real.exp (-centralDeficit N) := by
    rw [variance_lowerNearest_eq_eta (by omega) hOdd hm0 hmN,
      centralEta_eq_exp_neg_deficit (by omega)]
  have hgammaEq : oddGamma N m =
      oddProxyScale N m -
        (oddProxyScale (N - 2) (m - 1) + 1 / 12) := by
    unfold oddGamma
    ring
  have hroot : (oddAlpha N m / (2 * (N : ℝ))) * centralUpperRoot N m =
      centralDeficit N + oddGamma N m * centralUpperRoot N m ^ 2 / 2 := by
    have hdisc : 0 ≤ _root_.SharpSerfling.Analysis.hardCentralDiscriminant
        (centralDeficit N) (oddAlpha N m / (2 * (N : ℝ))) (oddGamma N m) := by
      unfold _root_.SharpSerfling.Analysis.hardCentralDiscriminant
      linarith
    unfold centralUpperRoot
    exact _root_.SharpSerfling.Analysis.hardCentral_upperRoot_equation
      (ne_of_gt hgammaPos) hdisc
  have hQroot : 0 ≤ _root_.SharpSerfling.Analysis.hardCentralQ
      (oddProxyScale N m) (variance N ((N - 1) / 2) m)
      (recursionTilt N ((N - 1) / 2) m)
      (oddProxyScale (N - 2) (m - 1) + 1 / 12) (centralUpperRoot N m) :=
    hardCentralQ_lowerNearest_nonneg (by omega) hOdd (by omega) hmHalf
      hroot ha hac hcd hc2 hcertificate
  apply _root_.SharpSerfling.Analysis.hardCentralQ_nonneg_of_upperRoot
    (oddProxyScale_pos (by omega) hm0 hmN) hv hgammaEq ha hrPos hgammaPos
  · rwa [hrEq]
  · simpa [centralUpperRoot, hrEq] using hQroot
  · exact ht

/-- Complete central `Q` comparison, split according to whether the derivative
ratio crosses one.  Only the crossing branch calls the numerical certificate. -/
theorem hardCentralQ_lowerNearest_all_nonneg
    {N m : ℕ}
    (hN : 7 ≤ N) (hOdd : Odd N) (hm3 : 3 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (hparameters :
      2 * oddGamma N m * centralDeficit N <
          (oddAlpha N m / (2 * (N : ℝ))) ^ 2 →
        CentralParameterCertificate N m)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ _root_.SharpSerfling.Analysis.hardCentralQ
      (oddProxyScale N m) (variance N ((N - 1) / 2) m)
      (recursionTilt N ((N - 1) / 2) m)
      (oddProxyScale (N - 2) (m - 1) + 1 / 12) t := by
  by_cases hcross : 2 * oddGamma N m * centralDeficit N <
      (oddAlpha N m / (2 * (N : ℝ))) ^ 2
  · obtain ⟨hac, hcd, hc2, hcertificate⟩ := hparameters hcross
    exact hardCentralQ_lowerNearest_all_nonneg_of_crossing_certificate
      hN hOdd hm3 hmHalf hcross hac hcd hc2 hcertificate ht
  · have hm0 : 0 < m := by omega
    have hmN : m < N := by omega
    have hS : 0 < oddProxyScale N m := oddProxyScale_pos (by omega) hm0 hmN
    have hgammaPos : 0 < oddGamma N m :=
      oddGamma_pos (by omega) hOdd (by omega) hmHalf
    have hrEq : recursionTilt N ((N - 1) / 2) m =
        oddAlpha N m / (2 * (N : ℝ)) :=
      recursionTilt_lowerNearest (by omega) hOdd
    have hv : variance N ((N - 1) / 2) m =
        oddProxyScale N m * Real.exp (-centralDeficit N) := by
      rw [variance_lowerNearest_eq_eta (by omega) hOdd hm0 hmN,
        centralEta_eq_exp_neg_deficit (by omega)]
    have hgammaEq : oddGamma N m =
        oddProxyScale N m -
          (oddProxyScale (N - 2) (m - 1) + 1 / 12) := by
      unfold oddGamma
      ring
    apply _root_.SharpSerfling.Analysis.hardCentralQ_nonneg_of_no_crossing
      hS hv hgammaEq hgammaPos
    · rw [hrEq]
      exact le_of_not_gt hcross
    · exact ht

/-- The hard nearest-balanced slice follows once the reduced sharp MGF bound
and the corresponding accumulated single-crossing inequality are known. -/
theorem mgf_le_oddProxy_lowerNearest_of_reduced_and_Q {N m : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (hm2 : 2 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (hred : ∀ u : ℝ, 0 ≤ u →
      mgf (N - 2) (((N - 1) / 2) - 1) (m - 1) u ≤
        Real.exp (oddProxyScale (N - 2) (m - 1) * u ^ 2 / 2))
    {t : ℝ} (ht : 0 ≤ t)
    (hQ : 0 ≤ _root_.SharpSerfling.Analysis.hardCentralQ
      (oddProxyScale N m) (variance N ((N - 1) / 2) m)
      (recursionTilt N ((N - 1) / 2) m)
      (oddProxyScale (N - 2) (m - 1) + 1 / 12) t) :
    mgf N ((N - 1) / 2) m t ≤
      Real.exp (oddProxyScale N m * t ^ 2 / 2) := by
  have hK0 : 0 < (N - 1) / 2 := by omega
  have hKN : (N - 1) / 2 < N := by omega
  have hm0 : 0 < m := by omega
  have hmN : m ≤ N := by omega
  apply mgf_le_exp_of_deriv_le_hardCentralQ hK0 hKN hm0 hmN ht
  · intro u hu _
    exact deriv_mgf_le_hardCentral_of_reduced hN hOdd hm2 hmHalf hu (hred u hu.le)
  · exact hQ

/-- Central induction step in its final reusable form: the reduced sharp MGF
bound and the central-parameter implication close the hard slice for all
nonnegative tilts. -/
theorem mgf_le_oddProxy_lowerNearest_of_reduced_and_centralParameters
    {N m : ℕ}
    (hN : 7 ≤ N) (hOdd : Odd N) (hm3 : 3 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (hparameters :
      2 * oddGamma N m * centralDeficit N <
          (oddAlpha N m / (2 * (N : ℝ))) ^ 2 →
        CentralParameterCertificate N m)
    (hred : ∀ u : ℝ, 0 ≤ u →
      mgf (N - 2) (((N - 1) / 2) - 1) (m - 1) u ≤
        Real.exp (oddProxyScale (N - 2) (m - 1) * u ^ 2 / 2))
    {t : ℝ} (ht : 0 ≤ t) :
    mgf N ((N - 1) / 2) m t ≤
      Real.exp (oddProxyScale N m * t ^ 2 / 2) := by
  apply mgf_le_oddProxy_lowerNearest_of_reduced_and_Q
    (by omega) hOdd (by omega) hmHalf hred ht
  exact hardCentralQ_lowerNearest_all_nonneg hN hOdd hm3 hmHalf hparameters ht

theorem mgf_le_oddProxy_noncentral_of_reduced {N K m : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (hK0 : 0 < K) (hKN : K < N)
    (hm2 : 2 ≤ m) (hmHalf : m ≤ (N - 1) / 2)
    (hfar : 3 / (N : ℝ) ≤ imbalance N K)
    (hred : ∀ u : ℝ, 0 ≤ u →
      mgf (N - 2) (K - 1) (m - 1) u ≤
        Real.exp (oddProxyScale (N - 2) (m - 1) * u ^ 2 / 2))
    {t : ℝ} (ht : 0 ≤ t) :
    mgf N K m t ≤ Real.exp (oddProxyScale N m * t ^ 2 / 2) := by
  have hmN : m ≤ N := by omega
  have hbound : mgf N K m t ≤
      Real.exp ((oddProxyScale N m / 2) * t ^ 2) := by
    apply le_exp_quadratic_of_deriv_le (b := oddProxyScale N m / 2) ht
      (fun u ↦ (hasDerivAt_mgf N K m u).differentiableAt)
      (mgf_zero_of_le N K m hmN)
    intro u hu hut
    have hderiv := deriv_mgf_le_oddProxy_of_reduced_noncentral hN hOdd hK0 hKN
      hm2 hmHalf hfar hu (hred u hu.le)
    convert hderiv using 1 <;> ring
  convert hbound using 1 <;> ring

theorem mgf_le_oddProxy_upperNearest_of_reduced {N m : ℕ}
    (hN : 5 ≤ N) (hOdd : Odd N) (hm2 : 2 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (hred : ∀ u : ℝ, 0 ≤ u →
      mgf (N - 2) (((N + 1) / 2) - 1) (m - 1) u ≤
        Real.exp (oddProxyScale (N - 2) (m - 1) * u ^ 2 / 2))
    {t : ℝ} (ht : 0 ≤ t) :
    mgf N ((N + 1) / 2) m t ≤
      Real.exp (oddProxyScale N m * t ^ 2 / 2) := by
  have hmN : m ≤ N := by omega
  have hbound : mgf N ((N + 1) / 2) m t ≤
      Real.exp ((oddProxyScale N m / 2) * t ^ 2) := by
    apply le_exp_quadratic_of_deriv_le (b := oddProxyScale N m / 2) ht
      (fun u ↦ (hasDerivAt_mgf N ((N + 1) / 2) m u).differentiableAt)
      (mgf_zero_of_le N ((N + 1) / 2) m hmN)
    intro u hu hut
    have hderiv := deriv_mgf_le_oddProxy_of_reduced_upperNearest hN hOdd hm2 hmHalf
      hu (hred u hu.le)
    convert hderiv using 1 <;> ring
  convert hbound using 1 <;> ring

end SharpSerfling.Hypergeometric
