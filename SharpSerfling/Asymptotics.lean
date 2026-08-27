import SharpSerfling.Hypergeometric.SmallTilt
import Mathlib.Analysis.Asymptotics.Lemmas

namespace SharpSerfling

open Filter Topology Asymptotics

/-- The optimal multiplier in the exchangeable normalization of the
manuscript. -/
noncomputable def exchangeableConstant (N : ℕ) : ℝ :=
  kappa N * (N : ℝ) / ((N : ℝ) - 1)

theorem exchangeableConstant_of_even {N : ℕ} (hN : 2 ≤ N) (heven : Even N) :
    exchangeableConstant N = (N : ℝ) / ((N : ℝ) - 1) := by
  rw [exchangeableConstant, kappa_of_even heven, one_mul]

theorem exchangeableConstant_even_expansion_exact {N : ℕ}
    (hN : 2 ≤ N) (heven : Even N) :
    exchangeableConstant N =
      1 + 1 / (N : ℝ) + 1 / (N : ℝ) ^ 2 +
        1 / ((N : ℝ) ^ 2 * ((N : ℝ) - 1)) := by
  rw [exchangeableConstant_of_even hN heven]
  have hNR : (N : ℝ) ≠ 0 := by positivity
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  field_simp [hNR, hNm1]
  ring

/-- Quantitative real-variable form of the odd-parity expansion.  It is a
direct consequence of the explicit remainder bound for the odd logarithmic
series. -/
theorem odd_exchangeable_expansion_bound {x : ℝ} (hx0 : 0 < x)
    (hx13 : x ≤ 1 / 3) :
    |x / ((1 - x) * (1 / 2 * Real.log ((1 + x) / (1 - x)))) -
        (1 + x + (2 / 3) * x ^ 2)| ≤ 10 * x ^ 3 := by
  have hxnonneg : 0 ≤ x := hx0.le
  have hx1 : x < 1 := hx13.trans_lt (by norm_num)
  let A : ℝ := 1 / 2 * Real.log ((1 + x) / (1 - x))
  let A₀ : ℝ := x + x ^ 3 / 3
  let r : ℝ := A - A₀
  let P : ℝ := 1 + x + (2 / 3) * x ^ 2
  have hlow := Real.sum_range_le_log_div hxnonneg hx1 2
  have hup := Real.log_div_le_sum_range_add hxnonneg hx1 2
  norm_num [Finset.sum_range_succ] at hlow hup
  have hlow' : A₀ ≤ A := by simpa [A, A₀] using hlow
  have hup' : A ≤ A₀ + x ^ 5 / (1 - x ^ 2) := by
    simpa [A, A₀] using hup
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hx2 : x ^ 2 ≤ 1 / 9 := by nlinarith [sq_nonneg x]
  have hden : 0 < 1 - x ^ 2 := by nlinarith
  have htail : x ^ 5 / (1 - x ^ 2) ≤ 2 * x ^ 5 := by
    rw [div_le_iff₀ hden]
    have hx5 : 0 ≤ x ^ 5 := by positivity
    nlinarith
  have hrUpper : r ≤ 2 * x ^ 5 := by
    dsimp [r]
    linarith
  have hA_ge_x : x ≤ A := by
    have hx3 : 0 ≤ x ^ 3 := by positivity
    dsimp [A₀] at hlow'
    linarith
  have hOneSub : 2 / 3 ≤ 1 - x := by linarith
  have hDlow : (2 / 3) * x ≤ (1 - x) * A := by
    calc
      (2 / 3) * x ≤ (1 - x) * x :=
        mul_le_mul_of_nonneg_right hOneSub hxnonneg
      _ ≤ (1 - x) * A :=
        mul_le_mul_of_nonneg_left hA_ge_x (by linarith)
  have hDpos : 0 < (1 - x) * A := lt_of_lt_of_le (by positivity) hDlow
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hP : P ≤ 3 / 2 := by
    dsimp [P]
    nlinarith
  let base : ℝ := x ^ 4 * (2 / 3 + x / 9 + 2 * x ^ 2 / 9)
  have hcoef0 : 0 ≤ 2 / 3 + x / 9 + 2 * x ^ 2 / 9 := by positivity
  have hcoef1 : 2 / 3 + x / 9 + 2 * x ^ 2 / 9 ≤ 1 := by nlinarith
  have hbase0 : 0 ≤ base := by dsimp [base]; positivity
  have hbase : base ≤ x ^ 4 := by
    dsimp [base]
    simpa using mul_le_mul_of_nonneg_left hcoef1 (show 0 ≤ x ^ 4 by positivity)
  have hPr : P * (1 - x) * r ≤ 3 * x ^ 5 := by
    calc
      P * (1 - x) * r ≤ (3 / 2) * (1 - x) * r := by
        gcongr
      _ ≤ (3 / 2) * 1 * r := by
        gcongr
        linarith
      _ ≤ (3 / 2) * 1 * (2 * x ^ 5) := by
        gcongr
      _ = 3 * x ^ 5 := by ring
  have hPr0 : 0 ≤ P * (1 - x) * r := mul_nonneg
    (mul_nonneg hP0 (by linarith)) hr0
  have h3x5 : 3 * x ^ 5 ≤ x ^ 4 := by
    calc
      3 * x ^ 5 = (3 * x) * x ^ 4 := by ring
      _ ≤ 1 * x ^ 4 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = x ^ 4 := one_mul _
  have hid : x - P * ((1 - x) * A) = base - P * (1 - x) * r := by
    dsimp [A₀, r, P, base]
    ring
  have hnum : |x - P * ((1 - x) * A)| ≤ 2 * x ^ 4 := by
    rw [hid]
    calc
      |base - P * (1 - x) * r| ≤ |base| + |P * (1 - x) * r| :=
        abs_sub _ _
      _ = base + P * (1 - x) * r := by rw [abs_of_nonneg hbase0, abs_of_nonneg hPr0]
      _ ≤ x ^ 4 + x ^ 4 := add_le_add hbase (hPr.trans h3x5)
      _ = 2 * x ^ 4 := by ring
  change |x / ((1 - x) * A) - P| ≤ 10 * x ^ 3
  have hApos : 0 < A := hx0.trans_le hA_ge_x
  rw [show x / ((1 - x) * A) - P =
      (x - P * ((1 - x) * A)) / ((1 - x) * A) by
        field_simp [ne_of_gt hDpos, ne_of_gt hApos, sub_ne_zero.mpr hx1.ne],
    abs_div, abs_of_pos hDpos]
  rw [div_le_iff₀ hDpos]
  calc
    |x - P * ((1 - x) * A)| ≤ 2 * x ^ 4 := hnum
    _ ≤ 10 * x ^ 3 * ((2 / 3) * x) := by
      have hx3 : 0 ≤ x ^ 3 := by positivity
      nlinarith
    _ ≤ 10 * x ^ 3 * ((1 - x) * A) :=
      mul_le_mul_of_nonneg_left hDlow (by positivity)

theorem exchangeableConstant_of_odd_scaled {N : ℕ} (hN : 2 ≤ N)
    (hOdd : Odd N) :
    exchangeableConstant N =
      ((1 : ℝ) / N) /
        ((1 - (1 : ℝ) / N) *
          (1 / 2 * Real.log
            ((1 + (1 : ℝ) / N) / (1 - (1 : ℝ) / N)))) := by
  have hnotEven : ¬Even N := Nat.not_even_iff_odd.mpr hOdd
  have hNR : (N : ℝ) ≠ 0 := by positivity
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hLpos := Hypergeometric.oddLogIncrement_pos hN
  have hscaled := Hypergeometric.oddLogIncrement_eq_scaled_log (N := N) (by omega)
  rw [exchangeableConstant, kappa_of_not_even hnotEven]
  change (2 / ((N : ℝ) * Hypergeometric.oddLogIncrement N)) * (N : ℝ) /
      ((N : ℝ) - 1) = _
  rw [hscaled]
  have hlog : Real.log
      ((1 + (1 : ℝ) / N) / (1 - (1 : ℝ) / N)) ≠ 0 := by
    rw [← hscaled]
    exact ne_of_gt hLpos
  field_simp [hNR, hNm1, hlog]

theorem exchangeableConstant_odd_expansion_bound {N : ℕ}
    (hN : 3 ≤ N) (hOdd : Odd N) :
    |exchangeableConstant N -
        (1 + 1 / (N : ℝ) + (2 / 3) / (N : ℝ) ^ 2)| ≤
      10 / (N : ℝ) ^ 3 := by
  have hNR : 0 < (N : ℝ) := by positivity
  have hx13 : (1 : ℝ) / N ≤ 1 / 3 := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hN)
  have hbound := odd_exchangeable_expansion_bound (x := (1 : ℝ) / N)
    (by positivity) hx13
  rw [exchangeableConstant_of_odd_scaled (by omega) hOdd]
  convert hbound using 1 <;> field_simp [ne_of_gt hNR] <;> ring

/-- The even branch of `C_N★` has remainder `O(N⁻³)`. -/
theorem exchangeableConstant_even_expansion :
    (fun q : ℕ ↦ exchangeableConstant (2 * (q + 1)) -
      (1 + 1 / (2 * (q + 1) : ℕ) +
        1 / ((2 * (q + 1) : ℕ) : ℝ) ^ 2)) =O[atTop]
      (fun q : ℕ ↦ 1 / ((2 * (q + 1) : ℕ) : ℝ) ^ 3) := by
  apply IsBigO.of_bound 2
  filter_upwards [] with q
  let N := 2 * (q + 1)
  have hN : 2 ≤ N := by omega
  have hEven : Even N := ⟨q + 1, by omega⟩
  rw [show exchangeableConstant N -
      (1 + 1 / (N : ℝ) + 1 / (N : ℝ) ^ 2) =
        1 / ((N : ℝ) ^ 2 * ((N : ℝ) - 1)) by
          rw [exchangeableConstant_even_expansion_exact hN hEven]
          ring]
  simp only [Real.norm_eq_abs, abs_div, abs_one, norm_div, norm_one]
  have hNR : 0 < (N : ℝ) := by positivity
  have hNm1 : 0 < (N : ℝ) - 1 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  rw [abs_of_pos (mul_pos (sq_pos_of_pos hNR) hNm1), abs_of_pos (pow_pos hNR 3)]
  have hcross : (N : ℝ) ^ 3 ≤
      2 * ((N : ℝ) ^ 2 * ((N : ℝ) - 1)) := by
    calc
      (N : ℝ) ^ 3 = (N : ℝ) ^ 2 * (N : ℝ) := by ring
      _ ≤ (N : ℝ) ^ 2 * (2 * ((N : ℝ) - 1)) := by
        gcongr
        have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      _ = 2 * ((N : ℝ) ^ 2 * ((N : ℝ) - 1)) := by ring
  rw [show 2 * (1 / (N : ℝ) ^ 3) = 2 / (N : ℝ) ^ 3 by ring]
  exact (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hNR) hNm1)
    (pow_pos hNR 3)).mpr (by simpa using hcross)

/-- The odd branch of `C_N★` has the manuscript coefficient `2/3` and
remainder `O(N⁻³)`. -/
theorem exchangeableConstant_odd_expansion :
    (fun q : ℕ ↦ exchangeableConstant (2 * (q + 1) + 1) -
      (1 + 1 / ((2 * (q + 1) + 1 : ℕ) : ℝ) +
        (2 / 3) / ((2 * (q + 1) + 1 : ℕ) : ℝ) ^ 2)) =O[atTop]
      (fun q : ℕ ↦ 1 / ((2 * (q + 1) + 1 : ℕ) : ℝ) ^ 3) := by
  apply IsBigO.of_bound 10
  filter_upwards [] with q
  let N := 2 * (q + 1) + 1
  have hN : 3 ≤ N := by omega
  have hOdd : Odd N := ⟨q + 1, by omega⟩
  have h := exchangeableConstant_odd_expansion_bound hN hOdd
  change |exchangeableConstant N -
      (1 + 1 / (N : ℝ) + (2 / 3) / (N : ℝ) ^ 2)| ≤
    10 * |1 / (N : ℝ) ^ 3|
  rw [abs_of_pos (by positivity : 0 < 1 / (N : ℝ) ^ 3)]
  simpa [div_eq_mul_inv] using h

theorem exchangeableConstant_firstOrder_error_bound {N : ℕ} (hN : 3 ≤ N) :
    |(N : ℝ) * (exchangeableConstant N - 1) - 1| ≤ 11 / (N : ℝ) := by
  have hNR : 0 < (N : ℝ) := by positivity
  by_cases hEven : Even N
  · rw [exchangeableConstant_even_expansion_exact (by omega) hEven]
    have hN3R : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hNm1pos : 0 < (N : ℝ) - 1 := by linarith
    have hNm1 : (N : ℝ) - 1 ≠ 0 := by
      exact ne_of_gt hNm1pos
    have hid :
        (N : ℝ) *
            ((1 + 1 / (N : ℝ) + 1 / (N : ℝ) ^ 2 +
              1 / ((N : ℝ) ^ 2 * ((N : ℝ) - 1))) - 1) - 1 =
          1 / ((N : ℝ) - 1) := by
      field_simp [ne_of_gt hNR, hNm1]
      ring
    rw [hid, abs_of_pos (one_div_pos.mpr hNm1pos)]
    rw [div_le_div_iff₀ hNm1pos hNR]
    nlinarith
  · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
    have hrem := exchangeableConstant_odd_expansion_bound hN hOdd
    let P : ℝ := 1 + 1 / (N : ℝ) + (2 / 3) / (N : ℝ) ^ 2
    have hid : (N : ℝ) * (exchangeableConstant N - 1) - 1 =
        (N : ℝ) * (exchangeableConstant N - P) + 2 / (3 * (N : ℝ)) := by
      dsimp [P]
      field_simp [ne_of_gt hNR]
      ring
    rw [hid]
    calc
      |(N : ℝ) * (exchangeableConstant N - P) + 2 / (3 * (N : ℝ))| ≤
          |(N : ℝ) * (exchangeableConstant N - P)| +
            |2 / (3 * (N : ℝ))| := abs_add_le _ _
      _ = (N : ℝ) * |exchangeableConstant N - P| +
            2 / (3 * (N : ℝ)) := by
          rw [abs_mul, abs_of_pos hNR, abs_of_pos (by positivity : 0 < 2 / (3 * (N : ℝ)))]
      _ ≤ (N : ℝ) * (10 / (N : ℝ) ^ 3) +
            2 / (3 * (N : ℝ)) := by
          gcongr
      _ ≤ 11 / (N : ℝ) := by
          have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
          field_simp [ne_of_gt hNR]
          nlinarith [sq_nonneg ((N : ℝ) - 1)]

/-- The exact first-order coefficient stated after the parity expansions:
`N (C_N★ - 1) → 1`. -/
theorem tendsto_nat_mul_exchangeableConstant_sub_one :
    Tendsto (fun N : ℕ ↦ (N : ℝ) * (exchangeableConstant N - 1))
      atTop (nhds 1) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hmajorant : Tendsto (fun N : ℕ ↦ (11 : ℝ) / N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm' ?_ hmajorant
  filter_upwards [eventually_atTop.2 ⟨3, fun N hN ↦ hN⟩] with N hN
  simpa [Real.norm_eq_abs] using exchangeableConstant_firstOrder_error_bound hN

end SharpSerfling
