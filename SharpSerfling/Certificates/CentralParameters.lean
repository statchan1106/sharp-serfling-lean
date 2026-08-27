import SharpSerfling.Hypergeometric.Odd
import Mathlib.Analysis.Complex.Exponential

namespace SharpSerfling.Hypergeometric

/-- The crossing condition forces the hard central slice into the small-sample
regime used by the manuscript's numerical certificate. -/
theorem centralCrossing_size_bounds {N m : ℕ}
    (hN : 7 ≤ N) (hOdd : Odd N) (hm3 : 3 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (hcross : 2 * oddGamma N m * centralDeficit N <
      (oddAlpha N m / (2 * (N : ℝ))) ^ 2) :
    (m : ℝ) - 1 < (N : ℝ) / 10 ∧
      21 ≤ N ∧ 3 / 4 < oddAlpha N m := by
  let u : ℝ := (m : ℝ) - 1
  have hNr : 0 < (N : ℝ) := by positivity
  have hNr0 : (N : ℝ) ≠ 0 := ne_of_gt hNr
  have hu2 : 2 ≤ u := by
    dsimp [u]
    have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
    linarith
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have huHalf : u ≤ (N : ℝ) / 2 := by
    have hmBound : 2 * m ≤ N - 1 := by omega
    have hcast : (2 * m : ℝ) ≤ (N - 1 : ℕ) := by exact_mod_cast hmBound
    rw [Nat.cast_sub (by omega)] at hcast
    norm_num at hcast ⊢
    dsimp [u]
    linarith
  have haLower := (centralDeficit_bounds (N := N) (by omega)).1
  have hgamma12 := oddGamma_ge_alpha_sq_add_u_div_twelve
    hN hOdd hm3 hmHalf
  have hprod :
      2 * (oddAlpha N m ^ 2 / 6 + u / (12 * (N : ℝ))) *
          (2 / (3 * (N : ℝ) ^ 2)) ≤
        2 * oddGamma N m * centralDeficit N := by
    have hgap0 : 0 ≤ oddAlpha N m ^ 2 / 6 + u / (12 * (N : ℝ)) := by
      positivity
    have ha0 : 0 ≤ 2 / (3 * (N : ℝ) ^ 2) := by positivity
    have hgamma0 : 0 ≤ oddGamma N m :=
      (oddGamma_pos (by omega) hOdd (by omega) hmHalf).le
    nlinarith [mul_le_mul hgamma12 haLower ha0 hgamma0]
  have halphaFour : 4 * u / (N : ℝ) < oddAlpha N m ^ 2 := by
    have hstrict := lt_of_le_of_lt hprod hcross
    field_simp [hNr0] at hstrict ⊢
    nlinarith
  have halpha0 : 0 < oddAlpha N m := oddAlpha_pos (by omega) hmHalf
  have halphaUpper : oddAlpha N m < 1 - 2 * (u / (N : ℝ)) := by
    unfold oddAlpha
    dsimp [u]
    have hN2 : 0 < (N : ℝ) - 2 := by
      have hNR : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    rw [div_lt_iff₀ hN2]
    field_simp [hNr0]
    nlinarith
  have huSeventh : u < (N : ℝ) / 7 := by
    by_contra hnot
    have hlow : (N : ℝ) / 7 ≤ u := le_of_not_gt hnot
    let x : ℝ := u / (N : ℝ)
    have hx0 : 0 ≤ x := by dsimp [x]; positivity
    have hxLow : 1 / 7 ≤ x := by
      dsimp [x]
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 7) hNr]
      nlinarith
    have hxHalf : x ≤ 1 / 2 := by
      dsimp [x]
      rw [div_le_iff₀ hNr]
      linarith
    have hxprod : 0 ≤ x * (1 / 2 - x) := mul_nonneg hx0 (sub_nonneg.mpr hxHalf)
    have hquad : (1 - 2 * x) ^ 2 ≤ 4 * x := by nlinarith
    have halphaUpper' : oddAlpha N m < 1 - 2 * x := by simpa [x] using halphaUpper
    have hright0 : 0 ≤ 1 - 2 * x := by linarith
    have halphaSq : oddAlpha N m ^ 2 < (1 - 2 * x) ^ 2 := by nlinarith
    have halphaFour' : 4 * x < oddAlpha N m ^ 2 := by
      convert halphaFour using 1 <;> simp [x] <;> ring
    linarith
  have hN15 : 15 ≤ N := by
    have hN14 : (14 : ℝ) < (N : ℝ) := by nlinarith
    exact_mod_cast hN14
  have hgamma7 := oddGamma_ge_alpha_sq_add_u_div_seven
    hN15 hOdd hm3 hmHalf (by simpa [u] using huSeventh.le)
  have hprodStrong :
      2 * (oddAlpha N m ^ 2 / 6 + u / (7 * (N : ℝ))) *
          (2 / (3 * (N : ℝ) ^ 2)) ≤
        2 * oddGamma N m * centralDeficit N := by
    have hgap0 : 0 ≤ oddAlpha N m ^ 2 / 6 + u / (7 * (N : ℝ)) := by
      positivity
    have ha0 : 0 ≤ 2 / (3 * (N : ℝ) ^ 2) := by positivity
    have hgamma0 : 0 ≤ oddGamma N m :=
      (oddGamma_pos (by omega) hOdd (by omega) hmHalf).le
    nlinarith [mul_le_mul hgamma7 haLower ha0 hgamma0]
  have halphaStrong : 48 * u / (7 * (N : ℝ)) < oddAlpha N m ^ 2 := by
    have hstrict := lt_of_le_of_lt hprodStrong hcross
    field_simp [hNr0] at hstrict ⊢
    nlinarith
  have huTenth : u < (N : ℝ) / 10 := by
    by_contra hnot
    have hlow : (N : ℝ) / 10 ≤ u := le_of_not_gt hnot
    let x : ℝ := u / (N : ℝ)
    have hx0 : 0 ≤ x := by dsimp [x]; positivity
    have hxLow : 1 / 10 ≤ x := by
      dsimp [x]
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 10) hNr]
      nlinarith
    have hxHalf : x ≤ 1 / 2 := by
      dsimp [x]
      rw [div_le_iff₀ hNr]
      linarith
    have hxprod : 0 ≤ x * (1 / 2 - x) := mul_nonneg hx0 (sub_nonneg.mpr hxHalf)
    have hquad : (1 - 2 * x) ^ 2 ≤ 48 * x / 7 := by nlinarith
    have halphaUpper' : oddAlpha N m < 1 - 2 * x := by simpa [x] using halphaUpper
    have hright0 : 0 ≤ 1 - 2 * x := by linarith
    have halphaSq : oddAlpha N m ^ 2 < (1 - 2 * x) ^ 2 := by nlinarith
    have halphaStrong' : 48 * x / 7 < oddAlpha N m ^ 2 := by
      convert halphaStrong using 1 <;> simp [x] <;> ring
    linarith
  have hN21 : 21 ≤ N := by
    have hN20 : (20 : ℝ) < (N : ℝ) := by
      nlinarith only [hu2, huTenth]
    exact_mod_cast hN20
  have halphaThreeQuarters : 3 / 4 < oddAlpha N m := by
    unfold oddAlpha
    have hN2 : 0 < (N : ℝ) - 2 := by
      have hNR : (21 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN21
      linarith only [hNR]
    rw [lt_div_iff₀ hN2]
    have hmR : (m : ℝ) = u + 1 := by dsimp [u]; ring
    rw [hmR]
    nlinarith only [huTenth, hu2]
  have huTenth' : (m : ℝ) - 1 < (N : ℝ) / 10 := by
    change (m : ℝ) - 1 < (N : ℝ) / 10 at huTenth
    exact huTenth
  exact ⟨huTenth', hN21, halphaThreeQuarters⟩

/-- The larger crossing root produces parameters `0 < a < c < d` and
`c < 2a`. -/
theorem centralCrossing_order_bounds {N m : ℕ}
    (hN : 7 ≤ N) (hOdd : Odd N) (hm3 : 3 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (hcross : 2 * oddGamma N m * centralDeficit N <
      (oddAlpha N m / (2 * (N : ℝ))) ^ 2) :
    centralDeficit N < oddGamma N m * centralUpperRoot N m ^ 2 / 2 ∧
      oddGamma N m * centralUpperRoot N m ^ 2 / 2 <
        2 * centralDeficit N ∧
      oddGamma N m * centralUpperRoot N m ^ 2 / 2 <
        oddProxyScale N m * centralUpperRoot N m ^ 2 / 2 := by
  let a : ℝ := centralDeficit N
  let alpha : ℝ := oddAlpha N m
  let gamma : ℝ := oddGamma N m
  let r : ℝ := alpha / (2 * (N : ℝ))
  let beta : ℝ := centralUpperRoot N m
  let c : ℝ := gamma * beta ^ 2 / 2
  let d : ℝ := oddProxyScale N m * beta ^ 2 / 2
  have hNr : 0 < (N : ℝ) := by positivity
  have ha : 0 < a := by dsimp [a]; exact centralDeficit_pos (by omega)
  have halpha : 0 < alpha := by dsimp [alpha]; exact oddAlpha_pos (by omega) hmHalf
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    exact oddGamma_pos (by omega) hOdd (by omega) hmHalf
  have hr : 0 < r := by dsimp [r]; positivity
  have hdisc : 0 < _root_.SharpSerfling.Analysis.hardCentralDiscriminant a r gamma := by
    unfold _root_.SharpSerfling.Analysis.hardCentralDiscriminant
    dsimp [a, r, gamma, alpha] at hcross ⊢
    linarith
  have hbeta : 0 < beta := by
    have hlower := _root_.SharpSerfling.Analysis.hardCentral_lowerRoot_pos
      ha hr hgamma (by
        unfold _root_.SharpSerfling.Analysis.hardCentralDiscriminant at hdisc
        linarith)
    have hroots := _root_.SharpSerfling.Analysis.hardCentral_lowerRoot_lt_upperRoot
      hgamma hdisc
    dsimp [beta, centralUpperRoot, a, r, gamma, alpha]
    exact hlower.trans hroots
  have hroot : r * beta = a + gamma * beta ^ 2 / 2 := by
    dsimp [beta, centralUpperRoot]
    exact _root_.SharpSerfling.Analysis.hardCentral_upperRoot_equation
      (ne_of_gt hgamma) hdisc.le
  have hc : 0 < c := by dsimp [c]; positivity
  have hcLower : a < c := by
    have hbetaLower : r / gamma < beta := by
      dsimp [beta, centralUpperRoot]
      unfold _root_.SharpSerfling.Analysis.hardCentralUpperRoot
      rw [div_lt_div_iff₀ hgamma hgamma]
      have hsqrt := Real.sqrt_pos.2 hdisc
      nlinarith
    have hratio0 : 0 < r / gamma := div_pos hr hgamma
    have hsq : (r / gamma) ^ 2 < beta ^ 2 := by nlinarith
    have hcross' : 2 * gamma * a < r ^ 2 := by
      dsimp [a, r, gamma, alpha]
      exact hcross
    have hscaled : 2 * a / gamma < (r / gamma) ^ 2 := by
      rw [div_pow]
      field_simp [ne_of_gt hgamma]
      nlinarith
    dsimp [c]
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have := lt_trans hscaled hsq
    have hgamma0 := hgamma.le
    field_simp [ne_of_gt hgamma] at this
    nlinarith
  have hratioLt : 2 * r ^ 2 < (9 / 2) * (gamma * a) := by
    let u : ℝ := (m : ℝ) - 1
    have hu : 0 < u := by
      dsimp [u]
      have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
      linarith
    obtain ⟨huTenth, hN21, halphaThree⟩ :=
      centralCrossing_size_bounds hN hOdd hm3 hmHalf hcross
    have hgap := oddGamma_ge_alpha_sq_add_u_div_seven
      (N := N) (m := m) (by omega) hOdd hm3 hmHalf (by
        linarith)
    have hgammaStrict : alpha ^ 2 / 6 < gamma := by
      dsimp [alpha, gamma]
      dsimp [u] at hu
      have hfrac : 0 < ((m : ℝ) - 1) / (7 * (N : ℝ)) := by positivity
      linarith
    have haLower := (centralDeficit_bounds (N := N) (by omega)).1
    have haLowerPos : 0 < 2 / (3 * (N : ℝ) ^ 2) := by positivity
    have hmul1 := mul_lt_mul_of_pos_right hgammaStrict haLowerPos
    have hmul2 := mul_le_mul_of_nonneg_left haLower hgamma.le
    have hbase : alpha ^ 2 / (9 * (N : ℝ) ^ 2) < gamma * a := by
      dsimp [a]
      calc
        alpha ^ 2 / (9 * (N : ℝ) ^ 2) =
            (alpha ^ 2 / 6) * (2 / (3 * (N : ℝ) ^ 2)) := by ring
        _ < gamma * (2 / (3 * (N : ℝ) ^ 2)) := hmul1
        _ ≤ gamma * centralDeficit N := hmul2
    dsimp [r]
    have hNr0 : (N : ℝ) ≠ 0 := ne_of_gt hNr
    field_simp [hNr0] at hbase ⊢
    nlinarith
  have hcUpper : c < 2 * a := by
    by_contra hnot
    have hca : 2 * a ≤ c := le_of_not_gt hnot
    have hfactor1 : 0 ≤ c - 2 * a := sub_nonneg.mpr hca
    have hfactor2 : 0 ≤ c - a / 2 := by nlinarith
    have hpoly : (9 / 2) * a * c ≤ (a + c) ^ 2 := by
      have := mul_nonneg hfactor1 hfactor2
      nlinarith
    have hrootSq : r ^ 2 * beta ^ 2 = (a + c) ^ 2 := by
      have hrootC : r * beta = a + c := by
        dsimp [c]
        exact hroot
      have hsquare := congrArg (fun x : ℝ ↦ x ^ 2) hrootC
      nlinarith
    have hcEq : gamma * beta ^ 2 = 2 * c := by dsimp [c]; ring
    have hscaled : (9 / 2) * (gamma * a) * c ≤ 2 * r ^ 2 * c := by
      have hmul := mul_le_mul_of_nonneg_left hpoly hgamma.le
      nlinarith
    have hc0 : 0 < c := hc
    nlinarith
  have hBpos : 0 < oddProxyScale (N - 2) (m - 1) + 1 / 12 := by
    have hred : 0 < oddProxyScale (N - 2) (m - 1) := by
      apply oddProxyScale_pos (by omega) (by omega)
      omega
    positivity
  have hgammaLtS : gamma < oddProxyScale N m := by
    dsimp [gamma]
    unfold oddGamma
    linarith
  have hcLtD : c < d := by
    dsimp [c, d]
    have hbetaSq : 0 < beta ^ 2 / 2 := by positivity
    have hmul := mul_lt_mul_of_pos_right hgammaLtS hbetaSq
    simpa [mul_div_assoc] using hmul
  exact ⟨by simpa [a, c, beta, gamma] using hcLower,
    by simpa [a, c, beta, gamma] using hcUpper,
    by simpa [c, d, beta, gamma] using hcLtD⟩

/-- Quantitative separation of `c` from the endpoint `2a`. -/
theorem centralCrossing_two_a_sub_c_lower {N m : ℕ}
    (hN : 7 ≤ N) (hOdd : Odd N) (hm3 : 3 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (hcross : 2 * oddGamma N m * centralDeficit N <
      (oddAlpha N m / (2 * (N : ℝ))) ^ 2) :
    (90 * ((m : ℝ) - 1) / (19 * (N : ℝ))) * centralDeficit N ≤
      2 * centralDeficit N -
        oddGamma N m * centralUpperRoot N m ^ 2 / 2 := by
  let u : ℝ := (m : ℝ) - 1
  let a : ℝ := centralDeficit N
  let alpha : ℝ := oddAlpha N m
  let gamma : ℝ := oddGamma N m
  let r : ℝ := alpha / (2 * (N : ℝ))
  let beta : ℝ := centralUpperRoot N m
  let c : ℝ := gamma * beta ^ 2 / 2
  let z : ℝ := a / c
  have hNr : 0 < (N : ℝ) := by positivity
  have hNr0 : (N : ℝ) ≠ 0 := ne_of_gt hNr
  have hu : 0 < u := by
    dsimp [u]
    have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
    linarith
  obtain ⟨huTenth0, hN21, halphaThree0⟩ :=
    centralCrossing_size_bounds hN hOdd hm3 hmHalf hcross
  have huTenth : u < (N : ℝ) / 10 := by simpa [u] using huTenth0
  have ha : 0 < a := by dsimp [a]; exact centralDeficit_pos (by omega)
  have halpha : 0 < alpha := by dsimp [alpha]; exact oddAlpha_pos (by omega) hmHalf
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    exact oddGamma_pos (by omega) hOdd (by omega) hmHalf
  have hr : 0 < r := by dsimp [r]; positivity
  have hbeta : 0 < beta := by
    have hdisc : 0 < _root_.SharpSerfling.Analysis.hardCentralDiscriminant a r gamma := by
      unfold _root_.SharpSerfling.Analysis.hardCentralDiscriminant
      dsimp [a, r, gamma, alpha] at hcross ⊢
      linarith
    have hlower := _root_.SharpSerfling.Analysis.hardCentral_lowerRoot_pos
      ha hr hgamma (by
        unfold _root_.SharpSerfling.Analysis.hardCentralDiscriminant at hdisc
        linarith)
    have hroots := _root_.SharpSerfling.Analysis.hardCentral_lowerRoot_lt_upperRoot
      hgamma hdisc
    dsimp [beta, centralUpperRoot, a, r, gamma, alpha]
    exact hlower.trans hroots
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨hcLower0, hcUpper0, _⟩ :=
    centralCrossing_order_bounds hN hOdd hm3 hmHalf hcross
  have hcLower : a < c := by simpa [a, c, beta, gamma] using hcLower0
  have hcUpper : c < 2 * a := by simpa [a, c, beta, gamma] using hcUpper0
  have hz0 : 0 < z := div_pos ha hc
  have hz1 : z < 1 := (div_lt_one hc).2 hcLower
  have hzHalf : 1 / 2 < z := by
    dsimp [z]
    rw [lt_div_iff₀ hc]
    nlinarith
  have hroot : r * beta = a + c := by
    have hdisc : 0 ≤ _root_.SharpSerfling.Analysis.hardCentralDiscriminant a r gamma := by
      unfold _root_.SharpSerfling.Analysis.hardCentralDiscriminant
      dsimp [a, r, gamma, alpha] at hcross ⊢
      linarith
    have h := _root_.SharpSerfling.Analysis.hardCentral_upperRoot_equation
      (a := a) (r := r) (gamma := gamma) (ne_of_gt hgamma) hdisc
    have hbetaDef : beta = _root_.SharpSerfling.Analysis.hardCentralUpperRoot a r gamma := by
      dsimp [beta, centralUpperRoot, a, r, gamma, alpha]
    rw [hbetaDef]
    simpa [c, hbetaDef] using h
  have hrootSq : r ^ 2 * beta ^ 2 = (a + c) ^ 2 := by
    have hsquare := congrArg (fun x : ℝ ↦ x ^ 2) hroot
    nlinarith
  have hcEq : gamma * beta ^ 2 = 2 * c := by dsimp [c]; ring
  have hratioIdentity :
      2 * r ^ 2 / (gamma * a) = 2 + z + 1 / z := by
    dsimp [z]
    field_simp [ne_of_gt hgamma, ne_of_gt ha, ne_of_gt hc]
    nlinarith
  have haLower := (centralDeficit_bounds (N := N) (by omega)).1
  have hgap := oddGamma_ge_alpha_sq_add_u_div_seven
    (N := N) (m := m) (by omega) hOdd hm3 hmHalf (by
      dsimp [u] at huTenth ⊢
      linarith)
  let denom : ℝ := 7 * (N : ℝ) * alpha ^ 2 + 6 * u
  have hdenom : 0 < denom := by dsimp [denom]; positivity
  have hgammaA :
      (alpha ^ 2 / 6 + u / (7 * (N : ℝ))) *
          (2 / (3 * (N : ℝ) ^ 2)) ≤ gamma * a := by
    have hleft0 : 0 ≤ alpha ^ 2 / 6 + u / (7 * (N : ℝ)) := by positivity
    have hright0 : 0 ≤ 2 / (3 * (N : ℝ) ^ 2) := by positivity
    have hgamma0 : 0 ≤ gamma := hgamma.le
    dsimp [a, alpha, gamma] at hgap ⊢
    nlinarith [mul_le_mul hgap haLower hright0 hgamma0]
  let coeff : ℝ := (9 / 2) * (7 * (N : ℝ) * alpha ^ 2) / denom
  have hcoeff0 : 0 ≤ coeff := by dsimp [coeff]; positivity
  have hratioUpper :
      2 * r ^ 2 / (gamma * a) ≤
        (9 / 2) * (7 * (N : ℝ) * alpha ^ 2) / denom := by
    rw [div_le_iff₀ (mul_pos hgamma ha)]
    calc
      2 * r ^ 2 = coeff *
          ((alpha ^ 2 / 6 + u / (7 * (N : ℝ))) *
            (2 / (3 * (N : ℝ) ^ 2))) := by
        dsimp [coeff, denom, r]
        field_simp [hNr0, ne_of_gt hdenom]
        ring
      _ ≤ coeff * (gamma * a) :=
        mul_le_mul_of_nonneg_left hgammaA hcoeff0
      _ = ((9 / 2) * (7 * (N : ℝ) * alpha ^ 2) / denom) *
          (gamma * a) := by rfl
  have hgapRatio :
      27 * u / denom ≤ 9 / 2 - 2 * r ^ 2 / (gamma * a) := by
    calc
      27 * u / denom = 9 / 2 -
          (9 / 2) * (7 * (N : ℝ) * alpha ^ 2) / denom := by
        dsimp [denom]
        field_simp [ne_of_gt hdenom]
        ring
      _ ≤ 9 / 2 - 2 * r ^ 2 / (gamma * a) := sub_le_sub_left hratioUpper _
  have hgapZ : 27 * u / denom ≤
      ((2 - z) / 2) * ((2 * z - 1) / z) := by
    calc
      27 * u / denom ≤ 9 / 2 - 2 * r ^ 2 / (gamma * a) := hgapRatio
      _ = ((2 - z) / 2) * ((2 * z - 1) / z) := by
        rw [hratioIdentity]
        field_simp [ne_of_gt hz0]
        ring
  have hq0 : 0 ≤ (2 * z - 1) / z := by
    exact div_nonneg (by linarith) hz0.le
  have hcoefUpper : (2 - z) / 2 ≤ 3 / 4 := by linarith
  have hgapQ : 36 * u / denom ≤ (2 * z - 1) / z := by
    have hmul := mul_le_mul_of_nonneg_right hcoefUpper hq0
    calc
      36 * u / denom = (4 / 3) * (27 * u / denom) := by ring
      _ ≤ (4 / 3) * (((2 - z) / 2) * ((2 * z - 1) / z)) :=
        mul_le_mul_of_nonneg_left hgapZ (by norm_num)
      _ ≤ (4 / 3) * ((3 / 4) * ((2 * z - 1) / z)) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = (2 * z - 1) / z := by ring
  have halphaOne : alpha ^ 2 ≤ 1 := by
    have halphaLt : alpha < 1 := by
      dsimp [alpha]
      unfold oddAlpha
      have hden : 0 < (N : ℝ) - 2 := by
        have hNR : (21 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN21
        linarith only [hNR]
      rw [div_lt_one hden]
      have hmR : (0 : ℝ) < (m : ℝ) := by positivity
      linarith
    have hprod := mul_nonneg halpha.le (sub_nonneg.mpr halphaLt.le)
    nlinarith only [hprod]
  have hdenomUpper : denom ≤ (38 / 5) * (N : ℝ) := by
    have hNa := mul_le_mul_of_nonneg_left halphaOne hNr.le
    dsimp [denom]
    nlinarith only [hNa, huTenth]
  have htargetFrac : 90 * u / (19 * (N : ℝ)) ≤ 36 * u / denom := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hNr) hdenom]
    have hcoef90 : 0 ≤ (90 : ℝ) * u := by positivity
    have hmulden := mul_le_mul_of_nonneg_left hdenomUpper
      hcoef90
    nlinarith only [hmulden]
  have hqTarget : 90 * u / (19 * (N : ℝ)) ≤ (2 * z - 1) / z :=
    htargetFrac.trans hgapQ
  have haMul := mul_le_mul_of_nonneg_left hqTarget ha.le
  have hid : a * ((2 * z - 1) / z) = 2 * a - c := by
    dsimp [z]
    field_simp [ne_of_gt hc]
  rw [hid] at haMul
  simpa [u, a, c, beta, gamma, mul_comm, mul_left_comm, mul_assoc] using haMul

/-- Quantitative separation of `d` from `c`. -/
theorem centralCrossing_d_sub_c_lower {N m : ℕ}
    (hN : 7 ≤ N) (hOdd : Odd N) (hm3 : 3 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (hcross : 2 * oddGamma N m * centralDeficit N <
      (oddAlpha N m / (2 * (N : ℝ))) ^ 2) :
    (6 * ((m : ℝ) - 1) / 5) * centralDeficit N ≤
      oddProxyScale N m * centralUpperRoot N m ^ 2 / 2 -
        oddGamma N m * centralUpperRoot N m ^ 2 / 2 := by
  let u : ℝ := (m : ℝ) - 1
  let a : ℝ := centralDeficit N
  let gamma : ℝ := oddGamma N m
  let beta : ℝ := centralUpperRoot N m
  let c : ℝ := gamma * beta ^ 2 / 2
  let B : ℝ := oddProxyScale (N - 2) (m - 1) + 1 / 12
  have hNr : 0 < (N : ℝ) := by positivity
  have hN21 := (centralCrossing_size_bounds hN hOdd hm3 hmHalf hcross).2.1
  have huTenth0 := (centralCrossing_size_bounds hN hOdd hm3 hmHalf hcross).1
  have huTenth : u < (N : ℝ) / 10 := by simpa [u] using huTenth0
  have hu : 0 < u := by
    dsimp [u]
    have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
    linarith
  have ha : 0 < a := by dsimp [a]; exact centralDeficit_pos (by omega)
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    exact oddGamma_pos (by omega) hOdd (by omega) hmHalf
  have hbeta : 0 < beta := by
    let alpha : ℝ := oddAlpha N m
    let r : ℝ := alpha / (2 * (N : ℝ))
    have halpha : 0 < alpha := by dsimp [alpha]; exact oddAlpha_pos (by omega) hmHalf
    have hr : 0 < r := by dsimp [r]; positivity
    have hdisc : 0 < _root_.SharpSerfling.Analysis.hardCentralDiscriminant a r gamma := by
      unfold _root_.SharpSerfling.Analysis.hardCentralDiscriminant
      dsimp [a, r, gamma, alpha] at hcross ⊢
      linarith
    have hlower := _root_.SharpSerfling.Analysis.hardCentral_lowerRoot_pos
      ha hr hgamma (by
        unfold _root_.SharpSerfling.Analysis.hardCentralDiscriminant at hdisc
        linarith)
    have hroots := _root_.SharpSerfling.Analysis.hardCentral_lowerRoot_lt_upperRoot
      hgamma hdisc
    dsimp [beta, centralUpperRoot, a, r, gamma, alpha]
    exact hlower.trans hroots
  have hc : 0 < c := by dsimp [c]; positivity
  have hcLower0 := (centralCrossing_order_bounds hN hOdd hm3 hmHalf hcross).1
  have hcLower : a < c := by simpa [a, c, beta, gamma] using hcLower0
  have hgammaUpper : gamma ≤ 1 / 6 := by
    dsimp [gamma]
    exact oddGamma_le_one_sixth hN hOdd hm3 hmHalf
  have hOddRed : Odd (N - 2) := by
    obtain ⟨q, hq⟩ := hOdd
    use q - 1
    omega
  have hkLower := kappa_odd_lower (N := N - 2) (by omega) hOddRed
  have hN2pos : 0 < (N : ℝ) - 2 := by
    have hNR : (21 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN21
    linarith only [hNR]
  have hkEight : (8 / 9 : ℝ) ≤ SharpSerfling.kappa (N - 2) := by
    apply le_trans _ hkLower
    rw [Nat.cast_sub (by omega)]
    norm_num only [Nat.cast_ofNat]
    rw [le_sub_iff_add_le]
    have hNR : (21 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN21
    have hdenPos : 0 < 2 * ((N : ℝ) - 2) ^ 2 := by positivity
    have hinv : 1 / (2 * ((N : ℝ) - 2) ^ 2) ≤ 1 / 9 := by
      rw [div_le_div_iff₀ hdenPos (by norm_num : (0 : ℝ) < 9)]
      nlinarith [sq_nonneg ((N : ℝ) - 2)]
    linarith
  let Ared : ℝ := u * ((N : ℝ) - 2 - u) / (4 * ((N : ℝ) - 3))
  have hN3 : 0 < (N : ℝ) - 3 := by
    have hNR : (21 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN21
    linarith only [hNR]
  have hAred0 : 0 ≤ Ared := by
    dsimp [Ared]
    have : 0 ≤ (N : ℝ) - 2 - u := by nlinarith
    positivity
  have hAredLower : 9 * u / 40 ≤ Ared := by
    dsimp [Ared]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 40)
      (mul_pos (by norm_num) hN3)]
    nlinarith [mul_pos hu (sub_pos.mpr huTenth)]
  have hscaleEq : oddProxyScale (N - 2) (m - 1) =
      SharpSerfling.kappa (N - 2) * Ared := by
    unfold oddProxyScale
    dsimp [Ared, u]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num only [Nat.cast_ofNat]
    ring
  have hscaleLower : u / 5 ≤ oddProxyScale (N - 2) (m - 1) := by
    rw [hscaleEq]
    calc
      u / 5 = (8 / 9 : ℝ) * (9 * u / 40) := by ring
      _ ≤ (8 / 9 : ℝ) * Ared :=
        mul_le_mul_of_nonneg_left hAredLower (by norm_num)
      _ ≤ SharpSerfling.kappa (N - 2) * Ared :=
        mul_le_mul_of_nonneg_right hkEight hAred0
  have hBLower : u / 5 ≤ B := by
    dsimp [B]
    linarith
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity) hBLower
  have hbetaGamma : 6 * c ≤ beta ^ 2 / 2 := by
    dsimp [c]
    have hmul := mul_le_mul_of_nonneg_right hgammaUpper (sq_nonneg beta)
    nlinarith
  have hBa : (6 * B) * a ≤ B * (beta ^ 2 / 2) := by
    have hcSix : 6 * a ≤ 6 * c := by nlinarith
    have hchain : 6 * a ≤ beta ^ 2 / 2 := hcSix.trans hbetaGamma
    have hmul := mul_le_mul_of_nonneg_left hchain hBpos.le
    nlinarith
  have hleft : (6 * u / 5) * a ≤ (6 * B) * a := by
    have hmul := mul_le_mul_of_nonneg_right hBLower ha.le
    nlinarith
  have hgapEq : oddProxyScale N m * beta ^ 2 / 2 - gamma * beta ^ 2 / 2 =
      B * (beta ^ 2 / 2) := by
    dsimp [B, gamma]
    unfold oddGamma
    ring
  calc
    (6 * ((m : ℝ) - 1) / 5) * centralDeficit N = (6 * u / 5) * a := by rfl
    _ ≤ (6 * B) * a := hleft
    _ ≤ B * (beta ^ 2 / 2) := hBa
    _ = oddProxyScale N m * beta ^ 2 / 2 - gamma * beta ^ 2 / 2 := hgapEq.symm
    _ = _ := by rfl

/-- The exponential parameter `d` is uniformly small on a crossing slice. -/
theorem centralCrossing_d_bounds {N m : ℕ}
    (hN : 7 ≤ N) (hOdd : Odd N) (hm3 : 3 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (hcross : 2 * oddGamma N m * centralDeficit N <
      (oddAlpha N m / (2 * (N : ℝ))) ^ 2) :
    oddProxyScale N m * centralUpperRoot N m ^ 2 / 2 <
        (16 * (m : ℝ) / 3) * centralDeficit N ∧
      oddProxyScale N m * centralUpperRoot N m ^ 2 / 2 < 1 / 10 ∧
      Real.exp (oddProxyScale N m * centralUpperRoot N m ^ 2 / 2) ≤ 10 / 9 := by
  let u : ℝ := (m : ℝ) - 1
  let a : ℝ := centralDeficit N
  let alpha : ℝ := oddAlpha N m
  let gamma : ℝ := oddGamma N m
  let beta : ℝ := centralUpperRoot N m
  let c : ℝ := gamma * beta ^ 2 / 2
  let d : ℝ := oddProxyScale N m * beta ^ 2 / 2
  have hNr : 0 < (N : ℝ) := by positivity
  have hNr0 : (N : ℝ) ≠ 0 := ne_of_gt hNr
  obtain ⟨huTenth0, hN21, halphaThree0⟩ :=
    centralCrossing_size_bounds hN hOdd hm3 hmHalf hcross
  have huTenth : u < (N : ℝ) / 10 := by simpa [u] using huTenth0
  have ha : 0 < a := by dsimp [a]; exact centralDeficit_pos (by omega)
  have halpha : 0 < alpha := by dsimp [alpha]; exact oddAlpha_pos (by omega) hmHalf
  have halphaThree : 3 / 4 < alpha := by simpa [alpha] using halphaThree0
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    exact oddGamma_pos (by omega) hOdd (by omega) hmHalf
  have hbeta : 0 < beta := by
    let r : ℝ := alpha / (2 * (N : ℝ))
    have hr : 0 < r := by dsimp [r]; positivity
    have hdisc : 0 < _root_.SharpSerfling.Analysis.hardCentralDiscriminant a r gamma := by
      unfold _root_.SharpSerfling.Analysis.hardCentralDiscriminant
      dsimp [a, r, gamma, alpha] at hcross ⊢
      linarith
    have hlower := _root_.SharpSerfling.Analysis.hardCentral_lowerRoot_pos
      ha hr hgamma (by
        unfold _root_.SharpSerfling.Analysis.hardCentralDiscriminant at hdisc
        linarith)
    have hroots := _root_.SharpSerfling.Analysis.hardCentral_lowerRoot_lt_upperRoot
      hgamma hdisc
    dsimp [beta, centralUpperRoot, a, r, gamma, alpha]
    exact hlower.trans hroots
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 < d := by
    dsimp [d]
    exact div_pos
      (mul_pos (oddProxyScale_pos (N := N) (m := m) (by omega) (by omega) (by omega))
        (sq_pos_of_pos hbeta)) (by norm_num)
  have hcUpper0 := (centralCrossing_order_bounds hN hOdd hm3 hmHalf hcross).2.1
  have hcUpper : c < 2 * a := by simpa [a, c, beta, gamma] using hcUpper0
  have hgammaLower : alpha ^ 2 / 6 ≤ gamma := by
    dsimp [alpha, gamma]
    exact oddGamma_ge_alpha_sq_div_six (by omega) hOdd (by omega) hmHalf
  have hSUpper : oddProxyScale N m ≤ (m : ℝ) / 4 := by
    have hk := kappa_odd_upper (N := N) (by omega) hOdd
    have hA0 : 0 ≤ (m : ℝ) * ((N : ℝ) - (m : ℝ)) /
        (4 * ((N : ℝ) - 1)) := by
      have hmN : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show m ≤ N by omega)
      have hNR : (21 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN21
      have hN1 : 0 < (N : ℝ) - 1 := by linarith only [hNR]
      positivity
    have hmul := mul_le_mul_of_nonneg_right hk hA0
    unfold oddProxyScale
    calc
      SharpSerfling.kappa N *
          ((m : ℝ) * ((N : ℝ) - (m : ℝ)) / (4 * ((N : ℝ) - 1))) ≤
        (m : ℝ) * ((N : ℝ) - (m : ℝ)) /
          (4 * ((N : ℝ) - 1)) := by simpa using hmul
      _ ≤ (m : ℝ) / 4 := by
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
        have hNR : (21 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN21
        have hN1 : 0 < (N : ℝ) - 1 := by linarith only [hNR]
        rw [div_le_iff₀ (mul_pos (by norm_num) hN1)]
        nlinarith
  have hdRelation : gamma * d = oddProxyScale N m * c := by
    dsimp [c, d]
    ring
  have hdUpperAlpha : d < (3 * (m : ℝ) / alpha ^ 2) * a := by
    have hgammaD : gamma * d < oddProxyScale N m * (2 * a) := by
      rw [hdRelation]
      exact mul_lt_mul_of_pos_left hcUpper
        (oddProxyScale_pos (N := N) (m := m) (by omega) (by omega) (by omega))
    have hleft : (alpha ^ 2 / 6) * d ≤ gamma * d :=
      mul_le_mul_of_nonneg_right hgammaLower hd.le
    have hright : oddProxyScale N m * (2 * a) ≤ ((m : ℝ) / 4) * (2 * a) :=
      mul_le_mul_of_nonneg_right hSUpper (mul_nonneg (by norm_num) ha.le)
    have hchain : (alpha ^ 2 / 6) * d < ((m : ℝ) / 4) * (2 * a) :=
      lt_of_le_of_lt hleft (lt_of_lt_of_le hgammaD hright)
    have halphaSq : 0 < alpha ^ 2 := sq_pos_of_pos halpha
    rw [show (3 * (m : ℝ) / alpha ^ 2) * a =
      (3 * (m : ℝ) * a) / alpha ^ 2 by ring]
    rw [lt_div_iff₀ halphaSq]
    nlinarith
  have hdUpper : d < (16 * (m : ℝ) / 3) * a := by
    have halphaSq : (9 / 16 : ℝ) < alpha ^ 2 := by nlinarith
    have hcoef : 3 * (m : ℝ) / alpha ^ 2 < 16 * (m : ℝ) / 3 := by
      rw [div_lt_div_iff₀ (sq_pos_of_pos halpha) (by norm_num : (0 : ℝ) < 3)]
      have hmR : 0 < (m : ℝ) := by positivity
      nlinarith
    exact hdUpperAlpha.trans (mul_lt_mul_of_pos_right hcoef ha)
  have haUpper := (centralDeficit_bounds (N := N) (by omega)).2
  have hdTenth : d < 1 / 10 := by
    have hdN : d < 4 * (m : ℝ) / (N : ℝ) ^ 2 := by
      calc
        d < (16 * (m : ℝ) / 3) * a := hdUpper
        _ ≤ (16 * (m : ℝ) / 3) * (3 / (4 * (N : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left haUpper (by positivity)
        _ = 4 * (m : ℝ) / (N : ℝ) ^ 2 := by ring
    have hmBound : (m : ℝ) < (N : ℝ) / 10 + 1 := by
      dsimp [u] at huTenth
      linarith
    have hfrac : 4 * (m : ℝ) / (N : ℝ) ^ 2 ≤ 1 / 10 := by
      rw [div_le_iff₀ (sq_pos_of_pos hNr)]
      have hNreal : (21 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN21
      nlinarith [sq_nonneg ((N : ℝ) - 2)]
    exact hdN.trans_le hfrac
  have hexp : Real.exp d ≤ 10 / 9 := by
    calc
      Real.exp d ≤ 1 / (1 - d) :=
        Real.exp_bound_div_one_sub_of_interval hd.le (hdTenth.trans (by norm_num))
      _ ≤ 10 / 9 := by
        rw [div_le_div_iff₀ (sub_pos.mpr (hdTenth.trans (by norm_num)))
          (by norm_num : (0 : ℝ) < 9)]
        nlinarith
  exact ⟨by simpa [a, d, beta] using hdUpper,
    by simpa [d, beta] using hdTenth,
    by simpa [d, beta] using hexp⟩

/-- The final numerical inequality required by the signed-area lemma. -/
theorem centralCrossing_singleCrossing_certificate {N m : ℕ}
    (hN : 7 ≤ N) (hOdd : Odd N) (hm3 : 3 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (hcross : 2 * oddGamma N m * centralDeficit N <
      (oddAlpha N m / (2 * (N : ℝ))) ^ 2) :
    centralDeficit N ^ 3 +
        (oddGamma N m * centralUpperRoot N m ^ 2 / 2) *
          (oddProxyScale N m * centralUpperRoot N m ^ 2 / 2) ^ 2 *
            Real.exp (oddProxyScale N m * centralUpperRoot N m ^ 2 / 2) ≤
      (2 * centralDeficit N -
          oddGamma N m * centralUpperRoot N m ^ 2 / 2) *
        (oddProxyScale N m * centralUpperRoot N m ^ 2 / 2 -
          oddGamma N m * centralUpperRoot N m ^ 2 / 2) := by
  let u : ℝ := (m : ℝ) - 1
  let a : ℝ := centralDeficit N
  let gamma : ℝ := oddGamma N m
  let beta : ℝ := centralUpperRoot N m
  let c : ℝ := gamma * beta ^ 2 / 2
  let d : ℝ := oddProxyScale N m * beta ^ 2 / 2
  have hNr : 0 < (N : ℝ) := by positivity
  have hNr0 : (N : ℝ) ≠ 0 := ne_of_gt hNr
  obtain ⟨huTenth0, hN21, _⟩ :=
    centralCrossing_size_bounds hN hOdd hm3 hmHalf hcross
  have huTenth : u < (N : ℝ) / 10 := by simpa [u] using huTenth0
  have hu2 : 2 ≤ u := by
    dsimp [u]
    have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
    linarith
  have hu0 : 0 ≤ u := hu2.trans' (by norm_num)
  have ha : 0 < a := by dsimp [a]; exact centralDeficit_pos (by omega)
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    exact oddGamma_pos (by omega) hOdd (by omega) hmHalf
  have hbeta : 0 < beta := by
    let alpha : ℝ := oddAlpha N m
    let r : ℝ := alpha / (2 * (N : ℝ))
    have halpha : 0 < alpha := by dsimp [alpha]; exact oddAlpha_pos (by omega) hmHalf
    have hr : 0 < r := by dsimp [r]; positivity
    have hdisc : 0 < _root_.SharpSerfling.Analysis.hardCentralDiscriminant a r gamma := by
      unfold _root_.SharpSerfling.Analysis.hardCentralDiscriminant
      dsimp [a, r, gamma, alpha] at hcross ⊢
      linarith
    have hlower := _root_.SharpSerfling.Analysis.hardCentral_lowerRoot_pos
      ha hr hgamma (by
        unfold _root_.SharpSerfling.Analysis.hardCentralDiscriminant at hdisc
        linarith)
    have hroots := _root_.SharpSerfling.Analysis.hardCentral_lowerRoot_lt_upperRoot
      hgamma hdisc
    dsimp [beta, centralUpperRoot, a, r, gamma, alpha]
    exact hlower.trans hroots
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 < d := by
    dsimp [d]
    exact div_pos
      (mul_pos (oddProxyScale_pos (N := N) (m := m) (by omega) (by omega) (by omega))
        (sq_pos_of_pos hbeta)) (by norm_num)
  have hcUpper0 := (centralCrossing_order_bounds hN hOdd hm3 hmHalf hcross).2.1
  have hcUpper : c ≤ 2 * a := by
    simpa [a, c, beta, gamma] using hcUpper0.le
  obtain ⟨hdUpper0, _, hexp0⟩ := centralCrossing_d_bounds hN hOdd hm3 hmHalf hcross
  have hdUpper : d ≤ (16 * (m : ℝ) / 3) * a := by
    simpa [a, d, beta] using hdUpper0.le
  have hexp : Real.exp d ≤ 10 / 9 := by simpa [d, beta] using hexp0
  have hDupper0 : 0 ≤ (16 * (m : ℝ) / 3) * a := by positivity
  have hdSq : d ^ 2 ≤ ((16 * (m : ℝ) / 3) * a) ^ 2 := by
    nlinarith
  have hcdSq : c * d ^ 2 ≤ (2 * a) * ((16 * (m : ℝ) / 3) * a) ^ 2 := by
    exact mul_le_mul hcUpper hdSq (sq_nonneg d) (by positivity)
  have hcdExp : c * d ^ 2 * Real.exp d ≤
      ((2 * a) * ((16 * (m : ℝ) / 3) * a) ^ 2) * (10 / 9) := by
    exact mul_le_mul hcdSq hexp (Real.exp_pos d).le (by positivity)
  have hupperFirst : a ^ 3 + c * d ^ 2 * Real.exp d ≤
      a ^ 3 * (1 + (5120 / 81) * (m : ℝ) ^ 2) := by
    calc
      a ^ 3 + c * d ^ 2 * Real.exp d ≤
          a ^ 3 + ((2 * a) * ((16 * (m : ℝ) / 3) * a) ^ 2) * (10 / 9) :=
        by simpa [add_comm] using add_le_add_left hcdExp (a ^ 3)
      _ = a ^ 3 * (1 + (5120 / 81) * (m : ℝ) ^ 2) := by ring
  have haUpper := (centralDeficit_bounds (N := N) (by omega)).2
  have hmU : (m : ℝ) ≤ (3 / 2) * u := by
    have hmEq : (m : ℝ) = u + 1 := by dsimp [u]; ring
    rw [hmEq]
    linarith
  have hmSq : (m : ℝ) ^ 2 ≤ ((3 / 2) * u) ^ 2 := by
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    have hright0 : 0 ≤ (3 / 2) * u := by positivity
    nlinarith
  have hcoeff :
      (3 / (4 * (N : ℝ) ^ 2)) *
          (1 + (5120 / 81) * (m : ℝ) ^ 2) ≤
        (5129 / 48) * u ^ 2 / (N : ℝ) ^ 2 := by
    have huSq : 4 ≤ u ^ 2 := by nlinarith
    field_simp [hNr0]
    nlinarith only [hmSq, huSq]
  have hfactor0 : 0 ≤ 1 + (5120 / 81) * (m : ℝ) ^ 2 := by positivity
  have haTimes := mul_le_mul_of_nonneg_right haUpper hfactor0
  have hupperSecond :
      a ^ 3 * (1 + (5120 / 81) * (m : ℝ) ^ 2) ≤
        ((5129 / 48) * u ^ 2 / (N : ℝ) ^ 2) * a ^ 2 := by
    have hbracket :
        a * (1 + (5120 / 81) * (m : ℝ) ^ 2) ≤
          (5129 / 48) * u ^ 2 / (N : ℝ) ^ 2 :=
      haTimes.trans hcoeff
    have hmul := mul_le_mul_of_nonneg_right hbracket (sq_nonneg a)
    nlinarith
  have hNreal : (21 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN21
  have hconstant :
      (5129 / 48) * u ^ 2 / (N : ℝ) ^ 2 ≤
        (108 / 19) * (u ^ 2 / (N : ℝ)) := by
    have huSq0 : 0 ≤ u ^ 2 := sq_nonneg u
    field_simp [hNr0]
    nlinarith only [hNreal, huSq0]
  have hupperThird :
      ((5129 / 48) * u ^ 2 / (N : ℝ) ^ 2) * a ^ 2 ≤
        ((108 / 19) * (u ^ 2 / (N : ℝ))) * a ^ 2 :=
    mul_le_mul_of_nonneg_right hconstant (sq_nonneg a)
  have hleft1 := centralCrossing_two_a_sub_c_lower hN hOdd hm3 hmHalf hcross
  have hleft2 := centralCrossing_d_sub_c_lower hN hOdd hm3 hmHalf hcross
  have hleft1' : (90 * u / (19 * (N : ℝ))) * a ≤ 2 * a - c := by
    simpa [u, a, c, beta, gamma] using hleft1
  have hleft2' : (6 * u / 5) * a ≤ d - c := by
    simpa [u, a, c, d, beta, gamma] using hleft2
  have hleftProduct :
      ((90 * u / (19 * (N : ℝ))) * a) * ((6 * u / 5) * a) ≤
        (2 * a - c) * (d - c) := by
    have hactual1 : 0 ≤ 2 * a - c := hleft1'.trans' (by positivity)
    have hlower2 : 0 ≤ (6 * u / 5) * a := by positivity
    exact mul_le_mul hleft1' hleft2' hlower2 hactual1
  have hleftSimplified :
      ((108 / 19) * (u ^ 2 / (N : ℝ))) * a ^ 2 ≤
        (2 * a - c) * (d - c) := by
    calc
      ((108 / 19) * (u ^ 2 / (N : ℝ))) * a ^ 2 =
          ((90 * u / (19 * (N : ℝ))) * a) * ((6 * u / 5) * a) := by ring
      _ ≤ (2 * a - c) * (d - c) := hleftProduct
  have hfinal : a ^ 3 + c * d ^ 2 * Real.exp d ≤ (2 * a - c) * (d - c) :=
    hupperFirst.trans (hupperSecond.trans (hupperThird.trans hleftSimplified))
  simpa [a, c, d, beta, gamma] using hfinal

/-- Full verification of the manuscript's central-parameter lemma. -/
theorem centralParameters {N m : ℕ}
    (hN : 7 ≤ N) (hOdd : Odd N) (hm3 : 3 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (hcross : 2 * oddGamma N m * centralDeficit N <
      (oddAlpha N m / (2 * (N : ℝ))) ^ 2) :
    CentralParameterCertificate N m := by
  obtain ⟨hac, hc2, hcd⟩ := centralCrossing_order_bounds hN hOdd hm3 hmHalf hcross
  exact ⟨hac, hcd, hc2.le,
    centralCrossing_singleCrossing_certificate hN hOdd hm3 hmHalf hcross⟩

/-- Unconditional hard-central induction step for every `m ≥ 3`. -/
theorem mgf_le_oddProxy_lowerNearest_of_reduced {N m : ℕ}
    (hN : 7 ≤ N) (hOdd : Odd N) (hm3 : 3 ≤ m)
    (hmHalf : m ≤ (N - 1) / 2)
    (hred : ∀ u : ℝ, 0 ≤ u →
      mgf (N - 2) (((N - 1) / 2) - 1) (m - 1) u ≤
        Real.exp (oddProxyScale (N - 2) (m - 1) * u ^ 2 / 2))
    {t : ℝ} (ht : 0 ≤ t) :
    mgf N ((N - 1) / 2) m t ≤
      Real.exp (oddProxyScale N m * t ^ 2 / 2) := by
  exact mgf_le_oddProxy_lowerNearest_of_reduced_and_centralParameters
    hN hOdd hm3 hmHalf (centralParameters hN hOdd hm3 hmHalf) hred ht

end SharpSerfling.Hypergeometric
