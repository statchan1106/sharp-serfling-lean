import SharpSerfling.Basic

namespace SharpSerfling.Certificates

/-- A concave quadratic is nonnegative between two nonnegative endpoint values. -/
theorem concaveQuadratic_nonneg {a b c l r x : ℝ}
    (ha : a ≤ 0) (hlr : l ≤ r) (hlx : l ≤ x) (hxr : x ≤ r)
    (hql : 0 ≤ a * l ^ 2 + b * l + c)
    (hqr : 0 ≤ a * r ^ 2 + b * r + c) :
    0 ≤ a * x ^ 2 + b * x + c := by
  by_cases heq : l = r
  · have hx : x = l := by linarith
    simpa [hx] using hql
  · have hrl : 0 < r - l := sub_pos.mpr (lt_of_le_of_ne hlr heq)
    have hleft : 0 ≤ (r - x) * (a * l ^ 2 + b * l + c) :=
      mul_nonneg (sub_nonneg.mpr hxr) hql
    have hright : 0 ≤ (x - l) * (a * r ^ 2 + b * r + c) :=
      mul_nonneg (sub_nonneg.mpr hlx) hqr
    have hcurve : 0 ≤ (-a) * (r - l) * (x - l) * (r - x) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (neg_nonneg.mpr ha) hrl.le) (sub_nonneg.mpr hlx))
        (sub_nonneg.mpr hxr)
    have hid :
        (r - l) * (a * x ^ 2 + b * x + c) =
          (r - x) * (a * l ^ 2 + b * l + c) +
          (x - l) * (a * r ^ 2 + b * r + c) +
          (-a) * (r - l) * (x - l) * (r - x) := by
      ring
    have hprod : 0 ≤ (r - l) * (a * x ^ 2 + b * x + c) := by
      rw [hid]
      positivity
    have hprod' : 0 ≤ (a * x ^ 2 + b * x + c) * (r - l) := by
      simpa [mul_comm] using hprod
    exact nonneg_of_mul_nonneg_left hprod' hrl

/-- The polynomial `P₀(N,u)` from the manuscript's basic proxy-gap certificate. -/
def P0 (N u : ℝ) : ℝ :=
  (-4 * N ^ 4 + 19 * N ^ 3 - 21 * N ^ 2 + 48 * N - 36) * u ^ 2 +
  (4 * N ^ 5 - 27 * N ^ 4 + 59 * N ^ 3 - 90 * N ^ 2 + 132 * N - 72) * u +
  (-3 * N ^ 4 + 24 * N ^ 3 - 69 * N ^ 2 + 84 * N - 36)

theorem P0_at_one (N : ℝ) :
    P0 N 1 = 2 * (N - 3) *
      (2 * N ^ 4 - 11 * N ^ 3 + 18 * N ^ 2 - 36 * N + 24) := by
  simp only [P0]
  ring

theorem P0_at_right (N : ℝ) :
    P0 N ((N - 3) / 2) = (N - 3) * (N - 1) / 4 *
      (4 * N ^ 4 - 19 * N ^ 3 + 9 * N ^ 2 - 12) := by
  simp only [P0]
  ring

theorem P0_quadraticCoefficient_nonpos {N : ℝ} (hN : 5 ≤ N) :
    -4 * N ^ 4 + 19 * N ^ 3 - 21 * N ^ 2 + 48 * N - 36 ≤ 0 := by
  let x := N - 5
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hNrepr : N = x + 5 := by dsimp [x]; ring
  rw [hNrepr]
  have hpos : 0 < 4 * x ^ 4 + 61 * x ^ 3 + 336 * x ^ 2 + 737 * x + 446 := by
    positivity
  nlinarith

theorem P0_leftFactor_pos {N : ℝ} (hN : 5 ≤ N) :
    0 < 2 * N ^ 4 - 11 * N ^ 3 + 18 * N ^ 2 - 36 * N + 24 := by
  let x := N - 5
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hNrepr : N = x + 5 := by dsimp [x]; ring
  rw [hNrepr]
  ring_nf
  positivity

theorem P0_rightFactor_pos {N : ℝ} (hN : 5 ≤ N) :
    0 < 4 * N ^ 4 - 19 * N ^ 3 + 9 * N ^ 2 - 12 := by
  let x := N - 5
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hNrepr : N = x + 5 := by dsimp [x]; ring
  rw [hNrepr]
  ring_nf
  positivity

/-- Complete basic polynomial certificate on `1 ≤ u ≤ (N-3)/2`. -/
theorem P0_nonneg {N u : ℝ} (hN : 5 ≤ N) (hu1 : 1 ≤ u)
    (huN : u ≤ (N - 3) / 2) : 0 ≤ P0 N u := by
  let a := -4 * N ^ 4 + 19 * N ^ 3 - 21 * N ^ 2 + 48 * N - 36
  let b := 4 * N ^ 5 - 27 * N ^ 4 + 59 * N ^ 3 - 90 * N ^ 2 + 132 * N - 72
  let c := -3 * N ^ 4 + 24 * N ^ 3 - 69 * N ^ 2 + 84 * N - 36
  have ha : a ≤ 0 := P0_quadraticCoefficient_nonpos hN
  have hlr : (1 : ℝ) ≤ (N - 3) / 2 := by linarith
  have hleft : 0 ≤ a * (1 : ℝ) ^ 2 + b * 1 + c := by
    rw [show a * (1 : ℝ) ^ 2 + b * 1 + c = P0 N 1 by simp [a, b, c, P0]]
    rw [P0_at_one]
    have hfac := P0_leftFactor_pos hN
    have hN3 : 0 ≤ N - 3 := by linarith
    positivity
  have hright : 0 ≤ a * ((N - 3) / 2) ^ 2 + b * ((N - 3) / 2) + c := by
    rw [show a * ((N - 3) / 2) ^ 2 + b * ((N - 3) / 2) + c =
      P0 N ((N - 3) / 2) by simp [a, b, c, P0]]
    rw [P0_at_right]
    have hfac := P0_rightFactor_pos hN
    have hN3 : 0 ≤ N - 3 := by linarith
    have hN1 : 0 ≤ N - 1 := by linarith
    positivity
  have hquad := concaveQuadratic_nonneg ha hlr hu1 huN hleft hright
  simpa [P0, a, b, c] using hquad

/-- The polynomial `P₁₂(N,u)` from the `u/(12N)` proxy-gap certificate. -/
def P12 (N u : ℝ) : ℝ :=
  (-4 * N ^ 4 + 19 * N ^ 3 - 21 * N ^ 2 + 48 * N - 36) * u ^ 2 +
  (2 * N ^ 5 - 11 * N ^ 4 + 13 * N ^ 3 - 34 * N ^ 2 + 108 * N - 72) * u +
  (-3 * N ^ 4 + 24 * N ^ 3 - 69 * N ^ 2 + 84 * N - 36)

theorem P12_at_two (N : ℝ) :
    P12 N 2 =
      4 * N ^ 5 - 41 * N ^ 4 + 126 * N ^ 3 - 221 * N ^ 2 + 492 * N - 324 := by
  simp only [P12]
  ring

theorem P12_at_right (N : ℝ) :
    P12 N ((N - 3) / 2) = (N - 3) * (N - 1) / 4 *
      (9 * N ^ 3 - 55 * N ^ 2 + 48 * N - 12) := by
  simp only [P12]
  ring

theorem P12_leftFactor_pos {N : ℝ} (hN : 7 ≤ N) :
    0 < 4 * N ^ 5 - 41 * N ^ 4 + 126 * N ^ 3 - 221 * N ^ 2 + 492 * N - 324 := by
  let x := N - 7
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hNrepr : N = x + 7 := by dsimp [x]; ring
  rw [hNrepr]
  ring_nf
  positivity

theorem P12_rightFactor_pos {N : ℝ} (hN : 7 ≤ N) :
    0 < 9 * N ^ 3 - 55 * N ^ 2 + 48 * N - 12 := by
  let x := N - 7
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hNrepr : N = x + 7 := by dsimp [x]; ring
  rw [hNrepr]
  ring_nf
  positivity

/-- Complete `u/(12N)` polynomial certificate. -/
theorem P12_nonneg {N u : ℝ} (hN : 7 ≤ N) (hu2 : 2 ≤ u)
    (huN : u ≤ (N - 3) / 2) : 0 ≤ P12 N u := by
  let a := -4 * N ^ 4 + 19 * N ^ 3 - 21 * N ^ 2 + 48 * N - 36
  let b := 2 * N ^ 5 - 11 * N ^ 4 + 13 * N ^ 3 - 34 * N ^ 2 + 108 * N - 72
  let c := -3 * N ^ 4 + 24 * N ^ 3 - 69 * N ^ 2 + 84 * N - 36
  have ha : a ≤ 0 := P0_quadraticCoefficient_nonpos (by linarith)
  have hlr : (2 : ℝ) ≤ (N - 3) / 2 := by linarith
  have hleft : 0 ≤ a * (2 : ℝ) ^ 2 + b * 2 + c := by
    rw [show a * (2 : ℝ) ^ 2 + b * 2 + c = P12 N 2 by simp [a, b, c, P12]]
    rw [P12_at_two]
    exact (P12_leftFactor_pos hN).le
  have hright : 0 ≤ a * ((N - 3) / 2) ^ 2 + b * ((N - 3) / 2) + c := by
    rw [show a * ((N - 3) / 2) ^ 2 + b * ((N - 3) / 2) + c =
      P12 N ((N - 3) / 2) by simp [a, b, c, P12]]
    rw [P12_at_right]
    have hfac := P12_rightFactor_pos hN
    have hN3 : 0 ≤ N - 3 := by linarith
    have hN1 : 0 ≤ N - 1 := by linarith
    positivity
  have hquad := concaveQuadratic_nonneg ha hlr hu2 huN hleft hright
  simpa [P12, a, b, c] using hquad

/-- The polynomial `P₇(N,u)` from the stronger `u/(7N)` proxy-gap certificate. -/
def P7 (N u : ℝ) : ℝ :=
  (-28 * N ^ 4 + 133 * N ^ 3 - 147 * N ^ 2 + 336 * N - 252) * u ^ 2 +
  (4 * N ^ 5 + 3 * N ^ 4 - 139 * N ^ 3 + 42 * N ^ 2 + 636 * N - 504) * u +
  (-21 * N ^ 4 + 168 * N ^ 3 - 483 * N ^ 2 + 588 * N - 252)

theorem P7_at_two (N : ℝ) :
    P7 N 2 =
      8 * N ^ 5 - 127 * N ^ 4 + 422 * N ^ 3 - 987 * N ^ 2 + 3204 * N - 2268 := by
  simp only [P7]
  ring

theorem P7_at_right (N : ℝ) :
    P7 N (N / 7) =
      (22 * N ^ 5 - 307 * N ^ 4 + 1266 * N ^ 3 - 2781 * N ^ 2 +
        3612 * N - 1764) / 7 := by
  simp only [P7]
  ring

theorem P7_quadraticCoefficient_nonpos {N : ℝ} (hN : 15 ≤ N) :
    -28 * N ^ 4 + 133 * N ^ 3 - 147 * N ^ 2 + 336 * N - 252 ≤ 0 := by
  let x := N - 15
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hNrepr : N = x + 15 := by dsimp [x]; ring
  rw [hNrepr]
  ring_nf
  have hpos : 0 < 28 * x ^ 4 + 1547 * x ^ 3 + 31842 * x ^ 2 + 289629 * x + 982782 := by
    positivity
  nlinarith

theorem P7_leftFactor_pos {N : ℝ} (hN : 15 ≤ N) :
    0 < 8 * N ^ 5 - 127 * N ^ 4 + 422 * N ^ 3 - 987 * N ^ 2 + 3204 * N - 2268 := by
  let x := N - 15
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hNrepr : N = x + 15 := by dsimp [x]; ring
  rw [hNrepr]
  ring_nf
  positivity

theorem P7_rightFactor_pos {N : ℝ} (hN : 15 ≤ N) :
    0 < 22 * N ^ 5 - 307 * N ^ 4 + 1266 * N ^ 3 - 2781 * N ^ 2 +
      3612 * N - 1764 := by
  let x := N - 15
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hNrepr : N = x + 15 := by dsimp [x]; ring
  rw [hNrepr]
  ring_nf
  positivity

/-- Complete stronger `u/(7N)` polynomial certificate. -/
theorem P7_nonneg {N u : ℝ} (hN : 15 ≤ N) (hu2 : 2 ≤ u)
    (huN : u ≤ N / 7) : 0 ≤ P7 N u := by
  let a := -28 * N ^ 4 + 133 * N ^ 3 - 147 * N ^ 2 + 336 * N - 252
  let b := 4 * N ^ 5 + 3 * N ^ 4 - 139 * N ^ 3 + 42 * N ^ 2 + 636 * N - 504
  let c := -21 * N ^ 4 + 168 * N ^ 3 - 483 * N ^ 2 + 588 * N - 252
  have ha : a ≤ 0 := P7_quadraticCoefficient_nonpos hN
  have hlr : (2 : ℝ) ≤ N / 7 := by linarith
  have hleft : 0 ≤ a * (2 : ℝ) ^ 2 + b * 2 + c := by
    rw [show a * (2 : ℝ) ^ 2 + b * 2 + c = P7 N 2 by simp [a, b, c, P7]]
    rw [P7_at_two]
    exact (P7_leftFactor_pos hN).le
  have hright : 0 ≤ a * (N / 7) ^ 2 + b * (N / 7) + c := by
    rw [show a * (N / 7) ^ 2 + b * (N / 7) + c = P7 N (N / 7) by
      simp [a, b, c, P7]]
    rw [P7_at_right]
    exact div_nonneg (P7_rightFactor_pos hN).le (by norm_num)
  have hquad := concaveQuadratic_nonneg ha hlr hu2 huN hleft hright
  simpa [P7, a, b, c] using hquad

end SharpSerfling.Certificates
