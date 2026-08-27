import SharpSerfling.FinitePopulation.BinarySlice
import SharpSerfling.FinitePopulation.TwoLevelBound

namespace SharpSerfling.FinitePopulation

open scoped BigOperators

/-- Centering makes the weighted permutation statistic vanish on constant
populations. -/
theorem statistic_const {N n : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (a : ℝ) (w : Fin n → ℝ) (π : Equiv.Perm (Fin N)) :
    statistic hn (fun _ ↦ a) w π = 0 := by
  have hmean : SharpSerfling.populationMean (fun _ : Fin N ↦ a) = a := by
    unfold SharpSerfling.populationMean
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp [hNR]
  unfold statistic
  rw [hmean]
  simp

/-- Exact affine equivariance of the centered statistic. -/
theorem statistic_affine {N n : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (X : Fin N → ℝ) (a c : ℝ) (w : Fin n → ℝ)
    (π : Equiv.Perm (Fin N)) :
    statistic hn (fun j ↦ a + c * X j) w π = c * statistic hn X w π := by
  let A : Fin N → ℝ := fun _ ↦ a
  have hfun : (fun j : Fin N ↦ a + c * X j) = A + c • X := by
    funext j
    simp [A, smul_eq_mul]
  change statisticLinear hn w π (fun j ↦ a + c * X j) = _
  rw [hfun, map_add, map_smul]
  change statistic hn A w π + c * statistic hn X w π = _
  rw [show statistic hn A w π = 0 by simpa [A] using statistic_const hN hn a w π]
  ring

/-- Affine rescaling of a population is exactly absorbed into the MGF tilt. -/
theorem mgf_affine {N n : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (X : Fin N → ℝ) (a c : ℝ) (w : Fin n → ℝ) (t : ℝ) :
    mgf hn (fun j ↦ a + c * X j) w t = mgf hn X w (c * t) := by
  unfold mgf
  apply congrArg SharpSerfling.finiteAverage
  funext π
  rw [statistic_affine hN hn]
  congr 1
  ring

theorem mgf_const {N n : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (a : ℝ) (w : Fin n → ℝ) (t : ℝ) :
    mgf hn (fun _ ↦ a) w t = 1 := by
  unfold mgf
  rw [show (fun π : Equiv.Perm (Fin N) ↦
      Real.exp (t * statistic hn (fun _ ↦ a) w π)) = fun _ ↦ 1 by
    funext π
    rw [statistic_const hN hn]
    simp]
  exact SharpSerfling.finiteAverage_one

/-- The manuscript's main finite-population MGF theorem.  This is the exact
statement packaged as `WeightedMGFStatement` in `Definitions.lean`. -/
theorem weighted_mgf : WeightedMGFStatement := by
  intro N n hN hn a b X hX w t
  let c : ℝ := b - a
  have hab : a ≤ b := by
    let j₀ : Fin N := ⟨0, by omega⟩
    exact (hX j₀).1.trans (hX j₀).2
  by_cases hc0 : c = 0
  · have habEq : a = b := by dsimp [c] at hc0; linarith
    have hXconst : X = fun _ ↦ a := by
      funext j
      have hj := hX j
      rw [← habEq] at hj
      linarith
    rw [hXconst, mgf_const (by omega) hn]
    simp [c] at hc0
    simp [hc0]
  have habne : a ≠ b := by
    intro heq
    apply hc0
    simp [c, heq]
  have hcpos : 0 < c := by
    dsimp [c]
    exact sub_pos.mpr (lt_of_le_of_ne hab habne)
  let Z : Fin N → ℝ := fun j ↦ (X j - a) / c
  have hZ : ∀ j, 0 ≤ Z j ∧ Z j ≤ 1 := by
    intro j
    dsimp [Z]
    constructor
    · exact div_nonneg (sub_nonneg.mpr (hX j).1) hcpos.le
    · rw [div_le_one hcpos]
      dsimp [c]
      linarith [(hX j).2]
  have hXZ : X = fun j ↦ a + c * Z j := by
    funext j
    dsimp [Z]
    field_simp [hc0]
    ring
  obtain ⟨v, hv, hle⟩ := binaryReduction hn w (c * t) Z hZ
  have hmgfXZ : mgf hn X w t = mgf hn Z w (c * t) := by
    rw [hXZ, mgf_affine (by omega) hn]
  have hlogBinary : Real.log (mgf hn X w t) ≤ Real.log (mgf hn v w (c * t)) := by
    rw [hmgfXZ]
    exact Real.log_le_log (mgf_pos hn Z w (c * t)) hle
  let y : Fin N → ℝ := fun j ↦ (c * t) * centeredWeight hn w j
  have hycenter : ∑ j, y j = 0 := by
    dsimp [y]
    rw [← Finset.mul_sum, sum_centeredWeight (by omega) hn]
    ring
  have hslice := sliceLogMgf_le hN (successCount_le v) hycenter
  have hbinaryBound : Real.log (mgf hn v w (c * t)) ≤
      SharpSerfling.kappa N * (N : ℝ) / (8 * ((N : ℝ) - 1)) * sqNorm y := by
    rw [mgf_binary_eq_sliceMgf (by omega) hn v hv w (c * t)]
    exact hslice
  have hynorm : sqNorm y =
      (c * t) ^ 2 * (((N : ℝ) - 1) / (N : ℝ) * SharpSerfling.rho N n w) := by
    unfold sqNorm
    dsimp [y]
    rw [show (∑ j, ((c * t) * centeredWeight hn w j) ^ 2) =
        (c * t) ^ 2 * ∑ j, (centeredWeight hn w j) ^ 2 by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring]
    rw [sum_sq_centeredWeight_eq_rho hN hn]
  calc
    Real.log (mgf hn X w t) ≤ Real.log (mgf hn v w (c * t)) := hlogBinary
    _ ≤ SharpSerfling.kappa N * (N : ℝ) / (8 * ((N : ℝ) - 1)) * sqNorm y :=
      hbinaryBound
    _ = SharpSerfling.kappa N / 8 * SharpSerfling.rho N n w *
        (b - a) ^ 2 * t ^ 2 := by
      rw [hynorm]
      dsimp [c]
      have hNR : (N : ℝ) ≠ 0 := by positivity
      have hNm1 : (N : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
        linarith
      field_simp [hNR, hNm1]

/-- Traceability alias for manuscript Theorem `thm:finite-population`. -/
theorem finitePopulation_mgf : WeightedMGFStatement := weighted_mgf

end SharpSerfling.FinitePopulation
