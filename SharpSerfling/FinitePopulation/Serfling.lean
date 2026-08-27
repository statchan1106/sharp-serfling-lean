import SharpSerfling.FinitePopulation.MainTheorem

namespace SharpSerfling.FinitePopulation

open scoped BigOperators

/-- Difference between the mean of the first `n` permuted observations and
the full finite-population mean. -/
noncomputable def sampleMeanDeviation {N n : ℕ} (hn : n ≤ N)
    (X : Fin N → ℝ) (π : Equiv.Perm (Fin N)) : ℝ :=
  (∑ i : Fin n, X (π (Fin.castLE hn i))) / (n : ℝ) -
    SharpSerfling.populationMean X

theorem statistic_equalWeights {N n : ℕ} (hn0 : 0 < n) (hn : n ≤ N)
    (X : Fin N → ℝ) (π : Equiv.Perm (Fin N)) :
    statistic hn X (fun _ ↦ (1 : ℝ) / (n : ℝ)) π =
      sampleMeanDeviation hn X π := by
  unfold statistic sampleMeanDeviation
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn0)
  rw [← Finset.mul_sum]
  field_simp [hnR]

/-- MGF of the without-replacement sample-mean deviation. -/
noncomputable def sampleMeanMgf {N n : ℕ} (hn : n ≤ N)
    (X : Fin N → ℝ) (t : ℝ) : ℝ :=
  SharpSerfling.finiteAverage fun π : Equiv.Perm (Fin N) ↦
    Real.exp (t * sampleMeanDeviation hn X π)

theorem sampleMeanMgf_eq_mgf {N n : ℕ} (hn0 : 0 < n) (hn : n ≤ N)
    (X : Fin N → ℝ) (t : ℝ) :
    sampleMeanMgf hn X t =
      mgf hn X (fun _ ↦ (1 : ℝ) / (n : ℝ)) t := by
  unfold sampleMeanMgf mgf
  apply congrArg SharpSerfling.finiteAverage
  funext π
  rw [statistic_equalWeights hn0 hn]

/-- MGF part of manuscript Corollary `cor:serfling`. -/
theorem serfling_mgf {N n : ℕ} (hN : 2 ≤ N) (hn0 : 1 ≤ n)
    (hnN : n ≤ N - 1) {a b : ℝ} (X : Fin N → ℝ)
    (hX : ∀ j, a ≤ X j ∧ X j ≤ b) (t : ℝ) :
    Real.log (sampleMeanMgf (show n ≤ N by omega) X t) ≤
      SharpSerfling.kappa N * ((N : ℝ) - (n : ℝ)) /
        (8 * (n : ℝ) * ((N : ℝ) - 1)) * (b - a) ^ 2 * t ^ 2 := by
  let hn : n ≤ N := by omega
  rw [sampleMeanMgf_eq_mgf (by omega) hn]
  have hmain := weighted_mgf N n hN hn a b X hX
    (fun _ ↦ (1 : ℝ) / (n : ℝ)) t
  rw [SharpSerfling.rho_equalWeights (by omega) (by omega)] at hmain
  calc
    Real.log (mgf hn X (fun _ ↦ (1 : ℝ) / (n : ℝ)) t) ≤
        SharpSerfling.kappa N / 8 *
          (((N : ℝ) - (n : ℝ)) / ((n : ℝ) * ((N : ℝ) - 1))) *
            (b - a) ^ 2 * t ^ 2 := hmain
    _ = SharpSerfling.kappa N * ((N : ℝ) - (n : ℝ)) /
        (8 * (n : ℝ) * ((N : ℝ) - 1)) * (b - a) ^ 2 * t ^ 2 := by
      have hnR : (n : ℝ) ≠ 0 := by positivity
      have hNm1 : (N : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
        linarith
      field_simp [hnR, hNm1]

/-- Uniform finite-space probability of an upper-tail event. -/
noncomputable def uniformUpperTail {Ω : Type*} [Fintype Ω]
    (T : Ω → ℝ) (u : ℝ) : ℝ :=
  SharpSerfling.finiteAverage fun ω ↦ if u ≤ T ω then 1 else 0

/-- Finite-space exponential Markov inequality, proved directly from the
uniform sums (so no measure-theoretic assumption is hidden). -/
theorem uniformUpperTail_le_chernoff {Ω : Type*} [Fintype Ω]
    (T : Ω → ℝ) (u t : ℝ) (ht : 0 ≤ t) :
    uniformUpperTail T u ≤
      Real.exp (-t * u) *
        SharpSerfling.finiteAverage (fun ω ↦ Real.exp (t * T ω)) := by
  unfold uniformUpperTail
  calc
    SharpSerfling.finiteAverage (fun ω ↦ if u ≤ T ω then 1 else 0) ≤
        SharpSerfling.finiteAverage
          (fun ω ↦ Real.exp (-t * u) * Real.exp (t * T ω)) := by
      unfold SharpSerfling.finiteAverage
      apply div_le_div_of_nonneg_right
      · apply Finset.sum_le_sum
        intro ω hω
        by_cases htail : u ≤ T ω
        · rw [if_pos htail, ← Real.exp_add]
          apply Real.one_le_exp
          nlinarith
        · rw [if_neg htail]
          positivity
      · positivity
    _ = Real.exp (-t * u) *
        SharpSerfling.finiteAverage (fun ω ↦ Real.exp (t * T ω)) :=
      SharpSerfling.finiteAverage_smul _ _

/-- Upper-tail probability for the normalized without-replacement sample
mean used in manuscript Corollary `cor:serfling`. -/
noncomputable def sampleMeanUpperTail {N n : ℕ} (hn : n ≤ N)
    (X : Fin N → ℝ) (u : ℝ) : ℝ :=
  uniformUpperTail
    (fun π : Equiv.Perm (Fin N) ↦
      Real.sqrt (n : ℝ) * sampleMeanDeviation hn X π) u

/-- Chernoff upper-tail part of manuscript Corollary `cor:serfling`.  The
right-hand finite-population factor is `(N-n)/(N-1) = 1-f_n`. -/
theorem serfling_tail {N n : ℕ} (hN : 2 ≤ N) (hn0 : 1 ≤ n)
    (hnN : n ≤ N - 1) {a b : ℝ} (X : Fin N → ℝ)
    (hX : ∀ j, a ≤ X j ∧ X j ≤ b) {u : ℝ} (hu : 0 < u) :
    sampleMeanUpperTail (show n ≤ N by omega) X u ≤
      Real.exp (-2 * u ^ 2 /
        (SharpSerfling.kappa N *
          (((N : ℝ) - (n : ℝ)) / ((N : ℝ) - 1)) * (b - a) ^ 2)) := by
  let hn : n ≤ N := by omega
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
    have hdev (π : Equiv.Perm (Fin N)) : sampleMeanDeviation hn X π = 0 := by
      rw [← statistic_equalWeights (by omega) hn, hXconst,
        statistic_const (by omega) hn]
    unfold sampleMeanUpperTail uniformUpperTail
    simp only [hdev, mul_zero]
    dsimp [c] at hc0
    simp [not_le_of_gt hu, SharpSerfling.finiteAverage, hc0]
  have hcpos : 0 < c := by
    dsimp [c]
    apply sub_pos.mpr
    apply lt_of_le_of_ne hab
    intro heq
    apply hc0
    simp [c, heq]
  let D : ℝ := SharpSerfling.kappa N *
    (((N : ℝ) - (n : ℝ)) / ((N : ℝ) - 1)) * c ^ 2
  have hDpos : 0 < D := by
    dsimp [D]
    have hNnNat : 0 < N - n := Nat.sub_pos_of_lt (show n < N by omega)
    have hNn : (0 : ℝ) < (N : ℝ) - (n : ℝ) := by
      rw [← Nat.cast_sub (show n ≤ N by omega)]
      exact_mod_cast hNnNat
    have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
      have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
      linarith
    exact mul_pos
      (mul_pos (SharpSerfling.kappa_pos hN) (div_pos hNn hNm1))
      (sq_pos_of_pos hcpos)
  let s : ℝ := 4 * u / D
  have hs : 0 ≤ s := by
    dsimp [s]
    positivity
  have hmoment :
      SharpSerfling.finiteAverage (fun π : Equiv.Perm (Fin N) ↦
        Real.exp (s * (Real.sqrt (n : ℝ) * sampleMeanDeviation hn X π))) =
        sampleMeanMgf hn X (s * Real.sqrt (n : ℝ)) := by
    unfold sampleMeanMgf
    apply congrArg SharpSerfling.finiteAverage
    funext π
    congr 1
    ring
  have hlogMoment :
      Real.log (sampleMeanMgf hn X (s * Real.sqrt (n : ℝ))) ≤ D / 8 * s ^ 2 := by
    have hmgf := serfling_mgf hN hn0 hnN X hX (s * Real.sqrt (n : ℝ))
    calc
      Real.log (sampleMeanMgf hn X (s * Real.sqrt (n : ℝ))) ≤
          SharpSerfling.kappa N * ((N : ℝ) - (n : ℝ)) /
            (8 * (n : ℝ) * ((N : ℝ) - 1)) * (b - a) ^ 2 *
              (s * Real.sqrt (n : ℝ)) ^ 2 := hmgf
      _ = D / 8 * s ^ 2 := by
        have hnR : (n : ℝ) ≠ 0 := by positivity
        have hNm1 : (N : ℝ) - 1 ≠ 0 := by
          have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
          linarith
        rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
        dsimp [D, c]
        field_simp [hnR, hNm1]
  have hmomentLe : sampleMeanMgf hn X (s * Real.sqrt (n : ℝ)) ≤
      Real.exp (D / 8 * s ^ 2) := Real.le_exp_of_log_le hlogMoment
  calc
    sampleMeanUpperTail hn X u ≤
        Real.exp (-s * u) *
          SharpSerfling.finiteAverage (fun π : Equiv.Perm (Fin N) ↦
            Real.exp (s * (Real.sqrt (n : ℝ) * sampleMeanDeviation hn X π))) := by
      exact uniformUpperTail_le_chernoff _ u s hs
    _ = Real.exp (-s * u) * sampleMeanMgf hn X (s * Real.sqrt (n : ℝ)) := by
      rw [hmoment]
    _ ≤ Real.exp (-s * u) * Real.exp (D / 8 * s ^ 2) :=
      mul_le_mul_of_nonneg_left hmomentLe (Real.exp_nonneg _)
    _ = Real.exp (-2 * u ^ 2 /
        (SharpSerfling.kappa N *
          (((N : ℝ) - (n : ℝ)) / ((N : ℝ) - 1)) * (b - a) ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      change -s * u + D / 8 * s ^ 2 = -2 * u ^ 2 / D
      dsimp [s]
      field_simp [hDpos.ne']
      ring

/-- Lower-tail event, written as the upper tail of the negated statistic. -/
noncomputable def sampleMeanLowerTail {N n : ℕ} (hn : n ≤ N)
    (X : Fin N → ℝ) (u : ℝ) : ℝ :=
  uniformUpperTail
    (fun π : Equiv.Perm (Fin N) ↦
      -(Real.sqrt (n : ℝ) * sampleMeanDeviation hn X π)) u

theorem sampleMeanDeviation_neg {N n : ℕ} (hN : 0 < N) (hn0 : 0 < n)
    (hn : n ≤ N) (X : Fin N → ℝ) (π : Equiv.Perm (Fin N)) :
    sampleMeanDeviation hn (fun j ↦ -X j) π = -sampleMeanDeviation hn X π := by
  rw [← statistic_equalWeights hn0 hn, ← statistic_equalWeights hn0 hn]
  have h := statistic_affine hN hn X 0 (-1)
    (fun _ ↦ (1 : ℝ) / (n : ℝ)) π
  simpa using h

/-- Lower-tail half of manuscript Corollary `cor:serfling`. -/
theorem serfling_lower_tail {N n : ℕ} (hN : 2 ≤ N) (hn0 : 1 ≤ n)
    (hnN : n ≤ N - 1) {a b : ℝ} (X : Fin N → ℝ)
    (hX : ∀ j, a ≤ X j ∧ X j ≤ b) {u : ℝ} (hu : 0 < u) :
    sampleMeanLowerTail (show n ≤ N by omega) X u ≤
      Real.exp (-2 * u ^ 2 /
        (SharpSerfling.kappa N *
          (((N : ℝ) - (n : ℝ)) / ((N : ℝ) - 1)) * (b - a) ^ 2)) := by
  let hn : n ≤ N := by omega
  let Xneg : Fin N → ℝ := fun j ↦ -X j
  have hXneg : ∀ j, -b ≤ Xneg j ∧ Xneg j ≤ -a := by
    intro j
    dsimp [Xneg]
    constructor <;> linarith [(hX j).1, (hX j).2]
  have htailEq : sampleMeanLowerTail hn X u = sampleMeanUpperTail hn Xneg u := by
    unfold sampleMeanLowerTail sampleMeanUpperTail
    congr 1
    funext π
    rw [sampleMeanDeviation_neg (by omega) (by omega) hn]
    ring
  rw [htailEq]
  convert serfling_tail hN hn0 hnN Xneg hXneg hu using 1 <;> ring

/-- Uniform probability of the absolute-value tail event. -/
noncomputable def uniformTwoSidedTail {Ω : Type*} [Fintype Ω]
    (T : Ω → ℝ) (u : ℝ) : ℝ :=
  SharpSerfling.finiteAverage fun ω ↦ if u ≤ |T ω| then 1 else 0

theorem finiteAverage_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (hfg : ∀ ω, f ω ≤ g ω) :
    SharpSerfling.finiteAverage f ≤ SharpSerfling.finiteAverage g := by
  unfold SharpSerfling.finiteAverage
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun ω hω ↦ hfg ω
  · positivity

theorem uniformTwoSidedTail_le_add {Ω : Type*} [Fintype Ω]
    (T : Ω → ℝ) (u : ℝ) :
    uniformTwoSidedTail T u ≤
      uniformUpperTail T u + uniformUpperTail (fun ω ↦ -T ω) u := by
  unfold uniformTwoSidedTail uniformUpperTail
  rw [← SharpSerfling.finiteAverage_add]
  apply finiteAverage_mono
  intro ω
  by_cases htail : u ≤ |T ω|
  · rw [if_pos htail]
    rcases le_total 0 (T ω) with hpos | hneg
    · have huT : u ≤ T ω := by simpa [abs_of_nonneg hpos] using htail
      by_cases hother : u ≤ -T ω <;> simp [huT, hother]
    · have huT : u ≤ -T ω := by simpa [abs_of_nonpos hneg] using htail
      by_cases hother : u ≤ T ω <;> simp [huT, hother]
  · rw [if_neg htail]
    positivity

noncomputable def sampleMeanTwoSidedTail {N n : ℕ} (hn : n ≤ N)
    (X : Fin N → ℝ) (u : ℝ) : ℝ :=
  uniformTwoSidedTail
    (fun π : Equiv.Perm (Fin N) ↦
      Real.sqrt (n : ℝ) * sampleMeanDeviation hn X π) u

/-- Two-sided conclusion of manuscript Corollary `cor:serfling`. -/
theorem serfling_twoSided_tail {N n : ℕ} (hN : 2 ≤ N) (hn0 : 1 ≤ n)
    (hnN : n ≤ N - 1) {a b : ℝ} (X : Fin N → ℝ)
    (hX : ∀ j, a ≤ X j ∧ X j ≤ b) {u : ℝ} (hu : 0 < u) :
    sampleMeanTwoSidedTail (show n ≤ N by omega) X u ≤
      2 * Real.exp (-2 * u ^ 2 /
        (SharpSerfling.kappa N *
          (((N : ℝ) - (n : ℝ)) / ((N : ℝ) - 1)) * (b - a) ^ 2)) := by
  let hn : n ≤ N := by omega
  let T : Equiv.Perm (Fin N) → ℝ := fun π ↦
    Real.sqrt (n : ℝ) * sampleMeanDeviation hn X π
  have hsplit := uniformTwoSidedTail_le_add T u
  have hupp := serfling_tail hN hn0 hnN X hX hu
  have hlow := serfling_lower_tail hN hn0 hnN X hX hu
  change uniformTwoSidedTail T u ≤ _
  calc
    uniformTwoSidedTail T u ≤
        uniformUpperTail T u + uniformUpperTail (fun π ↦ -T π) u := hsplit
    _ ≤ Real.exp (-2 * u ^ 2 /
          (SharpSerfling.kappa N *
            (((N : ℝ) - (n : ℝ)) / ((N : ℝ) - 1)) * (b - a) ^ 2)) +
        Real.exp (-2 * u ^ 2 /
          (SharpSerfling.kappa N *
            (((N : ℝ) - (n : ℝ)) / ((N : ℝ) - 1)) * (b - a) ^ 2)) :=
      add_le_add hupp hlow
    _ = _ := by ring

end SharpSerfling.FinitePopulation
