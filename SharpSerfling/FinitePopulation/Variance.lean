import SharpSerfling.FinitePopulation.Exchangeable
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

namespace SharpSerfling

open scoped BigOperators

/-- Variance on an explicitly uniform finite probability space. -/
noncomputable def finiteVariance {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  finiteAverage (fun ω ↦ (f ω - finiteAverage f) ^ 2)

/-- Uniform finite averaging commutes with a finite sum. -/
theorem finiteAverage_finsetSum {Ω ι : Type*} [Fintype Ω]
    (s : Finset ι) (f : ι → Ω → ℝ) :
    finiteAverage (fun ω ↦ ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, finiteAverage (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteAverage_zero]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [finiteAverage_add, ih]

theorem finiteAverage_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (f : ι → Ω → ℝ) :
    finiteAverage (fun ω ↦ ∑ i, f i ω) = ∑ i, finiteAverage (f i) := by
  simpa using finiteAverage_finsetSum (Finset.univ : Finset ι) f

end SharpSerfling

namespace SharpSerfling.FinitePopulation

open scoped BigOperators

/-- The ordered pair `(i,j)`, regarded as an embedding of `Fin 2`. -/
def pairEmbedding {N : ℕ} (i j : Fin N) (hij : i ≠ j) : Fin 2 ↪ Fin N where
  toFun k := if (k : ℕ) = 0 then i else j
  inj' := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all

@[simp] theorem pairEmbedding_zero {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    pairEmbedding i j hij 0 = i := by simp [pairEmbedding]

@[simp] theorem pairEmbedding_one {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    pairEmbedding i j hij 1 = j := by simp [pairEmbedding]

/-- A single coordinate of a uniformly permuted vector is uniformly
distributed over all population coordinates. -/
theorem finiteAverage_perm_apply {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℝ) (i : Fin N) :
    SharpSerfling.finiteAverage
        (fun π : Equiv.Perm (Fin N) ↦ z (π i)) =
      SharpSerfling.finiteAverage z := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  simpa using
    (SharpSerfling.finiteAverage_orbit_eq
      (G := Equiv.Perm (Fin N)) (X := Fin N) i z)

/-- The joint uniform-permutation average at two distinct positions is
independent of the chosen ordered pair. -/
theorem finiteAverage_perm_pair_eq {N : ℕ} (hN : 2 ≤ N)
    (z : Fin N → ℝ) {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l) :
    SharpSerfling.finiteAverage
        (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π j)) =
      SharpSerfling.finiteAverage
        (fun π : Equiv.Perm (Fin N) ↦ z (π k) * z (π l)) := by
  let eij := pairEmbedding i j hij
  let ekl := pairEmbedding k l hkl
  letI : Nonempty (Fin 2 ↪ Fin N) := ⟨eij⟩
  letI : MulAction.IsPretransitive (Equiv.Perm (Fin N)) (Fin 2 ↪ Fin N) :=
    Equiv.Perm.isMultiplyPretransitive (Fin N) 2
  let f : (Fin 2 ↪ Fin N) → ℝ := fun e ↦ z (e 0) * z (e 1)
  have hi := SharpSerfling.finiteAverage_orbit_eq
    (G := Equiv.Perm (Fin N)) (X := Fin 2 ↪ Fin N) eij f
  have hk := SharpSerfling.finiteAverage_orbit_eq
    (G := Equiv.Perm (Fin N)) (X := Fin 2 ↪ Fin N) ekl f
  simpa [eij, ekl, f, Function.Embedding.smul_apply] using hi.trans hk.symm

/-- The second moment at one position of a uniformly permuted vector. -/
theorem finiteAverage_perm_sq {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℝ) (i : Fin N) :
    SharpSerfling.finiteAverage
        (fun π : Equiv.Perm (Fin N) ↦ (z (π i)) ^ 2) =
      (∑ j, (z j) ^ 2) / (N : ℝ) := by
  have h := finiteAverage_perm_apply hN (fun j ↦ (z j) ^ 2) i
  simpa [SharpSerfling.finiteAverage] using h

/-- Distinct coordinates of a centered vector sampled by a uniform
permutation have covariance `-‖z‖²/(N(N-1))`. -/
theorem finiteAverage_perm_mul_of_ne {N : ℕ} (hN : 2 ≤ N)
    (z : Fin N → ℝ) (hz : ∑ j, z j = 0)
    {i j : Fin N} (hij : i ≠ j) :
    SharpSerfling.finiteAverage
        (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π j)) =
      -(∑ k, (z k) ^ 2) / ((N : ℝ) * ((N : ℝ) - 1)) := by
  classical
  obtain ⟨j₀, hj₀⟩ := Fintype.exists_ne_of_one_lt_card
    (α := Fin N) (by simpa using (show 1 < N by omega)) i
  let B : ℝ := SharpSerfling.finiteAverage
    (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π j₀))
  have htargetB :
      SharpSerfling.finiteAverage
          (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π j)) = B := by
    exact finiteAverage_perm_pair_eq hN z hij hj₀.symm
  have hsumzero :
      (∑ r : Fin N, SharpSerfling.finiteAverage
        (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π r))) = 0 := by
    rw [← SharpSerfling.finiteAverage_sum]
    have hfun :
        (fun π : Equiv.Perm (Fin N) ↦ ∑ r : Fin N, z (π i) * z (π r)) =
          fun _ ↦ 0 := by
      funext π
      rw [← Finset.mul_sum, Equiv.sum_comp π z, hz, mul_zero]
    rw [hfun, SharpSerfling.finiteAverage_zero]
  have hcross (r : Fin N) (hr : r ∈ (Finset.univ.erase i)) :
      SharpSerfling.finiteAverage
          (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π r)) = B := by
    have hir : i ≠ r := by
      exact fun hir ↦ (Finset.mem_erase.mp hr).1 hir.symm
    exact finiteAverage_perm_pair_eq hN z hir hj₀.symm
  have hdiag :
      SharpSerfling.finiteAverage
          (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π i)) =
        (∑ k, (z k) ^ 2) / (N : ℝ) := by
    simpa [pow_two] using finiteAverage_perm_sq (by omega) z i
  have hrelation :
      ((N : ℝ) - 1) * B + (∑ k, (z k) ^ 2) / (N : ℝ) = 0 := by
    have hsplit :
        (∑ r : Fin N, SharpSerfling.finiteAverage
          (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π r))) =
          (∑ r ∈ (Finset.univ.erase i), SharpSerfling.finiteAverage
            (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π r))) +
          SharpSerfling.finiteAverage
            (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π i)) := by
      exact (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)).symm
    rw [hsplit, hdiag] at hsumzero
    have hcrosssum :
        (∑ r ∈ (Finset.univ.erase i), SharpSerfling.finiteAverage
          (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π r))) =
          ((N : ℝ) - 1) * B := by
      rw [Finset.sum_congr rfl fun r hr ↦ hcross r hr]
      simp only [Finset.sum_const, Finset.card_erase_of_mem, Finset.mem_univ,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    rw [hcrosssum] at hsumzero
    exact hsumzero
  rw [htargetB]
  have hNR : (N : ℝ) ≠ 0 := by positivity
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  field_simp [hNR, hNm1] at hrelation ⊢
  linarith

/-- Exact second moment of a centered weighted dot product under a uniform
permutation.  This is the finite-population covariance calculation behind
the manuscript's variance identity. -/
theorem finiteAverage_perm_centered_dot_sq {N : ℕ} (hN : 2 ≤ N)
    (y z : Fin N → ℝ) (hy : ∑ i, y i = 0) (hz : ∑ j, z j = 0) :
    SharpSerfling.finiteAverage
        (fun π : Equiv.Perm (Fin N) ↦ (∑ i, y i * z (π i)) ^ 2) =
      (∑ i, (y i) ^ 2) * (∑ j, (z j) ^ 2) / ((N : ℝ) - 1) := by
  classical
  let A : ℝ := (∑ j, (z j) ^ 2) / (N : ℝ)
  let B : ℝ := -(∑ j, (z j) ^ 2) / ((N : ℝ) * ((N : ℝ) - 1))
  have hdiag (i : Fin N) :
      SharpSerfling.finiteAverage
          (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π i)) = A := by
    simpa [A, pow_two] using finiteAverage_perm_sq (by omega) z i
  have hcross (i j : Fin N) (hij : i ≠ j) :
      SharpSerfling.finiteAverage
          (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π j)) = B := by
    simpa [B] using finiteAverage_perm_mul_of_ne hN z hz hij
  have hyerase (i : Fin N) : ∑ j ∈ Finset.univ.erase i, y j = -y i := by
    have hs := Finset.sum_erase_add Finset.univ y (Finset.mem_univ i)
    rw [hy] at hs
    linarith
  have hsquare (π : Equiv.Perm (Fin N)) :
      (∑ i, y i * z (π i)) ^ 2 =
        ∑ i, ((y i) ^ 2 * (z (π i) * z (π i)) +
          ∑ j ∈ Finset.univ.erase i,
            (y i * y j) * (z (π i) * z (π j))) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun j ↦ (y i * z (π i)) * (y j * z (π j))) (Finset.mem_univ i)
    rw [← hsplit]
    calc
      _ = (y i * z (π i)) * (y i * z (π i)) +
          ∑ j ∈ Finset.univ.erase i,
            (y i * z (π i)) * (y j * z (π j)) := add_comm _ _
      _ = _ := by
        apply congrArg₂ (.+.)
        · ring
        · apply Finset.sum_congr rfl
          intro j hj
          ring
  rw [show (fun π : Equiv.Perm (Fin N) ↦ (∑ i, y i * z (π i)) ^ 2) =
      fun π ↦ ∑ i, ((y i) ^ 2 * (z (π i) * z (π i)) +
        ∑ j ∈ Finset.univ.erase i,
          (y i * y j) * (z (π i) * z (π j))) by
        funext π
        exact hsquare π]
  rw [SharpSerfling.finiteAverage_sum]
  simp_rw [SharpSerfling.finiteAverage_add,
    SharpSerfling.finiteAverage_finsetSum,
    SharpSerfling.finiteAverage_smul]
  have havg (i : Fin N) :
      (y i) ^ 2 *
          SharpSerfling.finiteAverage
            (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π i)) +
        ∑ j ∈ Finset.univ.erase i,
          (y i * y j) *
            SharpSerfling.finiteAverage
              (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π j)) =
        (y i) ^ 2 * (A - B) := by
    rw [hdiag]
    have hoff :
        (∑ j ∈ Finset.univ.erase i,
          (y i * y j) *
            SharpSerfling.finiteAverage
              (fun π : Equiv.Perm (Fin N) ↦ z (π i) * z (π j))) =
          -(y i) ^ 2 * B := by
      calc
        _ = ∑ j ∈ Finset.univ.erase i, (y i * y j) * B := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hcross i j (by exact fun h ↦ (Finset.mem_erase.mp hj).1 h.symm)]
        _ = (∑ j ∈ Finset.univ.erase i, y i * y j) * B := by
          rw [Finset.sum_mul]
        _ = y i * (∑ j ∈ Finset.univ.erase i, y j) * B := by
          congr 1
          rw [Finset.mul_sum]
        _ = -(y i) ^ 2 * B := by rw [hyerase]; ring
    rw [hoff]
    ring
  rw [Finset.sum_congr rfl fun i hi ↦ havg i]
  rw [← Finset.sum_mul]
  have hNR : (N : ℝ) ≠ 0 := by positivity
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  dsimp [A, B]
  field_simp [hNR, hNm1]
  ring

/-- The manuscript's finite-population variance, written as a uniform
finite average of squared centered population values. -/
noncomputable def populationVariance {N : ℕ} (X : Fin N → ℝ) : ℝ :=
  SharpSerfling.finiteAverage
    (fun j ↦ (X j - SharpSerfling.populationMean X) ^ 2)

/-- The centered population sums to zero. -/
theorem sum_centeredPopulation {N : ℕ} (hN : 0 < N) (X : Fin N → ℝ) :
    ∑ j, (X j - SharpSerfling.populationMean X) = 0 := by
  unfold SharpSerfling.populationMean
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNR : (N : ℝ) ≠ 0 := by positivity
  field_simp [hNR]
  ring

/-- Conversion between the manuscript's population variance and its
unnormalized centered sum of squares. -/
theorem sum_sq_centeredPopulation {N : ℕ} (hN : 0 < N) (X : Fin N → ℝ) :
    ∑ j, (X j - SharpSerfling.populationMean X) ^ 2 =
      (N : ℝ) * populationVariance X := by
  unfold populationVariance SharpSerfling.finiteAverage
  simp only [Fintype.card_fin]
  have hNR : (N : ℝ) ≠ 0 := by positivity
  field_simp [hNR]

/-- The uniformly permuted weighted statistic is centered. -/
theorem finiteAverage_statistic_eq_zero {N n : ℕ} (hN : 0 < N)
    (hn : n ≤ N) (X : Fin N → ℝ) (w : Fin n → ℝ) :
    SharpSerfling.finiteAverage
        (FinitePopulation.statistic hn X w) = 0 := by
  have hstat :
      FinitePopulation.statistic hn X w =
        fun π : Equiv.Perm (Fin N) ↦
          ∑ j, centeredWeight hn w j * X (π j) := by
    funext π
    exact statistic_eq_centeredWeight_dot hN hn X w π
  rw [hstat, SharpSerfling.finiteAverage_sum]
  simp_rw [SharpSerfling.finiteAverage_smul, finiteAverage_perm_apply hN X]
  rw [← Finset.sum_mul, sum_centeredWeight hN hn, zero_mul]

/-- Equation (2) of the manuscript: under uniform sampling without
replacement, the actual variance of the weighted centered statistic is
exactly `rho_N(w) * sigma_N²`. -/
theorem statistic_variance_eq_rho_mul_populationVariance {N n : ℕ}
    (hN : 2 ≤ N) (hn : n ≤ N) (X : Fin N → ℝ) (w : Fin n → ℝ) :
    SharpSerfling.finiteVariance (FinitePopulation.statistic hn X w) =
      SharpSerfling.rho N n w * populationVariance X := by
  let y : Fin N → ℝ := centeredWeight hn w
  let z : Fin N → ℝ := fun j ↦ X j - SharpSerfling.populationMean X
  have hy : ∑ j, y j = 0 := sum_centeredWeight (by omega) hn w
  have hz : ∑ j, z j = 0 := sum_centeredPopulation (by omega) X
  have hstat (π : Equiv.Perm (Fin N)) :
      FinitePopulation.statistic hn X w π = ∑ j, y j * z (π j) := by
    rw [statistic_eq_centeredWeight_dot (by omega) hn]
    dsimp [y, z]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    have hsumperm :
        ∑ j, centeredWeight hn w j * SharpSerfling.populationMean X = 0 := by
      rw [← Finset.sum_mul, sum_centeredWeight (by omega) hn, zero_mul]
    rw [hsumperm, sub_zero]
  unfold SharpSerfling.finiteVariance
  rw [finiteAverage_statistic_eq_zero (by omega) hn X w]
  simp only [sub_zero]
  rw [show (fun π : Equiv.Perm (Fin N) ↦
      (FinitePopulation.statistic hn X w π) ^ 2) =
      fun π ↦ (∑ j, y j * z (π j)) ^ 2 by
        funext π
        rw [hstat]]
  rw [finiteAverage_perm_centered_dot_sq hN y z hy hz]
  rw [show (∑ j, (y j) ^ 2) =
      ((N : ℝ) - 1) / (N : ℝ) * SharpSerfling.rho N n w by
        simpa [y] using sum_sq_centeredWeight_eq_rho hN hn w]
  rw [show (∑ j, (z j) ^ 2) = (N : ℝ) * populationVariance X by
        simpa [z] using sum_sq_centeredPopulation (by omega) X]
  have hNR : (N : ℝ) ≠ 0 := by positivity
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  field_simp [hNR, hNm1]

/-- The variance scale vanishes exactly for a constant zero-padded weight
vector (equivalently, for a zero centered-weight vector). -/
theorem rho_eq_zero_iff_centeredWeight_eq_zero {N n : ℕ}
    (hN : 2 ≤ N) (hn : n ≤ N) (w : Fin n → ℝ) :
    SharpSerfling.rho N n w = 0 ↔ centeredWeight hn w = 0 := by
  have hnorm := sum_sq_centeredWeight_eq_rho hN hn w
  have hcoef : ((N : ℝ) - 1) / (N : ℝ) ≠ 0 := by
    have hNR : (N : ℝ) ≠ 0 := by positivity
    have hNm1 : (N : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
      linarith
    exact div_ne_zero hNm1 hNR
  constructor
  · intro hrho
    rw [hrho, mul_zero] at hnorm
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) ↦ sq_nonneg (centeredWeight hn w j))).mp
        hnorm i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  · intro hw
    have hsumzero : ∑ j, (centeredWeight hn w j) ^ 2 = 0 := by simp [hw]
    rw [hsumzero] at hnorm
    exact (mul_eq_zero.mp hnorm.symm).resolve_left hcoef

end SharpSerfling.FinitePopulation
