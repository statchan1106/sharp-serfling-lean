import SharpSerfling.FinitePopulation.BinaryReduction
import SharpSerfling.Hypergeometric.Sharpness
import SharpSerfling.Hypergeometric.ParameterSwap

namespace SharpSerfling.FinitePopulation

open scoped BigOperators

open SharpSerfling.Hypergeometric

/-- Exponential subset average on the `K`th Hamming slice. -/
noncomputable def sliceMgf (N K : ℕ) (y : Fin N → ℝ) : ℝ :=
  SharpSerfling.finiteAverage fun s : Sample N K ↦
    Real.exp (∑ i ∈ s.1, y i)

/-- Logarithmic exponential subset average used in the two-level variational
problem. -/
noncomputable def sliceLogMgf (N K : ℕ) (y : Fin N → ℝ) : ℝ :=
  Real.log (sliceMgf N K y)

/-- Canonical centered vector with a first level of multiplicity `m`, written
in terms of the signed difference `d` between its two levels. -/
noncomputable def canonicalTwoLevel (N m : ℕ) (d : ℝ) (i : Fin N) : ℝ :=
  if i ∈ marked N m then
    (((N : ℝ) - (m : ℝ)) / (N : ℝ)) * d
  else
    (-(m : ℝ) / (N : ℝ)) * d

theorem sum_canonicalTwoLevel {N m : ℕ} (hN : 0 < N) (hm : m ≤ N) (d : ℝ) :
    ∑ i, canonicalTwoLevel N m d i = 0 := by
  classical
  unfold canonicalTwoLevel
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hfilterMarked :
      (Finset.univ : Finset (Fin N)).filter (fun i ↦ i ∈ marked N m) = marked N m := by
    ext i
    simp
  rw [hfilterMarked, card_marked hm]
  have hfilterNot :
      ((Finset.univ : Finset (Fin N)).filter fun i ↦ i ∉ marked N m).card = N - m := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin N))) (fun i ↦ i ∈ marked N m)
    rw [hfilterMarked, card_marked hm, Finset.card_univ, Fintype.card_fin] at hpart
    omega
  rw [hfilterNot]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [Nat.cast_sub hm]
  push_cast
  field_simp [hNR]
  ring

theorem sum_sq_canonicalTwoLevel {N m : ℕ} (hN : 0 < N) (hm : m ≤ N) (d : ℝ) :
    ∑ i, (canonicalTwoLevel N m d i) ^ 2 =
      (m : ℝ) * ((N : ℝ) - (m : ℝ)) / (N : ℝ) * d ^ 2 := by
  classical
  unfold canonicalTwoLevel
  simp_rw [ite_pow]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hfilterMarked :
      (Finset.univ : Finset (Fin N)).filter (fun i ↦ i ∈ marked N m) = marked N m := by
    ext i
    simp
  rw [hfilterMarked, card_marked hm]
  have hfilterNot :
      ((Finset.univ : Finset (Fin N)).filter fun i ↦ i ∉ marked N m).card = N - m := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin N))) (fun i ↦ i ∈ marked N m)
    rw [hfilterMarked, card_marked hm, Finset.card_univ, Fintype.card_fin] at hpart
    omega
  rw [hfilterNot]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [Nat.cast_sub hm]
  push_cast
  field_simp [hNR]
  ring

theorem subsetSum_canonicalTwoLevel {N K m : ℕ} (hN : 0 < N) (hm : m ≤ N)
    (d : ℝ) (s : Sample N K) :
    (∑ i ∈ s.1, canonicalTwoLevel N m d i) =
      d * ((count m s : ℕ) - center N m K) := by
  classical
  unfold canonicalTwoLevel
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hmarked : (s.1.filter fun i ↦ i ∈ marked N m).card = count m s := by
    change (s.1.filter fun i ↦ i ∈ marked N m).card = (s.1 ∩ marked N m).card
    congr 1
  rw [hmarked]
  have hnotMarked : (s.1.filter fun i ↦ i ∉ marked N m).card = K - count m s := by
    have hpartition :
        (s.1.filter fun i ↦ i ∈ marked N m).card +
          (s.1.filter fun i ↦ i ∉ marked N m).card = s.1.card := by
      simpa only [not_not] using
        (Finset.card_filter_add_card_filter_not
          (s := s.1) (fun i ↦ i ∈ marked N m))
    rw [s.property] at hpartition
    omega
  rw [hnotMarked]
  unfold center
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hcount : count m s ≤ K := count_le_sample s
  rw [Nat.cast_sub hcount]
  push_cast
  field_simp [hNR]
  ring

/-- A canonical two-level slice MGF is exactly a centered hypergeometric MGF. -/
theorem sliceMgf_canonicalTwoLevel {N K m : ℕ} (hN : 0 < N) (hm : m ≤ N)
    (d : ℝ) :
    sliceMgf N K (canonicalTwoLevel N m d) =
      Hypergeometric.mgf N m K d := by
  unfold sliceMgf Hypergeometric.mgf
  apply congrArg (fun z : ℝ ↦ z / Fintype.card (Sample N K))
  apply Finset.sum_congr rfl
  intro s _
  change Real.exp (∑ i ∈ s.1, canonicalTwoLevel N m d i) =
    Real.exp (d * ((count m s : ℕ) - center N m K))
  rw [subsetSum_canonicalTwoLevel hN hm]

/-- The sharp hypergeometric theorem gives the desired norm-scaled bound for
every canonical two-level vector. -/
theorem sliceLogMgf_canonicalTwoLevel_le {N K m : ℕ} (hN : 2 ≤ N)
    (hK : K ≤ N) (hm0 : 1 ≤ m) (hmN : m ≤ N - 1) (d : ℝ) :
    sliceLogMgf N K (canonicalTwoLevel N m d) ≤
      SharpSerfling.kappa N * (N : ℝ) / (8 * ((N : ℝ) - 1)) *
        (∑ i, (canonicalTwoLevel N m d i) ^ 2) := by
  have hm : m ≤ N := by omega
  rw [sliceLogMgf, sliceMgf_canonicalTwoLevel (by omega) hm,
    Hypergeometric.mgf_parameterSwap hm hK]
  have hsharp := Hypergeometric.sharp_mgf hN hK hm d
  rw [sum_sq_canonicalTwoLevel (by omega) hm]
  unfold SharpSerfling.hypergeomScale at hsharp
  calc
    Real.log (Hypergeometric.mgf N K m d) ≤
        SharpSerfling.kappa N *
          ((m : ℝ) * ((N : ℝ) - (m : ℝ)) / (8 * ((N : ℝ) - 1))) * d ^ 2 :=
      hsharp
    _ = SharpSerfling.kappa N * (N : ℝ) / (8 * ((N : ℝ) - 1)) *
        ((m : ℝ) * ((N : ℝ) - (m : ℝ)) / (N : ℝ) * d ^ 2) := by
      have hNR : (N : ℝ) ≠ 0 := by positivity
      field_simp [hNR]

end SharpSerfling.FinitePopulation
