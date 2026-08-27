import SharpSerfling.FinitePopulation.Exchangeable
import SharpSerfling.Hypergeometric.SmallTilt

namespace SharpSerfling.FinitePopulation

open scoped BigOperators
open SharpSerfling.Hypergeometric
open MeasureTheory
open Filter Topology

/-- Binary vector marking the first `K` coordinates. -/
noncomputable def markedIndicator (N K : ℕ) (j : Fin N) : ℝ :=
  if j ∈ marked N K then 1 else 0

theorem markedIndicator_binary (N K : ℕ) (j : Fin N) :
    markedIndicator N K j = 0 ∨ markedIndicator N K j = 1 := by
  unfold markedIndicator
  split_ifs <;> simp

theorem successSet_markedIndicator (N K : ℕ) :
    successSet (markedIndicator N K) = marked N K := by
  ext j
  simp [markedIndicator]

theorem successCount_markedIndicator {N K : ℕ} (hK : K ≤ N) :
    successCount (markedIndicator N K) = K := by
  unfold successCount
  rw [successSet_markedIndicator, card_marked hK]

theorem sum_markedIndicator {N K : ℕ} (hK : K ≤ N) :
    ∑ j, markedIndicator N K j = K := by
  rw [sum_binary_eq_successCount (markedIndicator N K) (markedIndicator_binary N K),
    successCount_markedIndicator hK]

theorem centeredWeight_markedIndicator {N m : ℕ} (hN : 0 < N)
    (hm : m ≤ N) :
    centeredWeight (show N ≤ N by rfl) (markedIndicator N m) =
      canonicalTwoLevel N m 1 := by
  funext j
  unfold centeredWeight canonicalTwoLevel
  have hzeroPad : zeroPad (show N ≤ N by rfl) (markedIndicator N m) j =
      markedIndicator N m j := by
    simpa using zeroPad_castLE (show N ≤ N by rfl) (markedIndicator N m) j
  rw [hzeroPad, sum_markedIndicator hm]
  unfold markedIndicator
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  by_cases hj : j ∈ marked N m
  · simp [hj]
    field_simp [hNR]
  · simp [hj]
    ring

theorem mul_canonicalTwoLevel_one {N m : ℕ} (t : ℝ) :
    (fun j ↦ t * canonicalTwoLevel N m 1 j) = canonicalTwoLevel N m t := by
  funext j
  unfold canonicalTwoLevel
  split_ifs <;> ring

/-- The hypergeometric family occurs exactly inside the weighted
finite-population family. -/
theorem mgf_markedIndicators {N K m : ℕ} (hN : 0 < N)
    (hK : K ≤ N) (hm : m ≤ N) (t : ℝ) :
    mgf (show N ≤ N by rfl) (markedIndicator N K) (markedIndicator N m) t =
      Hypergeometric.mgf N K m t := by
  rw [mgf_binary_eq_sliceMgf hN (show N ≤ N by rfl)
    (markedIndicator N K) (markedIndicator_binary N K) (markedIndicator N m) t]
  rw [successCount_markedIndicator hK, centeredWeight_markedIndicator hN hm,
    mul_canonicalTwoLevel_one]
  rw [sliceMgf_canonicalTwoLevel hN hm, Hypergeometric.mgf_parameterSwap hm hK]

theorem sum_sq_markedIndicator {N m : ℕ} (hm : m ≤ N) :
    ∑ j, (markedIndicator N m j) ^ 2 = m := by
  calc
    ∑ j, (markedIndicator N m j) ^ 2 = ∑ j, markedIndicator N m j := by
      apply Finset.sum_congr rfl
      intro j hj
      rcases markedIndicator_binary N m j with h | h <;> simp [h]
    _ = m := sum_markedIndicator hm

theorem rho_markedIndicator {N m : ℕ} (hN : 2 ≤ N) (hm : m ≤ N) :
    SharpSerfling.rho N N (markedIndicator N m) =
      (m : ℝ) * ((N : ℝ) - (m : ℝ)) / ((N : ℝ) - 1) := by
  unfold SharpSerfling.rho
  rw [sum_sq_markedIndicator hm, sum_markedIndicator hm]
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  field_simp [hNm1]

/-- Equal sample-mean weights, after centering and scaling by `n * t`, are
exactly the canonical two-level vector used by the hypergeometric theory. -/
theorem scaled_centeredWeight_equalWeights {N n : ℕ} (hN : 0 < N)
    (hn0 : 0 < n) (hn : n ≤ N) (t : ℝ) :
    (fun j ↦ ((n : ℝ) * t) *
      centeredWeight hn (fun _ ↦ (1 : ℝ) / (n : ℝ)) j) =
      canonicalTwoLevel N n t := by
  funext j
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn0)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hsum : (∑ i : Fin n, (1 : ℝ) / (n : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hnR]
  unfold centeredWeight canonicalTwoLevel
  rw [hsum]
  by_cases hj : (j : ℕ) < n
  · let i : Fin n := ⟨j, hj⟩
    have hij : Fin.castLE hn i = j := by ext; rfl
    have hz : zeroPad hn (fun _ : Fin n ↦ (1 : ℝ) / (n : ℝ)) j =
        (1 : ℝ) / (n : ℝ) := by
      rw [← hij, zeroPad_castLE]
    rw [hz]
    simp [Hypergeometric.marked, hj]
    field_simp [hnR, hNR]
  · have hz : zeroPad hn (fun _ : Fin n ↦ (1 : ℝ) / (n : ℝ)) j = 0 := by
      unfold zeroPad
      apply Function.extend_apply'
      rintro ⟨i, rfl⟩
      exact hj i.isLt
    rw [hz]
    simp [Hypergeometric.marked, hj]
    field_simp [hNR]

/-- Exact embedding of the centered hypergeometric MGF into the MGF of a
without-replacement sample mean from a binary population. -/
theorem sampleMeanMgf_markedIndicator {N K n : ℕ} (hN : 0 < N)
    (hK : K ≤ N) (hn0 : 0 < n) (hn : n ≤ N) (t : ℝ) :
    sampleMeanMgf hn (markedIndicator N K) ((n : ℝ) * t) =
      Hypergeometric.mgf N K n t := by
  rw [sampleMeanMgf_eq_mgf hn0 hn]
  rw [mgf_binary_eq_sliceMgf hN hn (markedIndicator N K)
    (markedIndicator_binary N K) (fun _ ↦ (1 : ℝ) / (n : ℝ)) ((n : ℝ) * t)]
  rw [successCount_markedIndicator hK,
    scaled_centeredWeight_equalWeights hN hn0 hn]
  rw [sliceMgf_canonicalTwoLevel hN hn,
    Hypergeometric.mgf_parameterSwap hn hK]

/-- A coefficient valid for the sample-mean MGF at a fixed sample size.  This
is the exact normalization used in Corollary 1. -/
def SerflingFixedCoefficient (N n : ℕ) (c : ℝ) : Prop :=
  ∀ (hn : n ≤ N) (a b : ℝ) (X : Fin N → ℝ),
    (∀ j, a ≤ X j ∧ X j ≤ b) → ∀ t : ℝ,
    Real.log (sampleMeanMgf hn X t) ≤
      c * ((N : ℝ) - (n : ℝ)) /
        (8 * (n : ℝ) * ((N : ℝ) - 1)) * (b - a) ^ 2 * t ^ 2

/-- A single coefficient valid in the sample-mean inequality simultaneously
for all nontrivial sample sizes. -/
def SerflingUniformCoefficient (N : ℕ) (c : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ N - 1 → SerflingFixedCoefficient N n c

theorem serflingFixedCoefficient_kappa {N n : ℕ} (hN : 2 ≤ N)
    (hn0 : 1 ≤ n) (hnN : n ≤ N - 1) :
    SerflingFixedCoefficient N n (SharpSerfling.kappa N) := by
  intro hn a b X hX t
  exact serfling_mgf hN hn0 hnN X hX t

theorem serflingUniformCoefficient_kappa {N : ℕ} (hN : 2 ≤ N) :
    SerflingUniformCoefficient N (SharpSerfling.kappa N) := by
  intro n hn0 hnN
  exact serflingFixedCoefficient_kappa hN hn0 hnN

/-- Any fixed-`n` sample-mean coefficient also bounds the corresponding
hypergeometric MGF, through the explicit binary population witness. -/
theorem hypergeom_mgf_le_of_serflingFixedCoefficient {N n : ℕ}
    (hN : 2 ≤ N) (hn0 : 1 ≤ n) (hnN : n ≤ N - 1) {c : ℝ}
    (hc : SerflingFixedCoefficient N n c) (K : ℕ) (hK : K ≤ N) (t : ℝ) :
    Real.log (Hypergeometric.mgf N K n t) ≤
      c * SharpSerfling.hypergeomScale N n * t ^ 2 := by
  have hn : n ≤ N := by omega
  have hv : ∀ j, (0 : ℝ) ≤ markedIndicator N K j ∧
      markedIndicator N K j ≤ 1 := by
    intro j
    rcases markedIndicator_binary N K j with h | h <;> simp [h]
  have hbound := hc hn 0 1 (markedIndicator N K) hv ((n : ℝ) * t)
  rw [sampleMeanMgf_markedIndicator (by omega) hK (by omega) hn] at hbound
  calc
    Real.log (Hypergeometric.mgf N K n t) ≤
        c * ((N : ℝ) - (n : ℝ)) /
          (8 * (n : ℝ) * ((N : ℝ) - 1)) * (1 - 0) ^ 2 *
            ((n : ℝ) * t) ^ 2 := hbound
    _ = c * SharpSerfling.hypergeomScale N n * t ^ 2 := by
      have hnR : (n : ℝ) ≠ 0 := by positivity
      have hNm1 : (N : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < (N : ℝ) := by
          exact_mod_cast (show 1 < N by omega)
        linarith
      unfold SharpSerfling.hypergeomScale
      field_simp [hnR, hNm1]
      ring

theorem hypergeomUniform_of_serflingUniform {N : ℕ} (hN : 2 ≤ N)
    {c : ℝ} (hc : SerflingUniformCoefficient N c) :
    Hypergeometric.UniformCoefficient N c := by
  intro K n hK hn0 hnN t
  exact hypergeom_mgf_le_of_serflingFixedCoefficient hN hn0 hnN
    (hc n hn0 hnN) K hK t

/-- Corollary 1 with its uniform sharpness clause: `κ_N` is valid for every
sample size and no smaller population-size-only multiplier can be valid. -/
theorem serfling_uniform_sharp_constant {N : ℕ} (hN : 2 ≤ N) :
    SerflingUniformCoefficient N (SharpSerfling.kappa N) ∧
      ∀ c : ℝ, SerflingUniformCoefficient N c →
        SharpSerfling.kappa N ≤ c := by
  constructor
  · exact serflingUniformCoefficient_kappa hN
  · intro c hc
    exact Hypergeometric.kappa_le_of_uniformCoefficient hN
      (hypergeomUniform_of_serflingUniform hN hc)

theorem normalizedLogMgf_le_of_serflingFixedCoefficient {N n : ℕ}
    (hN : 2 ≤ N) (hn0 : 1 ≤ n) (hnN : n ≤ N - 1) {c : ℝ}
    (hc : SerflingFixedCoefficient N n c) (K : ℕ) (hK : K ≤ N)
    (t : ℝ) (ht : t ≠ 0) :
    Hypergeometric.normalizedLogMgf N K n t ≤ c := by
  have hscale : 0 < SharpSerfling.hypergeomScale N n :=
    Hypergeometric.hypergeomScale_pos_of_nontrivial hN hn0 hnN
  have hden : 0 < SharpSerfling.hypergeomScale N n * t ^ 2 :=
    mul_pos hscale (sq_pos_of_ne_zero ht)
  unfold Hypergeometric.normalizedLogMgf
  apply (div_le_iff₀ hden).2
  simpa [mul_assoc] using
    hypergeom_mgf_le_of_serflingFixedCoefficient hN hn0 hnN hc K hK t

/-- The fixed-sample-size sharpness assertion of Corollary 1 for even
population size: for every `1 ≤ n ≤ N - 1`, the best multiplier is one. -/
theorem serfling_fixed_even_sharp {q n : ℕ} (hq : 0 < q)
    (hn0 : 1 ≤ n) (hnN : n ≤ 2 * q - 1) :
    SerflingFixedCoefficient (2 * q) n (SharpSerfling.kappa (2 * q)) ∧
      ∀ c : ℝ, SerflingFixedCoefficient (2 * q) n c →
        SharpSerfling.kappa (2 * q) ≤ c := by
  constructor
  · exact serflingFixedCoefficient_kappa (by omega) hn0 hnN
  · intro c hc
    have hlim := Hypergeometric.tendsto_normalizedLogMgf_even_central hq hn0 hnN
    have hevent : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ,
        Hypergeometric.normalizedLogMgf (2 * q) q n t ≤ c := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      exact normalizedLogMgf_le_of_serflingFixedCoefficient
        (by omega) hn0 hnN hc q (by omega) t ht0
    have hone : (1 : ℝ) ≤ c := le_of_tendsto hlim hevent
    have hEven : Even (2 * q) := ⟨q, by omega⟩
    rw [SharpSerfling.kappa_of_even hEven]
    exact hone

/-- For odd `N`, uniform sharpness is attained already at sample size one by
the explicit central binary population and distinguished nonzero tilt. -/
theorem serfling_uniform_odd_witness {q : ℕ} (hq : 0 < q) :
    Real.log
        (sampleMeanMgf (show 1 ≤ 2 * q + 1 by omega)
          (markedIndicator (2 * q + 1) q)
          (2 * Hypergeometric.oddLogIncrement (2 * q + 1))) /
        (SharpSerfling.hypergeomScale (2 * q + 1) 1 *
          (2 * Hypergeometric.oddLogIncrement (2 * q + 1)) ^ 2) =
      SharpSerfling.kappa (2 * q + 1) := by
  have hbridge := sampleMeanMgf_markedIndicator
    (N := 2 * q + 1) (K := q) (n := 1) (by omega) (by omega)
    (by omega) (by omega) (2 * Hypergeometric.oddLogIncrement (2 * q + 1))
  have hwitness := Hypergeometric.normalizedLogMgf_odd_witness hq
  unfold Hypergeometric.normalizedLogMgf at hwitness
  rw [show sampleMeanMgf (show 1 ≤ 2 * q + 1 by omega)
      (markedIndicator (2 * q + 1) q)
      (2 * Hypergeometric.oddLogIncrement (2 * q + 1)) =
        Hypergeometric.mgf (2 * q + 1) q 1
          (2 * Hypergeometric.oddLogIncrement (2 * q + 1)) by
      simpa using hbridge]
  exact hwitness

/-- A candidate coefficient valid for every bounded weighted finite
population of a fixed size `N`. -/
def WeightedUniformCoefficient (N : ℕ) (c : ℝ) : Prop :=
  ∀ (n : ℕ) (hn : n ≤ N) (a b : ℝ) (X : Fin N → ℝ),
    (∀ j, a ≤ X j ∧ X j ≤ b) → ∀ (w : Fin n → ℝ) (t : ℝ),
    Real.log (mgf hn X w t) ≤
      c / 8 * SharpSerfling.rho N n w * (b - a) ^ 2 * t ^ 2

theorem weightedUniformCoefficient_kappa {N : ℕ} (hN : 2 ≤ N) :
    WeightedUniformCoefficient N (SharpSerfling.kappa N) := by
  intro n hn a b X hX w t
  exact weighted_mgf N n hN hn a b X hX w t

theorem hypergeomUniform_of_weightedUniform {N : ℕ} (hN : 2 ≤ N)
    {c : ℝ} (hc : WeightedUniformCoefficient N c) :
    Hypergeometric.UniformCoefficient N c := by
  intro K m hK hm0 hmN t
  have hm : m ≤ N := by omega
  have hv : ∀ j, (0 : ℝ) ≤ markedIndicator N K j ∧ markedIndicator N K j ≤ 1 := by
    intro j
    rcases markedIndicator_binary N K j with h | h <;> simp [h]
  have hbound := hc N (show N ≤ N by rfl) 0 1 (markedIndicator N K) hv
    (markedIndicator N m) t
  rw [mgf_markedIndicators (by omega) hK hm,
    rho_markedIndicator hN hm] at hbound
  unfold SharpSerfling.hypergeomScale
  calc
    Real.log (Hypergeometric.mgf N K m t) ≤
        c / 8 * ((m : ℝ) * ((N : ℝ) - (m : ℝ)) / ((N : ℝ) - 1)) *
          (1 - 0) ^ 2 * t ^ 2 := hbound
    _ = c * ((m : ℝ) * ((N : ℝ) - (m : ℝ)) /
          (8 * ((N : ℝ) - 1))) * t ^ 2 := by
      have hNm1 : (N : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
        linarith
      have hcoef : c / 8 *
          ((m : ℝ) * ((N : ℝ) - (m : ℝ)) / ((N : ℝ) - 1)) =
          c * ((m : ℝ) * ((N : ℝ) - (m : ℝ)) /
            (8 * ((N : ℝ) - 1))) := by
        field_simp [hNm1]
      rw [hcoef]
      norm_num

/-- Exact validity and minimality of the finite-population multiplier. -/
theorem finitePopulation_sharp_constant {N : ℕ} (hN : 2 ≤ N) :
    WeightedUniformCoefficient N (SharpSerfling.kappa N) ∧
      ∀ c : ℝ, WeightedUniformCoefficient N c → SharpSerfling.kappa N ≤ c := by
  constructor
  · exact weightedUniformCoefficient_kappa hN
  · intro c hc
    exact Hypergeometric.kappa_le_of_uniformCoefficient hN
      (hypergeomUniform_of_weightedUniform hN hc)

/-- Randomly permuting a fixed population produces an exchangeable random
vector on the finite uniform permutation space. -/
theorem isExchangeable_uniformPermutation {N : ℕ} (x : Fin N → ℝ) :
    letI : MeasurableSpace (Equiv.Perm (Fin N)) := ⊤
    IsExchangeable (PMF.uniformOfFintype (Equiv.Perm (Fin N))).toMeasure
      (fun σ j ↦ x (σ j)) := by
  letI : MeasurableSpace (Equiv.Perm (Fin N)) := ⊤
  intro π f
  rw [SharpSerfling.integral_uniformOfFintype_eq_finiteAverage,
    SharpSerfling.integral_uniformOfFintype_eq_finiteAverage]
  let e : Equiv.Perm (Fin N) ≃ Equiv.Perm (Fin N) := Equiv.mulRight π
  calc
    SharpSerfling.finiteAverage
        (fun σ : Equiv.Perm (Fin N) ↦ f (fun j ↦ x (σ (π j)))) =
        SharpSerfling.finiteAverage
          ((fun σ : Equiv.Perm (Fin N) ↦ f (fun j ↦ x (σ j))) ∘ e) := by
      apply congrArg SharpSerfling.finiteAverage
      funext σ
      simp [e]
    _ = SharpSerfling.finiteAverage
        (fun σ : Equiv.Perm (Fin N) ↦ f (fun j ↦ x (σ j))) :=
      SharpSerfling.finiteAverage_equiv e _

theorem exchangeableMgf_uniformPermutation {N n : ℕ} (hn : n ≤ N)
    (x : Fin N → ℝ) (w : Fin n → ℝ) (lam : ℝ) :
    letI : MeasurableSpace (Equiv.Perm (Fin N)) := ⊤
    exchangeableMgf (PMF.uniformOfFintype (Equiv.Perm (Fin N))).toMeasure
      hn (fun σ j ↦ x (σ j)) w lam = mgf hn x w lam := by
  letI : MeasurableSpace (Equiv.Perm (Fin N)) := ⊤
  unfold exchangeableMgf
  rw [SharpSerfling.integral_uniformOfFintype_eq_finiteAverage]
  apply congrArg SharpSerfling.finiteAverage
  funext σ
  rw [contrast_comp_perm]

/-- A candidate coefficient in the manuscript's exchangeable
`c * N/(N-1) * ‖w°‖²` normalization. -/
def ExchangeableUniformCoefficient (N : ℕ) (c : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) (hn : n ≤ N)
    (a b : ℝ) (X : Ω → Fin N → ℝ),
    (∀ j, StronglyMeasurable (fun ω ↦ X ω j)) →
    (∀ ω j, a ≤ X ω j ∧ X ω j ≤ b) → IsExchangeable μ X →
    ∀ (w : Fin n → ℝ) (lam : ℝ),
    Real.log (exchangeableMgf μ hn X w lam) ≤
      lam ^ 2 * (b - a) ^ 2 / 8 *
        (c * (N : ℝ) / ((N : ℝ) - 1)) * sqNorm (centeredWeight hn w)

theorem exchangeableUniformCoefficient_kappa {N : ℕ} (hN : 2 ≤ N) :
    ExchangeableUniformCoefficient N (SharpSerfling.kappa N) := by
  intro Ω mΩ μ hμ n hn a b X hXmeas hX hEx w lam
  exact weighted_exchangeable_mgf_centeredNorm μ hN hn X hXmeas hX hEx w lam

theorem weightedUniform_of_exchangeableUniform {N : ℕ} (hN : 2 ≤ N)
    {c : ℝ} (hc : ExchangeableUniformCoefficient N c) :
    WeightedUniformCoefficient N c := by
  intro n hn a b x hx w lam
  let Ω := Equiv.Perm (Fin N)
  letI : MeasurableSpace Ω := ⊤
  let μ : Measure Ω := (PMF.uniformOfFintype Ω).toMeasure
  have hmeas : ∀ j, StronglyMeasurable (fun σ : Ω ↦ x (σ j)) := by
    intro j
    exact StronglyMeasurable.of_discrete
  have hrange : ∀ (σ : Ω) j, a ≤ x (σ j) ∧ x (σ j) ≤ b := by
    intro σ j
    exact hx (σ j)
  have hEx : IsExchangeable μ (fun σ j ↦ x (σ j)) := by
    exact isExchangeable_uniformPermutation x
  have hbound := hc Ω μ n hn a b (fun σ j ↦ x (σ j))
    hmeas hrange hEx w lam
  rw [exchangeableMgf_uniformPermutation hn x w lam] at hbound
  have hnorm := sum_sq_centeredWeight_eq_rho hN hn w
  change sqNorm (centeredWeight hn w) = _ at hnorm
  calc
    Real.log (mgf hn x w lam) ≤
        lam ^ 2 * (b - a) ^ 2 / 8 * (c * (N : ℝ) / ((N : ℝ) - 1)) *
          sqNorm (centeredWeight hn w) := hbound
    _ = c / 8 * SharpSerfling.rho N n w * (b - a) ^ 2 * lam ^ 2 := by
      rw [hnorm]
      have hNR : (N : ℝ) ≠ 0 := by positivity
      have hNm1 : (N : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
        linarith
      field_simp [hNR, hNm1]

/-- Exact validity and minimality of the exchangeable multiplier. -/
theorem exchangeable_sharp_constant {N : ℕ} (hN : 2 ≤ N) :
    ExchangeableUniformCoefficient N (SharpSerfling.kappa N) ∧
      ∀ c : ℝ, ExchangeableUniformCoefficient N c → SharpSerfling.kappa N ≤ c := by
  constructor
  · exact exchangeableUniformCoefficient_kappa hN
  · intro c hc
    exact (finitePopulation_sharp_constant hN).2 c
      (weightedUniform_of_exchangeableUniform hN hc)

end SharpSerfling.FinitePopulation
