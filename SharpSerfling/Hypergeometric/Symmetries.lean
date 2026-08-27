import SharpSerfling.Hypergeometric.Definitions
import Mathlib.Data.Fin.Rev

namespace SharpSerfling.Hypergeometric

/-- Complementing the sampled subset identifies sample sizes `m` and `N-m`. -/
def sampleComplement {N m : ℕ} (hm : m ≤ N) : Sample N m ≃ Sample N (N - m) :=
  Set.powersetCard.compl (by simpa using Nat.sub_add_cancel hm)

@[simp]
theorem sampleComplement_val {N m : ℕ} (hm : m ≤ N) (s : Sample N m) :
    (sampleComplement hm s : Finset (Fin N)) = (s : Finset (Fin N))ᶜ :=
  rfl

theorem count_sampleComplement {N K m : ℕ} (hK : K ≤ N) (hm : m ≤ N)
    (s : Sample N m) : count K (sampleComplement hm s) = K - count K s := by
  change (s.1ᶜ ∩ marked N K).card = K - (s.1 ∩ marked N K).card
  rw [show s.1ᶜ ∩ marked N K = marked N K \ s.1 by ext; simp [and_comm]]
  rw [Finset.card_sdiff, card_marked hK, Finset.inter_comm]

theorem centered_sampleComplement {N K m : ℕ} (hN : 0 < N) (hK : K ≤ N)
    (hm : m ≤ N) (s : Sample N m) (t : ℝ) :
    t * ((count K (sampleComplement hm s) : ℝ) - center N K (N - m)) =
      -t * ((count K s : ℝ) - center N K m) := by
  rw [count_sampleComplement hK hm s]
  rw [Nat.cast_sub (count_le_marked hK s), center, center, Nat.cast_sub hm]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
  ring

/-- Manuscript identity `G_{N,K,N-m}(t) = G_{N,K,m}(-t)`. -/
theorem mgf_sampleComplement {N K m : ℕ} (hN : 0 < N) (hK : K ≤ N)
    (hm : m ≤ N) (t : ℝ) : mgf N K (N - m) t = mgf N K m (-t) := by
  let e : Sample N m ≃ Sample N (N - m) := sampleComplement hm
  unfold mgf
  rw [← SharpSerfling.finiteAverage_equiv e]
  apply congrArg SharpSerfling.finiteAverage
  funext s
  apply congrArg Real.exp
  exact centered_sampleComplement hN hK hm s t

/-- Relabel fixed-cardinality samples along a permutation of the population. -/
def sampleRelabel {N m : ℕ} (e : Equiv.Perm (Fin N)) : Sample N m ≃ Sample N m where
  toFun s := Set.powersetCard.map m e.toEmbedding s
  invFun s := Set.powersetCard.map m e.symm.toEmbedding s
  left_inv s := by
    apply Subtype.ext
    ext i
    simp [Set.powersetCard.map]
  right_inv s := by
    apply Subtype.ext
    ext i
    simp [Set.powersetCard.map]

/-- Reversal turns successes for `N-K` into failures for `K`. -/
theorem count_successComplement {N K m : ℕ} (hK : K ≤ N) (s : Sample N m) :
    count (N - K) (sampleRelabel Fin.revPerm s) = m - count K s := by
  change ((Finset.map Fin.revPerm.toEmbedding s.1) ∩ marked N (N - K)).card =
    m - (s.1 ∩ marked N K).card
  have hsets : (Finset.map Fin.revPerm.toEmbedding s.1) ∩ marked N (N - K) =
      Finset.map Fin.revPerm.toEmbedding (s.1 \ marked N K) := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_map, Finset.mem_sdiff, marked,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j, hj, hji⟩, hi⟩
      refine ⟨j, ⟨hj, ?_⟩, hji⟩
      intro hjK
      have hv : i.val = N - (j.val + 1) := by
        simpa [Fin.rev] using congrArg Fin.val hji.symm
      omega
    · rintro ⟨j, ⟨hj, hjK⟩, hji⟩
      constructor
      · exact ⟨j, hj, hji⟩
      · have hv : i.val = N - (j.val + 1) := by
          simpa [Fin.rev] using congrArg Fin.val hji.symm
        omega
  rw [hsets, Finset.card_map, Finset.card_sdiff, Finset.inter_comm]
  exact congrArg (fun q => q - (s.1 ∩ marked N K).card) s.property

theorem centered_successComplement {N K m : ℕ} (hN : 0 < N) (hK : K ≤ N)
    (s : Sample N m) (t : ℝ) :
    t * ((count (N - K) (sampleRelabel Fin.revPerm s) : ℝ) - center N (N - K) m) =
      -t * ((count K s : ℝ) - center N K m) := by
  rw [count_successComplement hK s]
  rw [Nat.cast_sub (count_le_sample s), center, center, Nat.cast_sub hK]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
  ring

/-- Manuscript identity `G_{N,N-K,m}(t) = G_{N,K,m}(-t)`. -/
theorem mgf_successComplement {N K m : ℕ} (hN : 0 < N) (hK : K ≤ N) (t : ℝ) :
    mgf N (N - K) m t = mgf N K m (-t) := by
  let e : Sample N m ≃ Sample N m := sampleRelabel Fin.revPerm
  unfold mgf
  rw [← SharpSerfling.finiteAverage_equiv e]
  apply congrArg SharpSerfling.finiteAverage
  funext s
  apply congrArg Real.exp
  exact centered_successComplement hN hK s t

end SharpSerfling.Hypergeometric
