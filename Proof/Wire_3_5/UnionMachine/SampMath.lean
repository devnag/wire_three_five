import Proof.Wire_3_5.FinalPass.HashCell
import Proof.Wire_3_5.Primitive.SeedFix.C4Iface

/-! # C6 tail, item 2 (part 1): the sample positions as Horner values

"Evaluate a uniformly random polynomial of degree `2h−1` at those labels and project each value to `k` binary
coordinates" (`samp:seed`, P3:2932-2937). The seed's coefficients are its `ℓ`-bit chunks (**`chunk_eq`**); the
reference generator's value at the label `j` is Horner's rule on the coefficient records, the top coefficient first
(**`gen_horner`**, the machine field `𝔽₂[x]/(p)`, C5's `hornerBits`); the position `posC` is the value's low `2kh`
bits, the row its bits `[kh, 2kh)` and the column its bits `[0, kh)` (**`posC_vals`**, `binary_hi`, `binary_lo`).
So the printed sample word is the list of `pairW` of the Horner values (**`sampleWord_eq`**).

Paper quantity of the main type: the sample positions `posC P (bitsNum s) j`, `j < Q`, in the final pass's format. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.SampMath
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (hornerStep coefsRev hornerBits_fold)

/-! ## The values -/

/-- The seed's coefficients `a_i`: bits `[iℓ, (i+1)ℓ)` of the seed number. -/
def coefs (P : SeedParams) (s : Fin (8 * P.ell) → Bool) : Fin 8 → ℕ :=
  fun i => seedCoeff P.ell (SeedFix.bitsNum _ s) i

/-- The coefficient records of Horner's rule, the top coefficient first. -/
def allC (P : SeedParams) (s : Fin (8 * P.ell) → Bool) : List ℕ := coefsRev (coefs P s)

/-- The generator's value at the label `j`, by Horner's rule. -/
def hv (P : SeedParams) (s : Fin (8 * P.ell) → Bool) (j : ℕ) : ℕ :=
  (allC P s).foldl (hornerStep P.modulus P.ell j) 0

/-- The two framed `kh`-bit words of a value: its bits `[kh, 2kh)`, then its bits `[0, kh)`. -/
def pairW (ℓ kh v : ℕ) : List Bool := frame (((binary ℓ v).drop kh).take kh) ++ frame ((binary ℓ v).take kh)

/-! ## The chunks of the seed -/

theorem chunk_eq (ℓ : ℕ) (s : Fin (8 * ℓ) → Bool) (i : ℕ) (hi : i < 8) :
    binary ℓ (seedCoeff ℓ (SeedFix.bitsNum _ s) i) = ((List.ofFn s).drop (i * ℓ)).take ℓ := by
  have hle : i * ℓ + ℓ ≤ 8 * ℓ := by nlinarith
  apply List.ext_getElem
  · simp only [binary_length, List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro t h1 h2
    have ht : t < ℓ := by simpa using h1
    have hlt : i * ℓ + t < 8 * ℓ := by omega
    rw [GF2.binary_getElem, List.getElem_take, List.getElem_drop, List.getElem_ofFn,
      testBit_seedCoeff _ _ _ _ ht, SeedFix.testBit_bitsNum, dif_pos hlt]

/-! ## Horner's rule is the reference generator -/

theorem gen_horner (P : SeedParams) (seed j : ℕ) (hj : j < 2 ^ P.ell) :
    JoinElimination.gen P.modulus P.ell 8 seed j =
      (coefsRev fun i : Fin 8 => seedCoeff P.ell seed i).foldl (hornerStep P.modulus P.ell j) 0 := by
  rw [hornerBits_fold]
  have hp := P.cert.2.1
  obtain ⟨h1, h2⟩ := FinalPass.hornerBits_spec P.modulus P.ell hp j hj 8 (fun i => seedCoeff P.ell seed i)
    (fun i => seedCoeff_lt _ _ _)
  obtain ⟨h3, h4⟩ := gen_spec P.modulus P.ell seed j hp P.one_le_ell hj 8
  rw [gen_eq]
  apply GF.rep_injOn P.modulus P.ell _ _ hp h3 h1
  rw [h4, h2]
  exact (Fin.sum_univ_eq_sum_range (fun r => GF.rep P.modulus (seedCoeff P.ell seed r) * GF.rep P.modulus j ^ r)
    8).symm

/-! ## The position of a value -/

theorem ofVec_bits (m g : ℕ) : ofVec (fun b : Fin m => GF.bitF (g.testBit b)) = g % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ofVec, Nat.testBit_mod_two_pow]
  by_cases hi : i < m
  · cases hg : g.testBit i
    · simp [hi, hg, GF.bitF]
    · simp [hi, hg, GF.bitF]
  · simp [hi]

theorem posC_vals (P : SeedParams) (seed : ℕ) (j : Fin P.Q) :
    ((SeedFix.posC P seed j).1 : ℕ) = JoinElimination.gen P.modulus P.ell 8 seed j % 2 ^ (2 * P.kh) / 2 ^ P.kh ∧
      ((SeedFix.posC P seed j).2 : ℕ) = JoinElimination.gen P.modulus P.ell 8 seed j % 2 ^ P.kh := by
  have hnum : SeedFix.cellNumC (SeedFix.posC P seed j) =
      JoinElimination.gen P.modulus P.ell 8 seed j % 2 ^ (2 * P.kh) := by
    rw [SeedFix.cellNumC_eq P, cellNum, SeedFix.posC, Equiv.symm_apply_apply, ofVec_bits]
  unfold SeedFix.cellNumC at hnum
  have h2 : ((SeedFix.posC P seed j).2 : ℕ) < 2 ^ P.kh := (SeedFix.posC P seed j).2.isLt
  have hdvd : 2 ^ P.kh ∣ 2 ^ (2 * P.kh) := pow_dvd_pow 2 (by omega)
  constructor
  · rw [← hnum, Nat.add_mul_div_left _ _ (Nat.two_pow_pos P.kh), Nat.div_eq_of_lt h2, Nat.zero_add]
  · rw [← Nat.mod_mod_of_dvd _ hdvd, ← hnum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]

theorem binary_hi (ℓ kh g : ℕ) (h : 2 * kh ≤ ℓ) :
    binary kh (g % 2 ^ (2 * kh) / 2 ^ kh) = ((binary ℓ g).drop kh).take kh := by
  apply List.ext_getElem
  · simp only [binary_length, List.length_take, List.length_drop]
    omega
  · intro t h1 h2
    have ht : t < kh := by simpa using h1
    rw [GF2.binary_getElem, List.getElem_take, List.getElem_drop, GF2.binary_getElem, Nat.testBit_div_two_pow,
      Nat.testBit_mod_two_pow, Nat.add_comm t kh]
    simp [show kh + t < 2 * kh by omega]

theorem binary_lo (ℓ kh g : ℕ) (h : kh ≤ ℓ) : binary kh (g % 2 ^ kh) = (binary ℓ g).take kh := by
  apply List.ext_getElem
  · simp only [binary_length, List.length_take]
    omega
  · intro t h1 h2
    have ht : t < kh := by simpa using h1
    rw [GF2.binary_getElem, List.getElem_take, GF2.binary_getElem, Nat.testBit_mod_two_pow]
    simp [ht]

/-! ## The sample word -/

theorem pair_eq (P : SeedParams) (s : Fin (8 * P.ell) → Bool) (j : Fin P.Q) :
    frame (binary P.kh ((SeedFix.posC P (SeedFix.bitsNum _ s) j).1 : ℕ)) ++
      frame (binary P.kh ((SeedFix.posC P (SeedFix.bitsNum _ s) j).2 : ℕ)) = pairW P.ell P.kh (hv P s j) := by
  have hj : (j : ℕ) < 2 ^ P.ell := lt_of_lt_of_le j.isLt P.Q_le
  have hk := P.k_le
  obtain ⟨h1, h2⟩ := posC_vals P (SeedFix.bitsNum _ s) j
  rw [h1, h2, binary_hi _ _ _ hk, binary_lo P.ell P.kh _ (by omega), gen_horner P _ j hj]
  rfl

theorem flatMap_ofFn_range {β γ : Type} : ∀ (n : ℕ) (g : Fin n → β) (F : β → List γ) (H : ℕ → List γ),
    (∀ j : Fin n, F (g j) = H j) → (List.ofFn g).flatMap F = (List.range n).flatMap H
  | 0, _, _, _, _ => rfl
  | n + 1, g, F, H, h => by
    rw [List.ofFn_succ', List.range_succ, List.concat_eq_append, List.flatMap_append, List.flatMap_append,
      flatMap_ofFn_range n (fun j => g j.castSucc) F H (fun j => h j.castSucc)]
    simp [h (Fin.last n)]

/-- **The printed sample word** is the list of `pairW` of the Horner values at the labels `j < Q`. -/
theorem sampleWord_eq (P : SeedParams) (s : Fin (8 * P.ell) → Bool) :
    FinalPass.Sample.sampleWord P.kh (PrimT.C4Iface.seedPairs P s) =
      (List.range P.Q).flatMap fun j => pairW P.ell P.kh (hv P s j) := by
  unfold FinalPass.Sample.sampleWord PrimT.C4Iface.seedPairs
  exact flatMap_ofFn_range P.Q _ _ _ (fun j => pair_eq P s j)

end NearCubicWires.WireExponent3_5.UnionMachine.SampMath
