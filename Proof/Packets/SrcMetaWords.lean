import Proof.Packets.SrcMetaTM
import Proof.Packets.SrcCapsPow2
import Proof.SourceAssembly.SLoadSetup
import Proof.CaseAnalysis.RowsCountBinary

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.MetaWords
open NearCubicWires LocalBitMultitape RepairOrdinary RepairRepresentation
open NearCubicWires.SourceStart.MetaTM
noncomputable section

/-! ## 1. `natWord` in terms of `SignedSortKey.binary` -/

theorem binary_eq (W n : ℕ) : SignedSortKey.binary W n = List.ofFn (fun i : Fin W => n.testBit i.val) := by
  induction W generalizing n with
  | zero => rfl
  | succ W ih =>
    rw [SignedSortKey.binary, ih, List.ofFn_succ]
    congr 1
    · show (n % 2 == 1) = n.testBit 0
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
    · congr 1
      funext i
      rw [Nat.testBit_div_two]
      rfl

theorem natWord_eq (n : ℕ) :
    natWord n = List.replicate (natBitLength n) true ++ false :: SignedSortKey.binary (natBitLength n) n := by
  rw [binary_eq]
  rfl

/-! ## 2. Powers of two and shifted words -/

theorem bitlen_mul_pow (m x : ℕ) (hm : 1 ≤ m) : natBitLength (m * 2^x) = natBitLength m + x := by
  unfold natBitLength
  induction x with
  | zero => simp
  | succ x ih =>
    have hne : m * 2^x ≠ 0 := Nat.mul_ne_zero (by omega) (by positivity)
    rw [pow_succ, ← mul_assoc, Nat.log_mul_base (by norm_num) hne]
    omega

theorem binary_mul_pow (m x W : ℕ) :
    SignedSortKey.binary (W + x) (m * 2^x) = List.replicate x false ++ SignedSortKey.binary W m := by
  rw [binary_eq, binary_eq]
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_append, List.length_replicate, List.getElem_replicate]
    rw [Nat.testBit_mul_two_pow]
    split_ifs with hi
    · simp [show ¬ x ≤ i by omega]
    · simp [show x ≤ i by omega]

/-- **A shifted word**: `natWord (m·2^x) = 1^(bitlen m + x) ++ [false] ++ 0^x ++ bits m` (`1 ≤ m`). -/
theorem natWord_shift (m x : ℕ) (hm : 1 ≤ m) :
    natWord (m * 2^x) = List.replicate (natBitLength m + x) true ++ [false] ++ List.replicate x false ++
      CloseoutRowsCountBinary.bits m := by
  rw [natWord_eq, bitlen_mul_pow m x hm, binary_mul_pow]
  unfold CloseoutRowsCountBinary.bits
  rw [if_neg (by omega)]
  simp [List.append_assoc]

/-- **A power of two**: `natWord (2^y) = 1^(y+1) ++ [false] ++ 0^y ++ [true]`. -/
theorem natWord_pow2 (y : ℕ) :
    natWord (2^y) = List.replicate (y + 1) true ++ [false] ++ List.replicate y false ++ [true] := by
  have h := natWord_shift 1 y le_rfl
  rw [one_mul] at h
  rw [h]
  have e1 : natBitLength 1 = 1 := rfl
  have e2 : CloseoutRowsCountBinary.bits 1 = [true] := rfl
  rw [e1, e2, Nat.add_comm 1 y]

/-! ## 3. The meta word's frame as a concatenation of bodies -/

/-- The body of a word (`MetaTM.body false`). -/
abbrev bd (w : List Bool) : List Bool := body false w

theorem metaBits_eq (w deg C hF cC dR rR : ℕ) :
    SLoad.Setup.metaBits w deg C (⟨hF, cC, dR, rR⟩ : PCJd4d1d9d7d1fa4313_Production.RowCaps) =
      natWord 3 ++ natWord w ++ natWord deg ++ natWord C ++ natWord 4 ++ natWord hF ++ natWord cC ++ natWord dR ++
        natWord rR := by
  unfold SLoad.Setup.metaBits PCJd4d1d9d7d1fa4313_Production.RowCaps.word
  simp [natListWord, List.append_assoc]

/-- **`frame MB` as the concatenation of the nine natWords' bodies and one terminator.** -/
theorem meta_frame (w deg C hF cC dR rR : ℕ) :
    RepairOrdinary.frame (SLoad.Setup.metaBits w deg C (⟨hF, cC, dR, rR⟩ : PCJd4d1d9d7d1fa4313_Production.RowCaps)) =
      bd (natWord 3) ++ bd (natWord w) ++ bd (natWord deg) ++ bd (natWord C) ++ bd (natWord 4) ++ bd (natWord hF) ++
        bd (natWord cC) ++ bd (natWord dR) ++ bd (natWord rR) ++ [false] := by
  rw [metaBits_eq, ← body_false]
  simp only [bd, body_append]

/-- A power-of-two word's body, split into its four pieces' bodies. -/
theorem bd_pow2 (y : ℕ) : bd (natWord (2^y)) =
    bd (List.replicate (y + 1) true) ++ bd [false] ++ bd (List.replicate y false) ++ bd [true] := by
  rw [natWord_pow2]
  simp only [bd, body_append]

/-- A shifted word's body, split into its four pieces' bodies. -/
theorem bd_shift (m x : ℕ) (hm : 1 ≤ m) : bd (natWord (m * 2^x)) =
    bd (List.replicate (natBitLength m + x) true) ++ bd [false] ++ bd (List.replicate x false) ++
      bd (CloseoutRowsCountBinary.bits m) := by
  rw [natWord_shift m x hm]
  simp only [bd, body_append]

end
end NearCubicWires.SourceStart.MetaWords

