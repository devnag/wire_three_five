import Proof.Wire_3_5.Primitive.SeedFix.W6N
import Proof.Wire_3_5.FinalPass.WordMap

/-! # W6, part 15: the search's entry bank and the modulus reader

P3:2121-2157 (filt:majorant: the modulus `p = GF.firstPrimitive ℓ₀` of `GF(2^{ℓ₀})`; port `19` its frame
`frame (binary ℓ₀ p)`, port `16` the value `p` in unary): the entry bank of C1's search on the streams
`srT = 161 … 175` (tape `11`, the answer, on `sMod`), and the reader of a framed binary field:
* `readFW` / **`readFW_spec`** (PA's payload round `ParseNat.bitRound_spec` on the marked cells of `frame bs`, `v += value bs`);
* `fp_split` (`p = 2^{ℓ₀} + (p mod 2^{ℓ₀})`), `bitsValue_binary'`;
* `wrF_exec`, `prepA/B/C_exec` (the fifteen entry words), **`srPrep_exec`** (the whole entry bank `srIn ℓ₀`).

Paper quantities of the main types: the search's entry bank (degree `ℓ₀`) and the modulus value. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-! ## Reading a framed binary field -/

section Read
variable {ns nr : ℕ} (cap : ℕ)

theorem bitsValue_take_lt' : ∀ (bs : List Bool) (k : ℕ), CanonicalBinary.bitsValue (bs.take k) < 2 ^ k
  | [], k => by simp [CanonicalBinary.bitsValue]
  | b :: bs, 0 => by simp [CanonicalBinary.bitsValue]
  | b :: bs, k + 1 => by
    simp only [List.take_succ_cons, CanonicalBinary.bitsValue, pow_succ]
    have := bitsValue_take_lt' bs k
    cases b <;> simp <;> omega

/-- **Read the `c` marked bits** of stream `i` (a frame's payload, low bit first) into `v`. -/
def readFW (i : Fin (ns + 1)) (c v p t : Fin nr) : WM ns nr :=
  .seq (.inc p) (.seq (.whr c (.seq (.dec c) (ParseNat.bitBody true i v p t))) (WM.clear p))

theorem readFW_spec (i : Fin (ns + 1)) (c v p t : Fin nr) (hcv : c ≠ v) (hcp : c ≠ p) (hct : c ≠ t) (hpv : p ≠ v)
    (hpt : p ≠ t) (hvt : v ≠ t) (σ : WState ns nr) (bs : List Bool) (hc : σ.val c = bs.length) (hp : σ.val p = 0)
    (ht : σ.val t = 0) (hread : ∀ m < bs.length, readTapeBit (σ.st i) (σ.sh i + 2 * m + 1) = bs.getD m false)
    (hcap : σ.val v + 2 ^ (bs.length + 1) ≤ cap) :
    WExec cap (readFW i c v p t) σ
      (((σ.seth i (σ.sh i + 2 * bs.length)).setv v (σ.val v + CanonicalBinary.bitsValue bs)).setv c 0)
      (1 + 3 + 1 + (bs.length * (36 * 2 ^ bs.length + 12 + 4) + 1 + 1 + (3 * 2 ^ bs.length + 1))) := by
  have hstp : ParseNat.stp true = 2 := rfl
  have hoff : ParseNat.off true = 1 := rfl
  set L := bs.length with hL
  set v₀ := σ.val v with hv₀
  have hpow : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have hpow2 : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
  have hLlt : L < 2 ^ L := Nat.lt_two_pow_self
  have s1 := WExec.inc (cap := cap) p σ (by rw [hp]; omega)
  rw [hp, Nat.zero_add] at s1
  let S : ℕ → WState ns nr := fun k => ParseNat.payState true σ i c v p L v₀ bs k
  have hS0 : S 0 = σ.setv p 1 := by
    simp only [S, ParseNat.payState, hstp, Nat.mul_zero, Nat.add_zero, List.take_zero, Nat.sub_zero, pow_zero]
    wgen_eq [hc, hL, hv₀, CanonicalBinary.bitsValue, hcv, hcp, hpv]
  have hloop := UnionMachine.Round.wloop cap c (ParseNat.bitBody true i v p t) (36 * 2 ^ L + 12) L S
    (fun k _ => by simp [S, ParseNat.payState, Function.update_apply, hcv, hcp, Ne.symm hcv, Ne.symm hcp])
    (by omega)
    (fun k hk => ParseNat.bitRound_spec cap true i c v p t hcv hcp hct hpv hpt hvt σ L v₀ bs rfl ht
      (fun m hm => by rw [hstp, hoff]; exact hread m hm) (by omega)
      (fun k _ => bitsValue_take_lt' bs k) k hk)
  rw [hS0] at hloop
  have hSL : (S L).val p = 2 ^ L := by simp [S, ParseNat.payState]
  have s3 := wclear_spec cap p (2 ^ L) (S L) hSL (by rw [hSL]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq hloop s3)) ?_ (by omega)
  simp only [S, ParseNat.payState, hstp, List.take_length, Nat.sub_self]
  wgen_eq [hc, hL, hv₀, hp, hcv, hcp, hpv]

end Read

theorem bitsValue_binary' : ∀ (w x : ℕ), CanonicalBinary.bitsValue (binary w x) = x % 2 ^ w
  | 0, x => by simp [binary, CanonicalBinary.bitsValue, Nat.mod_one]
  | w + 1, x => by
    simp only [binary, CanonicalBinary.bitsValue, bitsValue_binary' w (x / 2)]
    rw [pow_succ', Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem frame_marks' : ∀ u : List Bool, frame u = Streaming.marks u ++ [false]
  | [] => rfl
  | b :: u => by
    rw [frame, frame_marks' u, ParseNat.marks_cons]
    rfl

/-- **The first primitive modulus** is `2^ℓ` plus its low `ℓ` bits. -/
theorem fp_split (ℓ : ℕ) : GF.firstPrimitive ℓ % 2 ^ ℓ + 2 ^ ℓ = GF.firstPrimitive ℓ := by
  have hlt : ((List.range (2 ^ ℓ)).find? fun j => decide (GF.PrimitiveCert (2 ^ ℓ + j) ℓ)).getD 0 < 2 ^ ℓ := by
    cases h : (List.range (2 ^ ℓ)).find? fun j => decide (GF.PrimitiveCert (2 ^ ℓ + j) ℓ) with
    | none => exact Nat.one_le_two_pow
    | some j =>
      have hm := List.mem_of_find?_eq_some h
      simpa using hm
  unfold GF.firstPrimitive
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt hlt]
  omega

/-! ## The entry bank -/

variable (cap : ℕ)

/-- The search's tapes on W6's streams (tape `11`, the answer, on `sMod`). -/
def srT : Fin 15 → Fin 192 := ![161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 21, 173, 174, 175]

theorem srT_inj : Function.Injective srT := by decide

/-- The stale bank the search starts from (all zero). -/
def J00 : GF2.Junk := ⟨0, 0, false, false, false, false, false⟩

theorem wrF_exec (O : Fin 192) (σ : WL) (hst : σ.st O = []) (hsh : σ.sh O = 0) :
    WExec cap (.wr O false) σ (σ.sets O [false]) 1 := by
  have h := WExec.wr (cap := cap) O false σ
  rw [hst, hsh] at h
  exact h

def prepA : WP :=
  .seq (wPRT 161 65 [] [true, false] [false]) (.seq (wPRT 162 65 [] [true, false] [false]) (.seq (wPRT 163 65 [] [true, false] [false]) (.seq (wPRT 164 75 [true, true] [true, false] [false]) (wPRT 165 65 [] [true, true] [false]))))

theorem prepA_exec (σ : WL) (ℓ : ℕ) (h65 : σ.val 65 = ℓ) (h75 : σ.val 75 = ℓ - 1) (hop : σ.val qOP = 0)
    (z77 : σ.val 77 = 0) (z78 : σ.val 78 = 0) (hs161 : σ.st 161 = [] ∧ σ.sh 161 = 0) (hs162 : σ.st 162 = [] ∧ σ.sh 162 = 0) (hs163 : σ.st 163 = [] ∧ σ.sh 163 = 0) (hs164 : σ.st 164 = [] ∧ σ.sh 164 = 0) (hs165 : σ.st 165 = [] ∧ σ.sh 165 = 0) (hb : 2 * ℓ + 4 ≤ cap) :
    WExec cap prepA σ ((((((σ).sets 161 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 162 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 163 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 164 ([true, true] ++ FiltRec.reps (ℓ - 1) [true, false] ++ [false])).sets 165 ([] ++ FiltRec.reps ℓ [true, true] ++ [false])) (5 * (4 * (opU cap + 1) + 1)) :=
  WExec.mono (WExec.seq (wPRT_exec cap 161 65 (by decide) (by decide) (by decide) [] [true, false] [false] (σ) (ℓ) h65 hs161.1 hs161.2 hop z77 z78 (by simp) (by simp) (by simp) (by omega))
    (WExec.seq (wPRT_exec cap 162 65 (by decide) (by decide) (by decide) [] [true, false] [false] ((σ).sets 161 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])) (ℓ) h65 (by simp only [WState.sets_st, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact hs162.1) hs162.2 hop z77 z78 (by simp) (by simp) (by simp) (by omega))
    (WExec.seq (wPRT_exec cap 163 65 (by decide) (by decide) (by decide) [] [true, false] [false] (((σ).sets 161 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 162 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])) (ℓ) h65 (by simp only [WState.sets_st, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact hs163.1) hs163.2 hop z77 z78 (by simp) (by simp) (by simp) (by omega))
    (WExec.seq (wPRT_exec cap 164 75 (by decide) (by decide) (by decide) [true, true] [true, false] [false] ((((σ).sets 161 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 162 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 163 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])) (ℓ - 1) h75 (by simp only [WState.sets_st, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact hs164.1) hs164.2 hop z77 z78 (by simp) (by simp) (by simp) (by omega))
    ((wPRT_exec cap 165 65 (by decide) (by decide) (by decide) [] [true, true] [false] (((((σ).sets 161 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 162 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 163 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 164 ([true, true] ++ FiltRec.reps (ℓ - 1) [true, false] ++ [false])) (ℓ) h65 (by simp only [WState.sets_st, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact hs165.1) hs165.2 hop z77 z78 (by simp) (by simp) (by simp) (by omega))))))) (by omega)

def prepB : WP :=
  .seq (.wr 166 false) (.seq (.wr 167 false) (.seq (.wr 168 false) (.seq (.wr 169 false) (.seq (.wr 170 false) (wPRT 171 65 [] [false, false] [false, false])))))

theorem prepB_exec (σ : WL) (ℓ : ℕ) (h65 : σ.val 65 = ℓ) (h75 : σ.val 75 = ℓ - 1) (hop : σ.val qOP = 0)
    (z77 : σ.val 77 = 0) (z78 : σ.val 78 = 0) (hs166 : σ.st 166 = [] ∧ σ.sh 166 = 0) (hs167 : σ.st 167 = [] ∧ σ.sh 167 = 0) (hs168 : σ.st 168 = [] ∧ σ.sh 168 = 0) (hs169 : σ.st 169 = [] ∧ σ.sh 169 = 0) (hs170 : σ.st 170 = [] ∧ σ.sh 170 = 0) (hs171 : σ.st 171 = [] ∧ σ.sh 171 = 0) (hb : 2 * ℓ + 4 ≤ cap) :
    WExec cap prepB σ (((((((σ).sets 166 ([false])).sets 167 ([false])).sets 168 ([false])).sets 169 ([false])).sets 170 ([false])).sets 171 ([] ++ FiltRec.reps ℓ [false, false] ++ [false, false])) (6 * (4 * (opU cap + 1) + 1)) :=
  WExec.mono (WExec.seq (wrF_exec cap 166 (σ) hs166.1 hs166.2)
    (WExec.seq (wrF_exec cap 167 ((σ).sets 166 ([false])) (by simp only [WState.sets_st, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact hs167.1) hs167.2)
    (WExec.seq (wrF_exec cap 168 (((σ).sets 166 ([false])).sets 167 ([false])) (by simp only [WState.sets_st, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact hs168.1) hs168.2)
    (WExec.seq (wrF_exec cap 169 ((((σ).sets 166 ([false])).sets 167 ([false])).sets 168 ([false])) (by simp only [WState.sets_st, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact hs169.1) hs169.2)
    (WExec.seq (wrF_exec cap 170 (((((σ).sets 166 ([false])).sets 167 ([false])).sets 168 ([false])).sets 169 ([false])) (by simp only [WState.sets_st, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact hs170.1) hs170.2)
    ((wPRT_exec cap 171 65 (by decide) (by decide) (by decide) [] [false, false] [false, false] ((((((σ).sets 166 ([false])).sets 167 ([false])).sets 168 ([false])).sets 169 ([false])).sets 170 ([false])) (ℓ) h65 (by simp only [WState.sets_st, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact hs171.1) hs171.2 hop z77 z78 (by simp) (by simp) (by simp) (by omega)))))))) (by omega)

def prepC : WP :=
  .seq (wPRT 21 65 [] [true, false] [false]) (.seq (.wr 173 false) (.seq (.wr 174 false) (.wr 175 false)))

theorem prepC_exec (σ : WL) (ℓ : ℕ) (h65 : σ.val 65 = ℓ) (h75 : σ.val 75 = ℓ - 1) (hop : σ.val qOP = 0)
    (z77 : σ.val 77 = 0) (z78 : σ.val 78 = 0) (hs21 : σ.st 21 = [] ∧ σ.sh 21 = 0) (hs173 : σ.st 173 = [] ∧ σ.sh 173 = 0) (hs174 : σ.st 174 = [] ∧ σ.sh 174 = 0) (hs175 : σ.st 175 = [] ∧ σ.sh 175 = 0) (hb : 2 * ℓ + 4 ≤ cap) :
    WExec cap prepC σ (((((σ).sets 21 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 173 ([false])).sets 174 ([false])).sets 175 ([false])) (4 * (4 * (opU cap + 1) + 1)) :=
  WExec.mono (WExec.seq (wPRT_exec cap 21 65 (by decide) (by decide) (by decide) [] [true, false] [false] (σ) (ℓ) h65 hs21.1 hs21.2 hop z77 z78 (by simp) (by simp) (by simp) (by omega))
    (WExec.seq (wrF_exec cap 173 ((σ).sets 21 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])) (by simp only [WState.sets_st, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact hs173.1) hs173.2)
    (WExec.seq (wrF_exec cap 174 (((σ).sets 21 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 173 ([false])) (by simp only [WState.sets_st, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact hs174.1) hs174.2)
    ((wrF_exec cap 175 ((((σ).sets 21 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 173 ([false])).sets 174 ([false])) (by simp only [WState.sets_st, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact hs175.1) hs175.2))))) (by omega)

end NearCubicWires.WireExponent3_5.PrimT.W6
