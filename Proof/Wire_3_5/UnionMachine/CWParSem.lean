import Proof.Wire_3_5.UnionMachine.CWParCore

/-! # C6 front, U5, the code writers: the parity writer writes the parity atom's code

"Constants, complemented atoms, and the systematic encoding parity are permitted at the same fixed description
envelope" (P3:3092-3094): the union setup's encoding parity of a variable with support `S` is `unionParityAtom m q S`. On the bitmap of `S` the parity writer's core writes
`sufCode (accOf (WLv l) (P3v l) k) k topv tagv`; this module identifies it with the atom's code in each class mode:
* the shared codes: `WLv_eq` (the bottoms' weight list), `SBv_eq` (their support list);
* **`codeB_eq`**: the `j`-th bottom's code is base's `encodeSupportedNormalizedGate (thresholdParityBottomGate S j)`;
* `BL_eq` (the bottoms' list), `topS_eq` (the `SYM∘THR` top table), `topT_eq` (the `THR∘THR` top gate);
* **`sym_code`**, **`thr_code`**: the whole code is `Mode.code m (unionParityAtom m q S)`.

Paper quantity of the main types: the code of the encoding parity atom of each class mode. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParSem
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.CanonicalBinary
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
open NearCubicWires.WireExponent3_5.UnionMachine.CWParCnt NearCubicWires.WireExponent3_5.UnionMachine.CWParGen
open NearCubicWires.WireExponent3_5.UnionMachine.CWParTop NearCubicWires.WireExponent3_5.UnionMachine.CWParRound
open NearCubicWires.WireExponent3_5.UnionMachine.CWParPre (WLv SBv P3v wlGs sbGs)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParTops (topSv topTv altV alltV altGs)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParSuf (sufCode)

variable {q : ℕ}

/-- The bitmap of a support. -/
def bmp (S : Finset (Fin q)) : List Bool := List.ofFn fun i => decide (i ∈ S)

theorem count_ofFn_true : ∀ (t : ℕ) (y : Fin t → Bool),
    (List.ofFn y).count true = (Finset.univ.filter fun k => y k = true).card
  | 0, y => by simp
  | t + 1, y => by
    rw [List.ofFn_succ, List.count_cons, count_ofFn_true t, Finset.card_filter, Finset.card_filter,
      Fin.sum_univ_succ]
    cases y 0 <;> simp [add_comm]

theorem count_bmp (S : Finset (Fin q)) : (bmp S).count true = S.card := by
  unfold bmp; rw [count_ofFn_true]; congr 1; ext i; simp

theorem value_w9 : RadixSemantics.value w9 = 9 := by simp [w9, RadixSemantics.value]
theorem value_w10 : RadixSemantics.value w10 = 10 := by simp [w10, RadixSemantics.value]
theorem value_f : RadixSemantics.value [false] = 0 := by simp [RadixSemantics.value]
theorem value_b (b : Bool) : RadixSemantics.value [b] = boolCode b := by
  cases b <;> simp [RadixSemantics.value, boolCode]

theorem encodeInt_one : encodeInt 1 = 9 := by
  simp [encodeInt, encodeNat, encodeBits, encodeBoolList, encodeBalancedList, boolCode, Nat.pair]
theorem encodeInt_zero : encodeInt 0 = 0 := by
  simp [encodeInt, encodeNat, encodeBits, encodeBoolList, encodeBalancedList, Nat.pair]
theorem encodeInt_neg_one : encodeInt (-1) = 10 := by
  simp [encodeInt, encodeNat, encodeBits, encodeBoolList, encodeBalancedList, boolCode, Nat.pair]
theorem encodeNat_zero : encodeNat 0 = 0 := by simp [encodeNat, encodeBits, encodeBoolList, encodeBalancedList]
theorem encodeNat_one : encodeNat 1 = 3 := by
  simp [encodeNat, encodeBits, encodeBoolList, encodeBalancedList, boolCode, Nat.pair]

theorem code_eq (gs : List (List Bool)) : PCPTraversal.code gs = encodeBalancedList (gs.map RadixSemantics.value) := rfl

theorem ofFn_range {α : Type} : ∀ (k : ℕ) (g : ℕ → α), List.ofFn (fun j : Fin k => g j.val) = (List.range k).map g
  | 0, g => rfl
  | k + 1, g => by
    rw [List.ofFn_succ', List.range_succ, List.map_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.concat_eq_append]
    rw [ofFn_range k g]; simp

/-! ## The shared codes -/

theorem WLv_eq (S : Finset (Fin q)) :
    WLv (bmp S) = encodeIntList (List.ofFn fun i : Fin q => if i ∈ S then (1 : ℤ) else 0) := by
  unfold WLv encodeIntList
  rw [code_eq]
  congr 1
  unfold wlGs bmp
  rw [List.map_map, List.map_ofFn, List.map_ofFn]
  congr 1; funext i
  by_cases h : i ∈ S
  · simp [h, value_w9, encodeInt_one]
  · simp [h, value_f, encodeInt_zero]

theorem SBv_eq (S : Finset (Fin q)) : SBv (bmp S) = encodeBoolList (List.ofFn fun i : Fin q => decide (i ∈ S)) := by
  unfold SBv encodeBoolList
  rw [code_eq]
  congr 1
  unfold sbGs bmp
  rw [List.map_map, List.map_ofFn, List.map_ofFn]
  congr 1
  try (funext i; simp [value_b])

theorem encodeInt_succ (j : ℕ) : encodeInt ((j : ℤ) + 1) = Nat.pair 0 (encodeNat (j + 1)) := by
  unfold encodeInt
  rw [if_neg (by omega)]
  congr 2
  try omega

/-- **The `j`-th bottom's code** is base's code of the staircase bottom `[Σ_{i∈S} x_i ≥ j+1]`. -/
theorem codeB_eq (S : Finset (Fin q)) (j : Fin S.card) :
    codeB (WLv (bmp S)) (P3v (bmp S)) j = encodeSupportedNormalizedGate (thresholdParityBottomGate S j) := by
  unfold codeB cons P3v cons encodeSupportedNormalizedGate
  rw [WLv_eq, SBv_eq]
  show _ = encodeTaggedList [_, encodeInt ((j.val : ℤ) + 1), _]
  rw [encodeInt_succ]
  rfl

/-- **The bottoms' list.** -/
theorem BL_eq (S : Finset (Fin q)) :
    PCPTraversal.code (accOf (WLv (bmp S)) (P3v (bmp S)) S.card) =
      encodeBalancedList (List.ofFn fun j : Fin S.card => encodeSupportedNormalizedGate (thresholdParityBottomGate S j)) := by
  rw [code_eq]
  congr 1
  unfold accOf
  rw [List.map_map]
  have e : ∀ j : Fin S.card, (RadixSemantics.value ∘ fun i => (codeB (WLv (bmp S)) (P3v (bmp S)) i).bits) j.val =
      encodeSupportedNormalizedGate (thresholdParityBottomGate S j) := by
    intro j
    simp only [Function.comp_apply, CanonicalPositiveOutput.nat_bits_value]
    exact codeB_eq S j
  rw [← ofFn_range]
  exact congrArg List.ofFn (funext e)

/-! ## The tops -/

theorem topS_eq (k : ℕ) : topSv k = encodeBoolList (List.ofFn fun c : Fin (k + 1) => decide (Odd c.val)) := by
  unfold topSv encodeBoolList
  rw [code_eq]
  congr 1
  unfold oddL
  rw [List.map_map, List.map_map, ← ofFn_range (k + 1), List.map_ofFn]
  congr 1
  try (funext c; simp [value_b])

theorem altV_eq (k : ℕ) : altV k = encodeIntList (List.ofFn fun i : Fin k => if Even i.val then (1 : ℤ) else -1) := by
  unfold altV encodeIntList altGs
  rw [code_eq, List.map_map, ← ofFn_range k, List.map_ofFn]
  congr 1
  congr 1; funext i
  by_cases h : Even i.val
  · simp [h, value_w9, encodeInt_one]
  · simp [h, value_w10, encodeInt_neg_one]

theorem alltV_eq (k : ℕ) : alltV k = encodeBoolList (List.ofFn fun i : Fin k => decide (i ∈ (Finset.univ : Finset (Fin k)))) := by
  unfold alltV encodeBoolList
  rw [code_eq, List.map_replicate, value_b]
  congr 1
  rw [List.map_ofFn]
  simp [Function.comp_def, List.ofFn_const]

theorem topT_eq (k : ℕ) : topTv k = encodeSupportedNormalizedGate (thresholdParityTopGate k) := by
  unfold topTv cons encodeSupportedNormalizedGate
  rw [altV_eq, alltV_eq, show (9 : ℕ) = encodeInt 1 from encodeInt_one.symm]
  rfl

/-! ## The whole codes -/

theorem sufCode_eq (L : List (List Bool)) (k t g : ℕ) :
    sufCode L k t g = encodeTaggedList [g, encodeNat k, PCPTraversal.code L, t] := rfl

/-- **The `SYM∘THR` parity atom's code.** -/
theorem sym_code (S : Finset (Fin q)) :
    sufCode (accOf (WLv (bmp S)) (P3v (bmp S)) (bmp S |>.count true)) ((bmp S).count true)
      (topSv ((bmp S).count true)) 0 = Mode.code .sym (Transfer.unionParityAtom .sym q S) := by
  rw [count_bmp, sufCode_eq, BL_eq, topS_eq, show (0 : ℕ) = encodeNat symmetricCircuitFamilyTag from encodeNat_zero.symm]
  rfl

/-- **The `THR∘THR` parity atom's code.** -/
theorem thr_code (S : Finset (Fin q)) :
    sufCode (accOf (WLv (bmp S)) (P3v (bmp S)) (bmp S |>.count true)) ((bmp S).count true)
      (topTv ((bmp S).count true)) 3 = Mode.code .thr (Transfer.unionParityAtom .thr q S) := by
  rw [count_bmp, sufCode_eq, BL_eq, topT_eq, show (3 : ℕ) = encodeNat thresholdCircuitFamilyTag from encodeNat_one.symm]
  rfl

end NearCubicWires.WireExponent3_5.UnionMachine.CWParSem
