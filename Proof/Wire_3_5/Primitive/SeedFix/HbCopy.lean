import Proof.Wire_3_5.Primitive.SeedFix.HbZ
import Proof.Wire_3_5.Primitive.SeedFix.TabScan
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixFetch

/-! # C4.Hb, machine part 3: skipping and copying the printed words (P3:2253-2290)

The Hb term copies its HASH factor `F_{q,e}` from PA's HASH tape (`hashTape = blockWord` of single-row FILTER entries,
`F` in `filtRefC`'s one-term one-factor form) and a cleared weight's framed bits from its table. This module has the
word programs over any streams: skip a polynomial word (`skipPolyW`), skip a HASH entry (`skipEntryW`; the entry of one
FILTER row is a fixed 9-bit head, the polynomial word, three terminators, `entry_single`), skip `k` entries
(`skipEntriesW`), and copy a framed word or a polynomial word to the end of an output stream, counting the appended
bits in a register (`copyFrameC`, `copyPolyC`, PA's `appendO` convention).

Paper quantity of the main types: the HASH factor's word `polyWord F` and the weights' words (`copyPolyC_spec`,
`copyFrameC_spec`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.ListMachine.Rec (polyWord recW monoBits atomCode coefWord termWord exprWord)
open NearCubicWires.WireExponent3_5.SeedFix (blockWord entryRec rowRec SExpr)

section Words
variable {ns nr : ℕ} (cap : ℕ)

theorem rd_app0 (pre l : List Bool) : readTapeBit (pre ++ l) pre.length = l.getD 0 false := by
  unfold readTapeBit; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp

theorem rd_app (pre l : List Bool) (k : ℕ) : readTapeBit (pre ++ l) (pre.length + k) = l.getD k false := by
  unfold readTapeBit; rw [List.getD_append_right _ _ _ _ (by omega)]; simp

/-! ## Skipping -/

/-- Skip one polynomial word: its monomial records, then its `F`. -/
def skipPolyW (S : Fin (ns + 1)) : WM ns nr := .seq (.whs S (.seq (.fwd S) (PrimT.skipFrameW S))) (.fwd S)

theorem skipPolyLoop_spec (S : Fin (ns + 1)) (rest : List Bool) :
    ∀ (ms : List (List ℕ)) (pre : List Bool) (σ : WState ns nr),
      σ.st S = pre ++ (ms.flatMap recW ++ (false :: rest)) → σ.sh S = pre.length →
      WExec cap (.whs S (.seq (.fwd S) (PrimT.skipFrameW S))) σ
        (σ.seth S (pre.length + (ms.flatMap recW).length)) ((ms.flatMap recW).length * 4 + 1)
  | [], pre, σ, hS, hh => by
    have hz : wbit σ S = false := by simp [wbit, hS, hh, rd_app0]
    have e : σ.seth S (pre.length + (([] : List (List ℕ)).flatMap recW).length) = σ := by
      simp only [List.flatMap_nil, List.length_nil, Nat.add_zero, ← hh, wseth_same]
    rw [e]; exact WExec.mono (WExec.whsF hz) (by simp)
  | m :: ms, pre, σ, hS, hh => by
    have hw : wbit σ S = true := by simp [wbit, hS, hh, rd_app0, List.flatMap_cons, recW]
    have s1 := WExec.fwd (cap := cap) S σ
    have hS1 : (σ.seth S (σ.sh S + 1)).st S = (pre ++ [true]) ++ (frame (monoBits m) ++
        (ms.flatMap recW ++ (false :: rest))) := by
      simp only [WState.seth_st, hS, List.flatMap_cons, recW]; simp
    have s2 := PrimT.skipFrame_spec cap S (pre ++ [true]) (ms.flatMap recW ++ (false :: rest)) (monoBits m)
      (σ.seth S (σ.sh S + 1)) hS1 (by simp [hh])
    rw [wseth_seth] at s2
    have ih := skipPolyLoop_spec S rest ms (pre ++ recW m) (σ.seth S ((pre ++ [true]).length + (frame (monoBits m)).length))
      (by simp [hS, List.flatMap_cons]) (by simp [recW, frame_length]; omega)
    rw [wseth_seth] at ih
    have hlen : (recW m).length = 1 + (frame (monoBits m)).length := by simp [recW]; omega
    refine WExec.cast cap (WExec.whsT hw (WExec.seq s1 s2) ih) ?_ ?_
    · congr 1; simp [List.flatMap_cons, hlen]; omega
    · simp only [List.flatMap_cons, List.length_append, hlen, frame_length] at *; omega

theorem skipPoly_spec (S : Fin (ns + 1)) (ms : List (List ℕ)) (pre rest : List Bool) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (polyWord ms ++ rest)) (hh : σ.sh S = pre.length) :
    WExec cap (skipPolyW S) σ (σ.seth S (pre.length + (polyWord ms).length)) ((polyWord ms).length * 4 + 3) := by
  have hS' : σ.st S = pre ++ (ms.flatMap recW ++ (false :: rest)) := by rw [hS]; simp [polyWord]
  have s1 := skipPolyLoop_spec cap S rest ms pre σ hS' hh
  have s2 := WExec.fwd (cap := cap) S (σ.seth S (pre.length + (ms.flatMap recW).length))
  rw [wseth_seth] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ ?_
  · congr 1; simp [polyWord]; omega
  · simp [polyWord]
    try omega

/-- The entry record of one FILTER row `[(1, [P])]`: a fixed 9-bit head, `P`'s word, three terminators. -/
theorem entry_single (P : List (List ℕ)) :
    entryRec [[((1 : ℤ), [P])]] = [true, true, true, true, false, true, true, false, true] ++ polyWord P ++
      [false, false, false] := by
  simp [entryRec, rowRec, exprWord, termWord, coefWord, frame]

/-- `k` steps forward on `S`. -/
def fwdsW (S : Fin (ns + 1)) : ℕ → WM ns nr
  | 0 => .skip
  | k + 1 => .seq (.fwd S) (fwdsW S k)

theorem fwdsW_spec (S : Fin (ns + 1)) : ∀ (k : ℕ) (σ : WState ns nr),
    WExec cap (fwdsW S k) σ (σ.seth S (σ.sh S + k)) (2 * k)
  | 0, σ => by simp only [Nat.add_zero, wseth_same]; exact WExec.skip σ
  | k + 1, σ => by
    have h1 := WExec.fwd (cap := cap) S σ
    have h2 := fwdsW_spec S k (σ.seth S (σ.sh S + 1))
    rw [wseth_seth] at h2
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
    simp only [WState.seth_sh, Function.update_self]; congr 1; omega

/-- Skip one HASH entry: the 9-bit head, the polynomial word, the three terminators. -/
def skipEntryW (S : Fin (ns + 1)) : WM ns nr := .seq (fwdsW S 9) (.seq (skipPolyW S) (fwdsW S 3))

theorem skipEntry_spec (S : Fin (ns + 1)) (P : List (List ℕ)) (pre rest : List Bool) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (entryRec [[((1 : ℤ), [P])]] ++ rest)) (hh : σ.sh S = pre.length) :
    WExec cap (skipEntryW S) σ (σ.seth S (pre.length + (entryRec [[((1 : ℤ), [P])]]).length))
      (2 * 9 + 1 + ((polyWord P).length * 4 + 3 + 1 + 2 * 3)) := by
  have s1 := fwdsW_spec cap S 9 σ
  set σ1 := σ.seth S (σ.sh S + 9) with hσ1
  have s2 := skipPoly_spec cap S P (pre ++ [true, true, true, true, false, true, true, false, true])
    ([false, false, false] ++ rest) σ1 (by simp [σ1, hS, entry_single]) (by simp [σ1, hh])
  set σ2 := σ1.seth S ((pre ++ [true, true, true, true, false, true, true, false, true]).length + (polyWord P).length)
    with hσ2
  have s3 := fwdsW_spec cap S 3 σ2
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (by omega)
  simp only [σ2, σ1, wseth_seth, WState.seth_sh, Function.update_self, entry_single]
  congr 1; simp; omega

end Words

/-! ## Copying to the end of an output, counted -/

section Copy
variable {ns nr : ℕ} (cap : ℕ)

theorem frameP_length (y : List Bool) : (frameP y).length = 2 * y.length := by
  induction y with
  | nil => rfl
  | cons b y ih => simp [frameP] at ih ⊢; omega

/-- Close an equality of word states component by component. -/
syntax "wst" : tactic
macro_rules
  | `(tactic| wst) => `(tactic| (refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | (funext x
           simp only [appendO_st, appendO_sh, appendO_val, appendO_cell, WState.setv_val, WState.seth_val,
             WState.sets_val, WState.setv_sh, WState.seth_sh, WState.sets_sh, WState.setv_st, WState.seth_st,
             WState.sets_st, Function.update_apply]
           split_ifs <;> subst_vars <;> (try simp [frameP, frameP_length, frame_length]) <;> (try omega))
        | rfl
        | simp))

theorem emitC_app (O : Fin (ns + 1)) (OP : Fin nr) (b : Bool) (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length)
    (hc : σ.val OP < cap) : WExec cap (emitC O OP b) σ (appendO σ O OP [b]) 7 := by
  have h := emitC_spec cap O OP b σ hO hc
  simpa [appendO] using h

theorem appendO_seth_comm (σ : WState ns nr) (O S : Fin (ns + 1)) (h : S ≠ O) (OP : Fin nr) (u : List Bool) (x : ℕ) :
    appendO (σ.seth S x) O OP u = (appendO σ O OP u).seth S x := by
  apply WState.eq
  · funext j; simp only [appendO, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl
  · rfl
  · rfl

/-- The body of the framed-word copy: one pair `T b` of `S`, emitted on `O`. -/
def copyPairC (S O : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (.fwd S) (.seq (emitC O OP true) (.seq (.ifs S (emitC O OP true) (emitC O OP false)) (.fwd S)))

/-- **Copy one framed word** from `S` (at its head) to the end of `O`, counting in `OP`. -/
def copyFrameC (S O : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (.whs S (copyPairC S O OP)) (.seq (.fwd S) (emitC O OP false))

theorem copyPairsLoop_spec (S O : Fin (ns + 1)) (hSO : S ≠ O) (OP : Fin nr) (rest : List Bool) :
    ∀ (y pre : List Bool) (σ : WState ns nr), σ.st S = pre ++ (frameP y ++ (false :: rest)) → σ.sh S = pre.length →
      σ.sh O = (σ.st O).length → σ.val OP + 2 * y.length ≤ cap →
      WExec cap (.whs S (copyPairC S O OP)) σ (appendO (σ.seth S (pre.length + 2 * y.length)) O OP (frameP y))
        (22 * y.length + 1)
  | [], pre, σ, hS, hh, _, _ => by
    have hz : wbit σ S = false := by simp [wbit, hS, hh, rd_app0, frameP]
    have e : appendO (σ.seth S (pre.length + 2 * ([] : List Bool).length)) O OP (frameP []) = σ := by
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, ← hh, wseth_same]; simp [frameP, appendO_nil]
    rw [e]; exact WExec.whsF hz
  | b :: y, pre, σ, hS, hh, hO, hc => by
    simp only [List.length_cons] at hc
    have hOS : O ≠ S := fun e => hSO e.symm
    have hw : wbit σ S = true := by simp [wbit, hS, hh, rd_app0, frameP]
    have s1 := WExec.fwd (cap := cap) S σ
    set σ1 := σ.seth S (σ.sh S + 1) with hσ1
    have s2 := emitC_app cap O OP true σ1 (by simp [σ1, Function.update_of_ne hOS, hO]) (by simp [σ1]; omega)
    set σ2 := appendO σ1 O OP [true] with hσ2
    have hb : wbit σ2 S = b := by
      simp only [wbit, σ2, σ1, appendO, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh,
        WState.seth_sh, WState.sets_sh, Function.update_of_ne hSO, Function.update_self, hS, hh]
      have := rd_app pre (frameP (b :: y) ++ false :: rest) 1
      simpa [frameP] using this
    have s3 : WExec cap (.ifs S (emitC O OP true) (emitC O OP false)) σ2 (appendO σ2 O OP [b]) 8 := by
      have ho2 : σ2.sh O = (σ2.st O).length := by
        simp [σ2, σ1, appendO, Function.update_of_ne hOS, hO]
      have hc2 : σ2.val OP < cap := by simp [σ2, σ1, appendO]; omega
      cases b
      · exact WExec.ifsF hb (emitC_app cap O OP false σ2 ho2 hc2)
      · exact WExec.ifsT hb (emitC_app cap O OP true σ2 ho2 hc2)
    set σ3 := appendO σ2 O OP [b] with hσ3
    have s4 := WExec.fwd (cap := cap) S σ3
    set σ4 := σ3.seth S (σ3.sh S + 1) with hσ4
    have h4S : σ4.st S = (pre ++ [true, b]) ++ (frameP y ++ (false :: rest)) := by
      simp [σ4, σ3, σ2, σ1, appendO, Function.update_of_ne hSO, hS, frameP]
    have h4h : σ4.sh S = (pre ++ [true, b]).length := by
      simp [σ4, σ3, σ2, σ1, appendO, Function.update_of_ne hSO, hh]
    have h4O : σ4.sh O = (σ4.st O).length := by
      simp [σ4, σ3, σ2, σ1, appendO, Function.update_of_ne hOS, hO]
      try omega
    have h4c : σ4.val OP + 2 * y.length ≤ cap := by simp [σ4, σ3, σ2, σ1, appendO]; omega
    have ih := copyPairsLoop_spec S O hSO OP rest y (pre ++ [true, b]) σ4 h4S h4h h4O h4c
    refine WExec.cast cap (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ih) ?_ (by simp; omega)
    rw [hσ4, hσ3, hσ2, hσ1]
    wst

theorem copyFrameC_spec (S O : Fin (ns + 1)) (hSO : S ≠ O) (OP : Fin nr) (pre y rest : List Bool) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (frame y ++ rest)) (hh : σ.sh S = pre.length) (hO : σ.sh O = (σ.st O).length)
    (hc : σ.val OP + (frame y).length ≤ cap) :
    WExec cap (copyFrameC S O OP) σ (appendO (σ.seth S (pre.length + (frame y).length)) O OP (frame y))
      (11 * (frame y).length) := by
  have hOS : O ≠ S := fun e => hSO e.symm
  have hS' : σ.st S = pre ++ (frameP y ++ (false :: rest)) := by rw [hS, frame_eq_frameP]; simp
  have hfl : (frame y).length = 2 * y.length + 1 := frame_length y
  have s1 := copyPairsLoop_spec cap S O hSO OP rest y pre σ hS' hh hO (by omega)
  set σ1 := appendO (σ.seth S (pre.length + 2 * y.length)) O OP (frameP y) with hσ1
  have s2 := WExec.fwd (cap := cap) S σ1
  set σ2 := σ1.seth S (σ1.sh S + 1) with hσ2
  have s3 := emitC_app cap O OP false σ2
    (by simp [σ2, σ1, appendO, Function.update_of_ne hOS, hO]) (by simp [σ2, σ1, appendO, frameP_length]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (by omega)
  rw [hσ2, hσ1, frame_eq_frameP]
  wst

end Copy

section CopyPoly
variable {ns nr : ℕ} (cap : ℕ)

/-- The body of the polynomial copy: one monomial record `T frame(m)`. -/
def copyRecC (S O : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (.fwd S) (.seq (emitC O OP true) (copyFrameC S O OP))

/-- **Copy one polynomial word** from `S` (at its head) to the end of `O`, counting in `OP`. -/
def copyPolyC (S O : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (.whs S (copyRecC S O OP)) (.seq (.fwd S) (emitC O OP false))

theorem copyRecsLoop_spec (S O : Fin (ns + 1)) (hSO : S ≠ O) (OP : Fin nr) (rest : List Bool) :
    ∀ (ms : List (List ℕ)) (pre : List Bool) (σ : WState ns nr),
      σ.st S = pre ++ (ms.flatMap recW ++ (false :: rest)) → σ.sh S = pre.length →
      σ.sh O = (σ.st O).length → σ.val OP + (ms.flatMap recW).length ≤ cap →
      WExec cap (.whs S (copyRecC S O OP))
        σ (appendO (σ.seth S (pre.length + (ms.flatMap recW).length)) O OP (ms.flatMap recW))
        (12 * (ms.flatMap recW).length + 1)
  | [], pre, σ, hS, hh, _, _ => by
    have hz : wbit σ S = false := by simp [wbit, hS, hh, rd_app0]
    have e : appendO (σ.seth S (pre.length + (([] : List (List ℕ)).flatMap recW).length)) O OP
        (([] : List (List ℕ)).flatMap recW) = σ := by
      simp only [List.flatMap_nil, List.length_nil, Nat.add_zero, ← hh, wseth_same, appendO_nil]
    rw [e]; exact WExec.mono (WExec.whsF hz) (by simp)
  | m :: ms, pre, σ, hS, hh, hO, hc => by
    have hOS : O ≠ S := fun e => hSO e.symm
    have hrec : recW m = true :: frame (monoBits m) := rfl
    have hlen : (recW m).length = (frame (monoBits m)).length + 1 := by rw [hrec]; simp
    have hfl : (frame (monoBits m)).length = 2 * (monoBits m).length + 1 := frame_length _
    simp only [List.flatMap_cons, List.length_append] at hc
    have hw : wbit σ S = true := by simp [wbit, hS, hh, rd_app0, List.flatMap_cons, recW]
    have s1 := WExec.fwd (cap := cap) S σ
    set σ1 := σ.seth S (σ.sh S + 1) with hσ1
    have s2 := emitC_app cap O OP true σ1 (by simp [σ1, Function.update_of_ne hOS, hO]) (by simp [σ1]; omega)
    set σ2 := appendO σ1 O OP [true] with hσ2
    have s3 := copyFrameC_spec cap S O hSO OP (pre ++ [true]) (monoBits m) (ms.flatMap recW ++ (false :: rest)) σ2
      (by simp [σ2, σ1, appendO, Function.update_of_ne hSO, hS, List.flatMap_cons, recW])
      (by simp [σ2, σ1, appendO, Function.update_of_ne hSO, hh])
      (by simp [σ2, σ1, appendO, Function.update_of_ne hOS, hO])
      (by simp only [hσ2, hσ1, appendO_val, WState.seth_val, Function.update_self, List.length_singleton]
          omega)
    set σ3 := appendO (σ2.seth S ((pre ++ [true]).length + (frame (monoBits m)).length)) O OP (frame (monoBits m))
      with hσ3
    have ih := copyRecsLoop_spec S O hSO OP rest ms (pre ++ recW m) σ3
      (by simp [σ3, σ2, σ1, appendO, Function.update_of_ne hSO, hS, List.flatMap_cons])
      (by simp [σ3, σ2, σ1, appendO, Function.update_of_ne hSO, hrec]; try omega)
      (by simp [σ3, σ2, σ1, appendO, Function.update_of_ne hOS, hO]; try omega)
      (by simp only [hσ3, hσ2, hσ1, appendO_val, WState.seth_val, Function.update_self, List.length_singleton]
          omega)
    refine WExec.cast cap (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 s3)) ih) ?_ ?_
    · rw [hσ3, hσ2, hσ1]
      simp only [List.flatMap_cons, hrec]
      wst
      all_goals omega
    · simp only [List.flatMap_cons, List.length_append, hlen]; omega

theorem copyPolyC_spec (S O : Fin (ns + 1)) (hSO : S ≠ O) (OP : Fin nr) (ms : List (List ℕ)) (pre rest : List Bool)
    (σ : WState ns nr) (hS : σ.st S = pre ++ (polyWord ms ++ rest)) (hh : σ.sh S = pre.length)
    (hO : σ.sh O = (σ.st O).length) (hc : σ.val OP + (polyWord ms).length ≤ cap) :
    WExec cap (copyPolyC S O OP) σ (appendO (σ.seth S (pre.length + (polyWord ms).length)) O OP (polyWord ms))
      (12 * (polyWord ms).length + 10) := by
  have hOS : O ≠ S := fun e => hSO e.symm
  have hS' : σ.st S = pre ++ (ms.flatMap recW ++ (false :: rest)) := by rw [hS]; simp [polyWord]
  have hpl : (polyWord ms).length = (ms.flatMap recW).length + 1 := by simp [polyWord]
  have s1 := copyRecsLoop_spec cap S O hSO OP rest ms pre σ hS' hh hO (by omega)
  set σ1 := appendO (σ.seth S (pre.length + (ms.flatMap recW).length)) O OP (ms.flatMap recW) with hσ1
  have s2 := WExec.fwd (cap := cap) S σ1
  set σ2 := σ1.seth S (σ1.sh S + 1) with hσ2
  have s3 := emitC_app cap O OP false σ2 (by simp [σ2, σ1, appendO, Function.update_of_ne hOS, hO])
    (by simp only [hσ2, hσ1, appendO_val, WState.seth_val, Function.update_self]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (by omega)
  rw [hσ2, hσ1]
  simp only [polyWord]
  wst

end CopyPoly

end NearCubicWires.WireExponent3_5.PrimT.HbM
