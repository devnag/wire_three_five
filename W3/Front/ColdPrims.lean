import W3.Front.Main
import Codec.Frame
import Platform.RecLoopSum
import Codec.FieldNum

/-!
# The cold front end, part 0: word-level primitives of the cold front end

* `zeroScan S Z`: on a framed tail `marks rest ++ false :: _` at the head of `S`, `Z += (count of 1s in rest)`
  (paper "malformed or noncanonical": a field may carry zero high bits; only its value counts, so the machine
  checks that every bit past the code bound is `0` and decodes the bounded prefix — `value_prefix`).
* `truncField FB TMP FBP OP L LC Z`: from `frame b` on `FB`, `FBP := frame (prefixBits b ℓ)` (`ℓ = L`) and
  `Z += count of 1s in b.drop ℓ`.
* `framedOnes O T U OP`: `O := frame 1^m` from `T = m` (the cold decoder's padding word).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 400000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairOrdinary.RadixSemantics (value)

namespace W3.NearCubicWires.RepairSource.Outer3.Front

variable {ns nr : ℕ} (cap : ℕ)

/-- Count the `1`s of a marked tail (head on a marker cell). -/
def zeroScan (S : Fin (ns + 1)) (Z : Fin nr) : WMX ns nr :=
  .whs S (.seq (WMX.fwd S) (.seq (.ifs S (WMX.inc Z) WMX.skip) (WMX.fwd S)))

theorem zeroScan_spec (S : Fin (ns + 1)) (Z : Fin nr) :
    ∀ (rest pre tail : List Bool) (σ : WState ns nr), σ.st S = pre ++ marks rest ++ false :: tail →
      σ.sh S = pre.length → σ.val Z + rest.length < cap + 1 →
      WXExec cap (zeroScan S Z) σ ((σ.seth S (pre.length + 2 * rest.length)).setv Z (σ.val Z + rest.count true))
        (10 * rest.length + 1)
  | [], pre, tail, σ, hst, hsh, _ => by
    have hw : wbit σ S = false := by
      unfold wbit; rw [hst, hsh]; simp [readTapeBit, marks]
    refine WXExec.cast cap (WXExec.whsF hw) ?_ le_rfl
    apply WState.eq
    · funext j; by_cases hj : j = S
      · subst hj; simp [hsh]
      · simp [Function.update_of_ne hj]
    · rfl
    · simp
    · rfl
  | b :: rest, pre, tail, σ, hst, hsh, hc => by
    have hw : wbit σ S = true := by
      unfold wbit; rw [hst, hsh]; simp [readTapeBit, marks]
    have e1 := WXExec.fwd (cap := cap) S σ
    set σ1 := σ.seth S (σ.sh S + 1) with hσ1
    have hb : wbit σ1 S = b := by
      unfold wbit; simp only [hσ1, WState.seth_st, WState.seth_sh, Function.update_self]
      rw [hst, hsh]; simp [readTapeBit, marks]
    have e2 : WXExec cap (.ifs S (WMX.inc Z) WMX.skip) σ1 (σ1.setv Z (σ1.val Z + b.toNat)) (b.toNat * 3 + 1) := by
      cases b
      · refine WXExec.cast cap (WXExec.ifsF hb (WXExec.skip cap σ1)) ?_ (by simp)
        simp [wsetv_same]
      · refine WXExec.cast cap (WXExec.ifsT hb (WXExec.inc (cap := cap) Z σ1 (by simp [hσ1]; simp at hc; omega)))
          ?_ (by simp)
        simp
    set σ2 := σ1.setv Z (σ1.val Z + b.toNat) with hσ2
    have e3 := WXExec.fwd (cap := cap) S σ2
    set σ3 := σ2.seth S (σ2.sh S + 1) with hσ3
    have hrest := zeroScan_spec S Z rest (pre ++ [true, b]) tail σ3
      (by simp only [hσ3, hσ2, hσ1, WState.seth_st, WState.setv_st]; rw [hst]; simp [marks])
      (by simp [hσ3, hσ2, hσ1, hsh])
      (by simp only [hσ3, hσ2, hσ1, WState.seth_val, WState.setv_val, Function.update_self]
          simp at hc; cases b <;> simp <;> omega)
    refine WXExec.cast cap (WXExec.whsT hw (WXExec.seq e1 (WXExec.seq e2 e3)) hrest) ?_ ?_
    · apply WState.eq
      · funext j; by_cases hj : j = S
        · subst hj; simp [hσ3, hσ2, hσ1, hsh]; omega
        · simp [hσ3, hσ2, hσ1, Function.update_of_ne hj]
      · rfl
      · funext r; by_cases hr : r = Z
        · subst hr; simp [hσ3, hσ2, hσ1, List.count_cons]; cases b <;> simp <;> omega
        · simp [hσ3, hσ2, hσ1, Function.update_of_ne hr]
      · rfl
    · cases b <;> simp <;> omega

/-- `FBP := frame (prefixBits b ℓ)` from `FB = frame b`, and `Z += #1s of b past ℓ` (`ℓ` in `L`; scratch `TMP`,
`OP`, `LC`, `D`). -/
def truncField (FB TMP FBP : Fin (ns + 1)) (OP L LC Z D : Fin nr) : WMX ns nr :=
  .seq (.wm (Codec.dupR L LC D))
  (.seq (.wm (Codec.unframeW FB TMP OP LC))
  (.seq (zeroScan FB Z)
  (.seq (.wm (WM.rewind TMP OP))
  (.seq (.wm (Codec.dupR L LC D))
  (.seq (.wm (Codec.frameStream TMP FBP OP LC))
  (.seq (.wm (emitC FBP OP false))
   (.wm (WM.rewind FBP OP))))))))

def truncCost (ℓ m : ℕ) : ℕ := 200 * (ℓ + m + 1)

theorem marks_take_drop (b : List Bool) (ℓ : ℕ) :
    RepairOrdinary.frame b = marks (b.take ℓ) ++ marks (b.drop ℓ) ++ false :: [] := by
  rw [Codec.frame_eq_marks, ← Streaming.marks_append, List.take_append_drop]

theorem truncField_spec (FB TMP FBP : Fin (ns + 1)) (h1 : FB ≠ TMP) (h2 : FB ≠ FBP) (h3 : TMP ≠ FBP)
    (OP L LC Z D : Fin nr) (hR : [OP, L, LC, Z, D].Nodup) (b : List Bool) (ℓ : ℕ) (σ : WState ns nr)
    (hFB : σ.st FB = RepairOrdinary.frame b) (hFBh : σ.sh FB = 0) (hT : σ.st TMP = []) (hTh : σ.sh TMP = 0)
    (hP : σ.st FBP = []) (hPh : σ.sh FBP = 0) (hOP : σ.val OP = 0) (hL : σ.val L = ℓ) (hLC : σ.val LC = 0)
    (hD : σ.val D = 0) (hcap : 4 * ℓ + 2 * b.length + σ.val Z + 8 ≤ cap) :
    ∃ τ, WXExec cap (truncField FB TMP FBP OP L LC Z D) σ τ (truncCost ℓ b.length) ∧
      τ.st FBP = RepairOrdinary.frame (Codec.prefixBits b ℓ) ∧ τ.sh FBP = 0 ∧
      τ.val Z = σ.val Z + (b.drop ℓ).count true ∧ SameExcept σ τ [FB, TMP, FBP] [Z] := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR
  obtain ⟨⟨oL, oLC, oZ, oD⟩, ⟨lLC, lZ, lD⟩, ⟨cZ, cD⟩, zD⟩ := hR
  have hpl : (Codec.prefixBits b ℓ).length = ℓ := by simp [Codec.prefixBits]
  -- 1. `LC := ℓ`
  have e1 := Codec.dupR_spec cap L LC D lLC lD cD σ hD (by rw [hL, hLC]; omega)
  rw [hLC, hL, Nat.zero_add] at e1
  set σ1 := σ.setv LC ℓ with hσ1
  -- 2. unframe `ℓ` cells
  have e2 := Codec.unframeW_spec cap FB TMP h1 OP LC (Ne.symm oLC) b ℓ σ1 (by simp [hσ1, hFB]) (by simp [hσ1, hFBh])
    (by simp [hσ1, hT, hTh]) (by simp [hσ1]) (by omega) (by simp [hσ1, Function.update_of_ne oLC, hOP]; omega)
  set σ2 := ((NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO σ1 TMP OP (Codec.prefixBits b ℓ)).seth FB
    (2 * min ℓ b.length)).setv LC 0 with hσ2
  -- 3. scan
  have hlt : (marks (b.take ℓ)).length = 2 * min ℓ b.length := by simp [Streaming.marks_length]
  have e3 := zeroScan_spec cap FB Z (b.drop ℓ) (marks (b.take ℓ)) [] σ2
    (by simp only [hσ2, WState.setv_st, WState.seth_st, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO_st,
          Function.update_of_ne h1, hσ1, WState.setv_st, hFB]
        exact marks_take_drop b ℓ)
    (by simp [hσ2, hlt])
    (by
      have vZ : σ2.val Z = σ.val Z := by
        simp [hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply, Ne.symm cZ,
          Ne.symm oZ]
      rw [vZ]; have : (b.drop ℓ).length ≤ b.length := by simp
      omega)
  set σ3 := (σ2.seth FB ((marks (b.take ℓ)).length + 2 * (b.drop ℓ).length)).setv Z
    (σ2.val Z + (b.drop ℓ).count true) with hσ3
  have v3OP : σ3.val OP = ℓ := by
    simp [hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply, oZ, oLC, hOP,
      hpl]
  -- 4. rewind `TMP`
  have e4 := wrewind_spec cap TMP OP ℓ σ3 v3OP (by omega)
  have h3TMPh : σ3.sh TMP = ℓ := by
    simp [hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply, h1, Ne.symm h1,
      hTh, hpl]
  rw [h3TMPh, Nat.sub_self] at e4
  set σ4 := (σ3.setv OP 0).seth TMP 0 with hσ4
  -- 5. `LC := ℓ`
  have v4LC : σ4.val LC = 0 := by
    simp [hσ4, hσ3, hσ2, Function.update_apply, Ne.symm cZ, cZ, oLC, Ne.symm oLC]
  have v4D : σ4.val D = 0 := by
    simp [hσ4, hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply,
      Ne.symm oD, Ne.symm zD, Ne.symm cD, hD]
  have v4L : σ4.val L = ℓ := by
    simp [hσ4, hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply,
      Ne.symm oL, lZ, lLC, hL]
  have e5 := Codec.dupR_spec cap L LC D lLC lD cD σ4 v4D (by rw [v4L, v4LC]; omega)
  rw [v4LC, v4L, Nat.zero_add] at e5
  set σ5 := σ4.setv LC ℓ with hσ5
  -- 6. frame the prefix
  have h5TMP : σ5.st TMP = [] ++ Codec.prefixBits b ℓ ++ [] := by
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply,
      h1, hT]
  have h5P : σ5.st FBP = [] := by
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply,
      h2.symm, h3.symm, hP]
  have h5Ph : σ5.sh FBP = 0 := by
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply,
      Ne.symm h2, Ne.symm h3, hPh]
  have v5OP : σ5.val OP = 0 := by simp [hσ5, hσ4, Function.update_apply, oLC]
  have e6 := Codec.frameStream_spec cap TMP FBP h3 OP LC (Ne.symm oLC) (Codec.prefixBits b ℓ) [] [] σ5 h5TMP
    (by simp [hσ5, hσ4]) (by rw [h5P, h5Ph]; rfl) (by simp [hσ5, hpl]) (by rw [hpl]; omega)
    (by rw [v5OP, hpl]; omega)
  set σ6 := ((NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO σ5 FBP OP (marks (Codec.prefixBits b ℓ))).setv
    LC 0).seth TMP (([] : List Bool).length + (Codec.prefixBits b ℓ).length) with hσ6
  -- 7. the closing `false`
  have e7 := emitC_spec cap FBP OP false σ6
    (by simp [hσ6, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply, Ne.symm h3, h5P,
        h5Ph])
    (by simp [hσ6, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply, oLC, v5OP, hpl];
        omega)
  set σ7 := ((σ6.sets FBP (σ6.st FBP ++ [false])).seth FBP (σ6.sh FBP + 1)).setv OP (σ6.val OP + 1) with hσ7
  have v7OP : σ7.val OP = 2 * ℓ + 1 := by
    simp [hσ7, hσ6, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply, oLC, v5OP, hpl,
      Streaming.marks_length]
  have h7Ph : σ7.sh FBP = 2 * ℓ + 1 := by
    simp [hσ7, hσ6, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply, Ne.symm h3, h5Ph,
      hpl, Streaming.marks_length]
  -- 8. rewind `FBP`
  have e8 := wrewind_spec cap FBP OP (2 * ℓ + 1) σ7 v7OP (by omega)
  rw [h7Ph, Nat.sub_self] at e8
  set σ8 := (σ7.setv OP 0).seth FBP 0 with hσ8
  refine ⟨σ8, WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq (WXExec.wm e2) (WXExec.seq e3
    (WXExec.seq (WXExec.wm e4) (WXExec.seq (WXExec.wm e5) (WXExec.seq (WXExec.wm e6) (WXExec.seq (WXExec.wm e7)
      (WXExec.wm e8)))))))) ?_, ?_, ?_, ?_, ?_⟩
  · unfold truncCost
    have hd : (b.drop ℓ).length ≤ b.length := by simp
    simp only [hpl]
    omega
  · simp [hσ8, hσ7, hσ6, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply, h5P,
      Codec.frame_eq_marks]
  · simp [hσ8]
  · simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply,
      oZ, cZ, Ne.symm oZ, Ne.symm cZ, lZ]
    simp [hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply, Ne.symm cZ,
      Ne.symm oZ]
  · refine ⟨fun x hx => ?_, fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      obtain ⟨x1, x2, x3⟩ := hx
      constructor
      · simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO,
          Function.update_apply, x1, x2, x3]
      · simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO,
          Function.update_apply, x1, x2, x3]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO,
        Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO]

/-- `O := frame 1^m` (`m` in `T`, kept; scratch `U`, `OP` at `0`). -/
def framedOnes (O : Fin (ns + 1)) (T U OP : Fin nr) : WMX ns nr :=
  .seq (.wm (Codec.onesLoop T U O OP)) (.seq (.wm (emitC O OP false)) (.seq (.wm (WM.rewind O OP))
    (.wm (WM.move U T))))

theorem framedOnes_spec (O : Fin (ns + 1)) (T U OP : Fin nr) (hTU : T ≠ U) (hTO : T ≠ OP) (hUO : U ≠ OP)
    (m : ℕ) (σ : WState ns nr) (hO : σ.st O = []) (hOh : σ.sh O = 0) (hT : σ.val T = m) (hU : σ.val U = 0)
    (hOP : σ.val OP = 0) (hc : 2 * m + 2 ≤ cap) :
    WXExec cap (framedOnes O T U OP) σ (σ.sets O (RepairOrdinary.frame (List.replicate m true))) (40 * m + 20) := by
  have e1 := Codec.onesLoop_spec cap T U O OP hTU hTO hUO m σ hT (by rw [hO, hOh]; rfl) (by omega)
    (by rw [hU]; omega) (by rw [hOP]; omega)
  set σ1 := NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO ((σ.setv T 0).setv U (σ.val U + m)) O OP
    (marks (List.replicate m true)) with hσ1
  have e2 := emitC_spec cap O OP false σ1
    (by simp [hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hO, hOh])
    (by simp [hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply, hTO, hUO,
        Ne.symm hTO, Ne.symm hUO, hOP, Streaming.marks_length]; omega)
  set σ2 := ((σ1.sets O (σ1.st O ++ [false])).seth O (σ1.sh O + 1)).setv OP (σ1.val OP + 1) with hσ2
  have v2 : σ2.val OP = 2 * m + 1 := by
    simp [hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply, Ne.symm hTO,
      Ne.symm hUO, hOP, Streaming.marks_length]
  have h2 : σ2.sh O = 2 * m + 1 := by
    simp [hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hOh, Streaming.marks_length]
  have e3 := wrewind_spec cap O OP (2 * m + 1) σ2 v2 (by omega)
  rw [h2, Nat.sub_self] at e3
  set σ3 := (σ2.setv OP 0).seth O 0 with hσ3
  have vU : σ3.val U = m := by
    simp [hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply, hUO, hU]
  have vT : σ3.val T = 0 := by
    simp [hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_apply, hTO, hTU]
  have e4 := wmove_spec cap U T (Ne.symm hTU) m σ3 vU (by omega) (by rw [vT, vU]; omega)
  refine WXExec.cast cap (WXExec.seq (WXExec.wm e1) (WXExec.seq (WXExec.wm e2) (WXExec.seq (WXExec.wm e3)
    (WXExec.wm e4)))) ?_ (by omega)
  rw [vT, vU, Nat.zero_add]
  apply WState.eq
  · funext j; by_cases hj : j = O
    · subst hj; simp [hσ3, hOh]
    · simp [hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_of_ne hj]
  · funext j; by_cases hj : j = O
    · subst hj; simp [hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hO,
        Codec.frame_eq_marks]
    · simp [hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_of_ne hj]
  · funext r
    simp only [hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, WState.setv_val,
      WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · simp [hσ3, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO]

/-! ## Values of truncated fields -/

theorem value_zero_of_count : ∀ l : List Bool, l.count true = 0 → value l = 0
  | [], _ => rfl
  | b :: l, h => by
    cases b
    · simp only [List.count_cons, beq_iff_eq] at h
      simp [RadixSemantics.value, value_zero_of_count l (by simpa using h)]
    · simp [List.count_cons] at h

theorem value_pos_of_count : ∀ l : List Bool, 0 < l.count true → 0 < value l
  | [], h => by simp at h
  | b :: l, h => by
    cases b
    · simp only [List.count_cons, beq_iff_eq] at h
      have := value_pos_of_count l (by simpa using h)
      simp [RadixSemantics.value]; omega
    · simp [RadixSemantics.value]

theorem value_replicate_false' : ∀ n : ℕ, value (List.replicate n false) = 0
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, RadixSemantics.value, value_replicate_false' n]

theorem prefixBits_eq (b : List Bool) (ℓ : ℕ) :
    Codec.prefixBits b ℓ = b.take ℓ ++ List.replicate (ℓ - b.length) false := by
  apply List.ext_getElem
  · simp [Codec.prefixBits]; omega
  · intro i h1 h2
    have hl : (Codec.prefixBits b ℓ).length = ℓ := by simp [Codec.prefixBits]
    simp only [Codec.prefixBits, List.getElem_ofFn, List.getD_eq_getElem?_getD]
    by_cases hi : i < b.length
    · rw [List.getElem_append_left (by simp; omega)]
      simp [hi]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [List.getElem?_eq_none (by omega : b.length ≤ i)]

theorem value_prefix_of_zero (b : List Bool) (ℓ : ℕ) (h : (b.drop ℓ).count true = 0) :
    value (Codec.prefixBits b ℓ) = value b := by
  rw [prefixBits_eq, RadixSemantics.value_append, value_replicate_false']
  conv_rhs => rw [← List.take_append_drop ℓ b, RadixSemantics.value_append, value_zero_of_count _ h]

theorem zero_of_value_lt (b : List Bool) (ℓ : ℕ) (h : value b < 2 ^ ℓ) : (b.drop ℓ).count true = 0 := by
  by_contra hc
  have hpos := value_pos_of_count (b.drop ℓ) (Nat.pos_of_ne_zero hc)
  have hlen : (b.take ℓ).length = ℓ := by
    have : ℓ ≤ b.length := by
      by_contra hl
      rw [List.drop_eq_nil_of_le (by omega)] at hpos
      simp [RadixSemantics.value] at hpos
    simp; omega
  have := RadixSemantics.value_append (b.take ℓ) (b.drop ℓ)
  rw [List.take_append_drop, hlen] at this
  have : 2 ^ ℓ ≤ 2 ^ ℓ * value (b.drop ℓ) := Nat.le_mul_of_pos_right _ hpos
  omega

end W3.NearCubicWires.RepairSource.Outer3.Front
