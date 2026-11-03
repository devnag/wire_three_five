import Proof.Wire_3_5.UnionMachine.IncInt
import Proof.Wire_3_5.Foundations.Contracts

/-! # C6 front, the C1 dock: a carrier's gates in C1's request format

C1's request word lists every gate as its weights' `intWord`s and its threshold's `intWord` (`Plan.selWord`, at
`toInt g = ⟨g.weight, g.threshold⟩`); base's decoders leave a carrier's gates as the framed native region
`tabSeg X = X.flatMap (frame ∘ gateW)`, `gateW g = natWord n ++ weights' intWords ++ intWord (θ − 1)` (T's
`TabRef.tabGW_eq`, base `Production.bottomWord`). The converter (layout `WState 1 16`, IncInt's registers `0 … 7`,
`8` the arity `q` (kept), `9` the gate count, `10` the weight counter, `11` a temp) reads the region's gates while
their frames last and appends, framed, **`selGate g = weights' intWords ++ intWord θ`** per gate:
* **`gBody_spec`** (one gate: skip `natWord q`, copy `q` weights (PA's `copyBit`, `copyNatM`), increment the threshold
  (`IncInt.incInt_spec`), step past the frame's end), **`gconv_spec`** (every gate of `X`).

Paper quantity: the carriers' gates of `star:selection`'s request (P3:1326-1330). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.GateConv
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicWires.WireExponent3_5.UnionMachine.BinW (dupR)
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable (cap : ℕ)

/-- A gate's native word (`tabGW`, at arity `q`). -/
def gateW {q : ℕ} (g : NormalizedThresholdGate q) : List Bool :=
  natWord q ++ (List.ofFn g.weight).flatMap intWord ++ intWord (g.threshold - 1)

/-- **A gate in C1's request format**: its weights' `intWord`s, its threshold's `intWord`. -/
def selGate {q : ℕ} (g : NormalizedThresholdGate q) : List Bool :=
  (List.ofFn g.weight).flatMap intWord ++ intWord g.threshold

/-- The weights' loop body: one sign bit and one magnitude. -/
def wBody : WM 1 16 := .seq (.seq (.dec 10) (copyBit true 0 1 6)) (copyNatM true 0 1 0 2 6)

/-- One gate. -/
def gBody : WM 1 16 :=
  .seq (.seq (.seq (.seq (.seq (skipNatM true 0 0 2) (dupR 8 10 11)) (.whr 10 wBody)) (IncInt.incIntM true))
    (.fwd 0)) (.inc 9)

/-- **The converter**: every framed gate while the next cell is a frame's marker. -/
def gconv : WM 1 16 := .whs 0 gBody

theorem intWord_len' (z : ℤ) : (intWord z).length = 2 * natBitLength z.natAbs + 2 := IncInt.intWord_len z

/-- The weights' state after `k` weights. -/
def wSt (σ : WState 1 16) (pre : List Bool) (ws : List ℤ) (k : ℕ) : WState 1 16 :=
  ((appendO σ 1 6 (marks ((ws.take k).flatMap intWord))).seth 0
    (pre.length + 2 * ((ws.take k).flatMap intWord).length)).setv 10 (ws.length - k)

theorem take_flat_succ (ws : List ℤ) (k : ℕ) (hk : k < ws.length) :
    (ws.take (k + 1)).flatMap intWord = (ws.take k).flatMap intWord ++ intWord (ws.getD k 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.flatMap_append]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem flat_split (ws : List ℤ) (k : ℕ) (hk : k < ws.length) :
    ws.flatMap intWord = (ws.take k).flatMap intWord ++ intWord (ws.getD k 0) ++ (ws.drop (k + 1)).flatMap intWord := by
  rw [← take_flat_succ ws k hk, ← List.flatMap_append, List.take_append_drop]

theorem wStep_spec (σ : WState 1 16) (pre rest : List Bool) (ws : List ℤ)
    (hst : σ.st 0 = pre ++ marks (ws.flatMap intWord) ++ rest) (hsh : σ.sh 0 = pre.length)
    (ho : σ.sh 1 = (σ.st 1).length) (hf : σ.val 0 = 0) (hc : σ.val 2 = 0)
    (hcap : σ.val 6 + 2 * (ws.flatMap intWord).length + 10 ≤ cap) (hq : ws.length ≤ cap) (k : ℕ)
    (hk : k < ws.length) :
    WExec cap wBody (wSt σ pre ws k) (wSt σ pre ws (k + 1)) (200 * (ws.flatMap intWord).length + 100) := by
  obtain ⟨w, hw⟩ : ∃ w, w = ws.getD k 0 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (ws.take k).flatMap intWord := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (ws.drop (k + 1)).flatMap intWord := ⟨_, rfl⟩
  have hsp : ws.flatMap intWord = A ++ intWord w ++ B := by rw [hA, hw, hB]; exact flat_split ws k hk
  have hnext : (ws.take (k + 1)).flatMap intWord = A ++ intWord w := by rw [take_flat_succ ws k hk, hA, hw]
  have hwl : (intWord w).length = 2 * natBitLength w.natAbs + 2 := intWord_len' w
  have hnl := natWord_length w.natAbs
  have htot : (ws.flatMap intWord).length = A.length + (2 * natBitLength w.natAbs + 2) + B.length := by
    rw [hsp]; simp [hwl]; omega
  have hsrc : σ.st 0 = (pre ++ marks A ++ [true, decide (w < 0)]) ++ PrimAsm.ParseNat.enc true (natWord w.natAbs) ++
      (marks B ++ rest) := by
    rw [hst, hsp, Streaming.marks_append, Streaming.marks_append, IncMath.intWord_eq, BitLoop.marks_cons]
    simp [PrimAsm.ParseNat.enc]
  set τ := wSt σ pre ws k with hτ
  have hτst : τ.st 0 = σ.st 0 := by simp [τ, wSt]
  have hτsh : τ.sh 0 = pre.length + 2 * A.length := by simp [τ, wSt, hA]
  have hτo : τ.sh 1 = (τ.st 1).length := by simp [τ, wSt, ho]
  have hτ10 : τ.val 10 = ws.length - k := by simp [τ, wSt]
  have hτ6 : τ.val 6 = σ.val 6 + 2 * A.length := by simp [τ, wSt, hA]
  have hτ0 : τ.val 0 = 0 := by simp [τ, wSt, hf]
  have hτ2 : τ.val 2 = 0 := by simp [τ, wSt, hc]
  have c1 := WExec.dec (cap := cap) 10 τ (by rw [hτ10]; omega)
  have c2 := WExec.seq c1 (copyBit_spec cap true 0 1 (by decide) 6 _ (by simp [hτo]) (by simp [hτ6]; omega))
  have hsgn : readTapeBit ((τ.setv 10 (τ.val 10 - 1)).st 0) ((τ.setv 10 (τ.val 10 - 1)).sh 0 + off true) =
      decide (w < 0) := by
    have hsrc2 : σ.st 0 = (pre ++ marks A) ++ (true :: decide (w < 0) ::
        (PrimAsm.ParseNat.enc true (natWord w.natAbs) ++ (marks B ++ rest))) := by
      rw [hsrc]; simp
    simp only [WState.setv_st, WState.setv_sh]
    rw [hτst, hsrc2, hτsh, show pre.length + 2 * A.length + off true = (pre ++ marks A).length + 1 by
      simp [off], read_pre]
    rfl
  rw [hsgn] at c2
  have c3 := WExec.seq c2 (copyNatM_spec cap true 0 1 (by decide) 0 2 6 (by decide) (by decide) (by decide)
    w.natAbs (pre ++ marks A ++ [true, decide (w < 0)]) (marks B ++ rest) _
    (by simp only [WState.seth_st, appendO_st, WState.setv_st, Function.update_apply]; simp [hτst, hsrc])
    (by simp [hτsh, PrimAsm.ParseNat.stp]; ring) (by simp [hτo]) (by simp [hτ0]) (by simp [hτ2])
    (by simp [hτ6, hnl]; omega))
  refine WExec.cast cap c3 ?_ (by rw [htot]; omega)
  simp only [wSt, hnext]
  apply WState.eq
  · funext j; fin_cases j
    · simp [hτsh, PrimAsm.ParseNat.stp, hnl, hwl, hA]; ring
    · simp [τ, wSt, hA, Streaming.marks_append, hwl, IncMath.intWord_eq, BitLoop.marks_cons]; ring
  · funext j; fin_cases j
    · simp [τ, wSt]
    · simp [τ, wSt, hA, Streaming.marks_append, IncMath.intWord_eq, BitLoop.marks_cons, List.append_assoc]
  · funext r; by_cases h : r = 10
    · subst h; simp [τ, wSt]; omega
    · by_cases h6 : r = 6
      · subst h6; simp [τ, wSt, hA, Streaming.marks_append, IncMath.intWord_eq, BitLoop.marks_cons, hnl]; ring
      · simp [τ, wSt, Function.update_apply, h, h6]
  · simp [τ, wSt]

/-- **The weights' loop**: the `q` weights' `intWord`s, copied framed. -/
theorem wLoop_spec (σ : WState 1 16) (pre rest : List Bool) (ws : List ℤ)
    (hst : σ.st 0 = pre ++ marks (ws.flatMap intWord) ++ rest) (hsh : σ.sh 0 = pre.length)
    (ho : σ.sh 1 = (σ.st 1).length) (hW : σ.val 10 = ws.length) (hf : σ.val 0 = 0) (hc : σ.val 2 = 0)
    (hcap : σ.val 6 + 2 * (ws.flatMap intWord).length + 10 ≤ cap) (hq : ws.length ≤ cap) :
    WExec cap (.whr 10 wBody) σ (wSt σ pre ws ws.length)
      (ws.length * (200 * (ws.flatMap intWord).length + 102) + 1) := by
  have e0 : wSt σ pre ws 0 = σ := by
    apply WState.eq
    · funext j; fin_cases j <;> simp [wSt, hsh, BitLoop.marks_nil]
    · funext j; fin_cases j <;> simp [wSt, BitLoop.marks_nil]
    · funext r; by_cases h : r = 10
      · subst h; simp [wSt, hW]
      · by_cases h6 : r = 6
        · subst h6; simp [wSt, BitLoop.marks_nil]
        · simp [wSt, Function.update_apply, h, h6]
    · simp [wSt]
  have lp := PrimAsm.UnaryPow.flagLoop cap 10 wBody (200 * (ws.flatMap intWord).length + 100) ws.length
    (wSt σ pre ws) (fun k hk => by simp [wSt]; omega) (by simp [wSt])
    (fun k hk => wStep_spec cap σ pre rest ws hst hsh ho hf hc hcap hq k hk)
  rw [e0] at lp
  exact lp

theorem frame_marks (w : List Bool) : frame w = marks w ++ [false] := by
  rw [frame_eq_frameP]; rfl

theorem gateW_len {q : ℕ} (g : NormalizedThresholdGate q) :
    (gateW g).length = (natWord q).length + ((List.ofFn g.weight).flatMap intWord).length +
      (intWord (g.threshold - 1)).length := by
  simp only [gateW, List.length_append]

/-- A gate's cost bound. -/
def gCost (L : ℕ) : ℕ := 1000 * (L + 1) * (L + 1)

/-- **One gate**: from `frame (gateW g)` at the head (arity `q` in register `8`), it appends `marks (selGate g)` and
moves past the frame; the gate count `+1`; every scratch register back at `0`. -/
theorem gBody_spec {q : ℕ} (g : NormalizedThresholdGate q) (σ : WState 1 16) (pre rest : List Bool)
    (hst : σ.st 0 = pre ++ frame (gateW g) ++ rest) (hsh : σ.sh 0 = pre.length) (ho : σ.sh 1 = (σ.st 1).length)
    (hq : σ.val 8 = q) (hf : σ.val 0 = 0) (hL : σ.val 1 = 0) (hT : σ.val 2 = 0) (hU : σ.val 3 = 0) (hF : σ.val 4 = 0)
    (hC : σ.val 5 = 0) (hW : σ.val 7 = 0) (hw : σ.val 10 = 0) (hu : σ.val 11 = 0)
    (hcap : σ.val 6 + 10 * ((gateW g).length + 2) + σ.val 9 ≤ cap) :
    WExec cap gBody σ ((appendO (σ.seth 0 (pre.length + (frame (gateW g)).length)) 1 6 (marks (selGate g))).setv 9
      (σ.val 9 + 1)) (gCost (gateW g).length) := by
  obtain ⟨W, hWd⟩ : ∃ W, W = (List.ofFn g.weight).flatMap intWord := ⟨_, rfl⟩
  have hgl := gateW_len g
  rw [← hWd] at hgl
  have hnl := natWord_length q
  have hth := intWord_len' (g.threshold - 1)
  have hwsl : (List.ofFn g.weight).length = q := List.length_ofFn
  have hqW : q ≤ W.length := by
    have : ∀ ws : List ℤ, ws.length ≤ (ws.flatMap intWord).length := by
      intro ws; induction ws with
      | nil => simp
      | cons a t ih => simp [List.flatMap_cons, intWord_len']; omega
    have := this (List.ofFn g.weight); rw [hwsl, ← hWd] at this; exact this
  have hwt : (List.ofFn g.weight).take q = List.ofFn g.weight := List.take_of_length_le (by rw [hwsl])
  have hsrc : σ.st 0 = pre ++ PrimAsm.ParseNat.enc true (natWord q) ++
      (marks W ++ marks (intWord (g.threshold - 1)) ++ [false] ++ rest) := by
    rw [hst, frame_marks, gateW, ← hWd, Streaming.marks_append, Streaming.marks_append]
    simp [PrimAsm.ParseNat.enc, List.append_assoc]
  have c1 := skipNatM_spec cap true 0 0 2 (by decide) q pre _ σ hsrc hsh hf hT (by omega)
  have c2 := WExec.seq c1 (BinW.dupR_spec cap 8 10 11 (by decide) (by decide) (by decide) _ q (by simp [hq])
    (by simp [hw]) (by simp [hu]) (by omega))
  have c3 := WExec.seq c2 (wLoop_spec cap _ (pre ++ marks (natWord q))
    (marks (intWord (g.threshold - 1)) ++ [false] ++ rest) (List.ofFn g.weight)
    (by simp [hsrc, ← hWd, PrimAsm.ParseNat.enc, List.append_assoc])
    (by simp [PrimAsm.ParseNat.stp, hnl]) (by simp [ho]) (by simp [hwsl]) (by simp [hf]) (by simp [hT])
    (by simp [← hWd]; omega) (by rw [hwsl]; omega))
  simp only [wSt, hwsl, hwt, ← hWd, Nat.sub_self] at c3
  have c4 := WExec.seq c3 (IncInt.incInt_spec cap true _ (pre ++ marks (natWord q) ++ marks W) ([false] ++ rest)
    (g.threshold - 1) (by simp [hsrc, PrimAsm.ParseNat.enc, List.append_assoc])
    (by simp [PrimAsm.ParseNat.stp, hnl]; ring) (by simp [ho]) (by simp [hf])
    (by simp [hL]) (by simp [hT]) (by simp [hU]) (by simp [hF]) (by simp [hC])
    (by simp [hW]) (by simp; omega))
  have c5 := WExec.seq c4 (WExec.fwd (cap := cap) 0 _)
  have c6 := WExec.seq c5 (WExec.inc (cap := cap) 9 _ (by simp; omega))
  refine WExec.cast cap c6 ?_ ?_
  · rw [show g.threshold - 1 + 1 = g.threshold by ring]
    apply WState.eq
    · funext j; fin_cases j
      · simp [PrimAsm.ParseNat.stp, hnl, frame_marks, gateW, ← hWd, hth]; ring
      · simp [selGate, ← hWd, Streaming.marks_append]; ring
    · funext j; fin_cases j
      · simp
      · simp [selGate, ← hWd, Streaming.marks_append, List.append_assoc]
    · funext r
      by_cases h9 : r = 9
      · subst h9; simp
      · by_cases h10 : r = 10
        · subst h10; simp [hw]
        · by_cases h6 : r = 6
          · subst h6; simp [selGate, ← hWd, Streaming.marks_append]; ring
          · simp [Function.update_apply, h9, h10, h6]
    · simp
  · unfold gCost
    rw [hgl]
    obtain ⟨G, hG⟩ : ∃ G, G = (natWord q).length + W.length + (intWord (g.threshold - 1)).length := ⟨_, rfl⟩
    rw [← hG]
    have hq2 : q * (200 * W.length + 102) ≤ G * (200 * G + 102) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith

/-- The framed native region of a gate list (`TabRef.tabSeg`). -/
def tabL {q : ℕ} (X : List (NormalizedThresholdGate q)) : List Bool := X.flatMap fun g => frame (gateW g)

/-- The converter's capacity need. -/
def capNeed {q : ℕ} (X : List (NormalizedThresholdGate q)) : ℕ :=
  (X.map fun g => 2 * (selGate g).length + 10 * ((gateW g).length + 2) + 2).sum

/-- The converter's cost. -/
def gsCost {q : ℕ} (X : List (NormalizedThresholdGate q)) : ℕ :=
  (X.map fun g => gCost (gateW g).length + 2).sum + 1

theorem gateW_ne {q : ℕ} (g : NormalizedThresholdGate q) (rest : List Bool) :
    readTapeBit (frame (gateW g) ++ rest) 0 = true := by
  have hne : gateW g ≠ [] := by simp [gateW, natWord_eq]
  obtain ⟨b, t, h⟩ := List.exists_cons_of_ne_nil hne
  rw [frame_marks, h, BitLoop.marks_cons]
  simp [readTapeBit]

/-- **The converter**: every gate of `X` while the frames last (the cell after them reads `false`). -/
theorem gconv_spec {q : ℕ} : ∀ (X : List (NormalizedThresholdGate q)) (σ : WState 1 16) (pre rest : List Bool),
    σ.st 0 = pre ++ tabL X ++ rest → σ.sh 0 = pre.length → readTapeBit rest 0 = false →
    σ.sh 1 = (σ.st 1).length → σ.val 8 = q → σ.val 0 = 0 → σ.val 1 = 0 → σ.val 2 = 0 → σ.val 3 = 0 →
    σ.val 4 = 0 → σ.val 5 = 0 → σ.val 7 = 0 → σ.val 10 = 0 → σ.val 11 = 0 →
    σ.val 6 + σ.val 9 + capNeed X ≤ cap →
    WExec cap gconv σ ((appendO (σ.seth 0 (pre.length + (tabL X).length)) 1 6 (marks (X.flatMap selGate))).setv 9
      (σ.val 9 + X.length)) (gsCost X)
  | [], σ, pre, rest, hst, hsh, hstop, ho, hq, hf, hL, hT, hU, hF, hC, hW, hw, hu, hcap => by
    have e : (appendO (σ.seth 0 (pre.length + (tabL ([] : List (NormalizedThresholdGate q))).length)) 1 6
        (marks (([] : List (NormalizedThresholdGate q)).flatMap selGate))).setv 9 (σ.val 9 + 0) = σ := by
      apply WState.eq
      · funext j; fin_cases j <;> simp [tabL, hsh, BitLoop.marks_nil]
      · funext j; fin_cases j <;> simp [BitLoop.marks_nil]
      · funext r; by_cases h9 : r = 9
        · subst h9; simp
        · by_cases h6 : r = 6
          · subst h6; simp [BitLoop.marks_nil]
          · simp [Function.update_apply, h9, h6]
      · simp
    simp only [List.length_nil] at e ⊢
    rw [e]
    refine WExec.mono (WExec.whsF ?_) (by simp [gsCost])
    simp only [wbit, hsh, hst, tabL, List.flatMap_nil, List.append_nil]
    rw [show pre.length = pre.length + 0 by rfl, read_pre]; exact hstop
  | g :: X, σ, pre, rest, hst, hsh, hstop, ho, hq, hf, hL, hT, hU, hF, hC, hW, hw, hu, hcap => by
    have hcn : capNeed (g :: X) = 2 * (selGate g).length + 10 * ((gateW g).length + 2) + 2 + capNeed X := by
      simp [capNeed]
    have hgc : gsCost (g :: X) = gCost (gateW g).length + 2 + gsCost X := by simp [gsCost]; omega
    have htl : tabL (g :: X) = frame (gateW g) ++ tabL X := by simp [tabL]
    have c1 := gBody_spec cap g σ pre (tabL X ++ rest) (by rw [hst, htl]; simp) hsh ho hq hf hL hT hU hF hC hW hw hu
      (by rw [hcn] at hcap; omega)
    have ih := gconv_spec X ((appendO (σ.seth 0 (pre.length + (frame (gateW g)).length)) 1 6
      (marks (selGate g))).setv 9 (σ.val 9 + 1)) (pre ++ frame (gateW g)) rest (by simp [hst, htl]) (by simp)
      hstop (by simp [ho]) (by simp [hq]) (by simp [hf]) (by simp [hL]) (by simp [hT]) (by simp [hU])
      (by simp [hF]) (by simp [hC]) (by simp [hW]) (by simp [hw]) (by simp [hu])
      (by simp; rw [hcn] at hcap; omega)
    have hbit : wbit σ 0 = true := by
      simp only [wbit, hsh, hst, htl]
      rw [show pre.length = pre.length + 0 by rfl, List.append_assoc, List.append_assoc, read_pre]
      exact gateW_ne g _
    refine WExec.cast cap (WExec.whsT hbit c1 ih) ?_ (by rw [hgc] <;> omega)
    apply WState.eq
    · funext j; fin_cases j
      · simp [htl]; ring
      · simp [Streaming.marks_append]; ring
    · funext j; fin_cases j
      · simp
      · simp [Streaming.marks_append, List.append_assoc]
    · funext r; by_cases h9 : r = 9
      · subst h9; simp; ring
      · by_cases h6 : r = 6
        · subst h6; simp [Streaming.marks_append]; ring
        · simp [Function.update_apply, h9, h6]
    · simp

/-- **The type anchor**: a converted gate is exactly C1's request segment of the gate (`Plan.selWord`'s
`(List.ofFn fun i => intWord (g.weights i)).flatten ++ intWord g.threshold` at `⟨g.weight, g.threshold⟩`). -/
theorem selGate_selWord {q : ℕ} (g : NormalizedThresholdGate q) :
    selGate g = (fun (G : NearCubicWires.WireExponent3_5.Machine.S0Stub.IntGate q) =>
      (List.ofFn fun i => intWord (G.weights i)).flatten ++ intWord G.threshold) ⟨g.weight, g.threshold⟩ := by
  simp only [selGate]
  congr 1
  rw [List.flatMap_def, List.map_ofFn]
  rfl

/-- **The request's gate segment**: `Plan.selWord` lists the gates `X.map toInt` (`toInt g = ⟨g.weight, g.threshold⟩`)
as `X.flatMap selGate`, the converter's output. -/
theorem selGates_selWord {q : ℕ} (X : List (NormalizedThresholdGate q)) :
    (X.map fun g => (⟨g.weight, g.threshold⟩ : NearCubicWires.WireExponent3_5.Machine.S0Stub.IntGate q)).flatMap
      (fun G => (List.ofFn fun i => intWord (G.weights i)).flatten ++ intWord G.threshold) = X.flatMap selGate := by
  induction X with
  | nil => rfl
  | cons g X ih => rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih, selGate_selWord]

end NearCubicWires.WireExponent3_5.UnionMachine.GateConv
