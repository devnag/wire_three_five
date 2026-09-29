import Proof.Wire_3_5.Primitive.SeedFix.FlipsSteps

/-! # FLIPS, part 5: the cell loops (P3:1224, 1655-1664)

For every cell row `L < 2^{kh}` (left-major) and column `R < 2^{kh}` (right-minor), the four corner points
(`blk`) in C3a's order: **`rLoop`** walks the columns of one row (`outR`), **`lLoop`** the rows (`outL`), each with its
binary counter stepped by `stepCtr` (the last-index test `onesChk`, then C1's `incCNT`, or the loop flag cleared).

* `stepCtr_spec`, `ctrR_step`, `ctrL_step`; `rBody_spec`, **`rLoop_spec`**; `lBody_spec`, **`lLoop_spec`**.

Paper quantity of the main type: the flip patterns of every cell and corner (`outL`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Flips
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GS GR gIN gOUT)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn incCNT zeroCNT)

/-! ## The counter step -/

/-- **The counter step**: the last-index test, then the increment (or the loop flag cleared). -/
def stepCtr (C : Fin (GS + 1)) (go : Fin GR) : WM GS GR :=
  .seq (onesChk C rNz rScn) (.ifr rNz (.seq (incCNT C sTOT rF rR) (.dec rNz)) (.dec go))

/-- The step's cost bound. -/
def ctrCost (w : ℕ) : ℕ := onesCost w + 1 + (41 * w + 7 + 1 + 1 + 1)

section Ctr
variable (cap : ℕ)

theorem stepCtr_spec (C : Fin (GS + 1)) (go : Fin GR) (hC : C ≠ sTOT) (hgo1 : go ≠ rNz) (hgo2 : go ≠ rScn)
    (hgo3 : go ≠ rF) (hgo4 : go ≠ rR) (w v : ℕ) (hv : v < 2 ^ w) (σ : WState GS GR) (hN : NumOn σ C w v)
    (hT : NumOn σ sTOT w 0) (hnz : σ.val rNz = 0) (hsc : σ.val rScn = 0) (hF : σ.val rF = 0) (hR : σ.val rR = 0)
    (hg : σ.val go = 1) (hcap : 2 * w + 2 ≤ cap) :
    ∃ τ, WExec cap (stepCtr C go) σ τ (ctrCost w) ∧
      τ.st C = frame (binary w (if v + 1 < 2 ^ w then v + 1 else v)) ∧ τ.sh C = 0 ∧
      τ.val go = (if v + 1 < 2 ^ w then 1 else 0) ∧ τ.val rNz = 0 ∧ τ.val rScn = 0 ∧ τ.val rF = 0 ∧
      τ.val rR = 0 ∧ (∀ i, i ≠ C → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      (∀ r, r ≠ go → r ≠ rNz → r ≠ rScn → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have hbl : (binary w v).length = w := SignedSortKey.binary_length w v
  obtain ⟨τ1, e1, a1, a2, a3, a4, a5, a6, a7⟩ := onesChk_spec cap C rNz rScn (by decide) (binary w v) [] σ
    (by rw [hN.1, frame_eq_frameP]) hN.2 hnz hsc (by rw [hbl]; omega)
  rw [hbl] at e1
  have hsn : rScn ≠ rNz := by decide
  have hfn : rF ≠ rNz := by decide
  have hrn : rR ≠ rNz := by decide
  have hflag : flagOf (binary w v) = if v + 1 < 2 ^ w then 1 else 0 := by
    unfold flagOf
    have := binary_all w v hv
    by_cases h1 : v + 1 < 2 ^ w
    · rw [if_pos h1, if_neg (fun h => by have := this.mp h; omega)]
    · rw [if_neg h1, if_pos (this.mpr (by omega))]
  rw [hflag] at a2
  by_cases h1 : v + 1 < 2 ^ w
  · rw [if_pos h1] at a2
    have hN1 : NumOn τ1 C w v := ⟨by rw [a4, hN.1], a1⟩
    have hT1 : NumOn τ1 sTOT w 0 := ⟨by rw [a4, hT.1], by rw [a5 sTOT (Ne.symm hC), hT.2]⟩
    have e2 := SelectionMachine.Sort.incCNT_spec cap w hC (show rF ≠ rR by decide) τ1 v 0 hN1 hT1
      (by rw [a6 rF (by decide) (by decide), hF]) (by rw [a6 rR (by decide) (by decide), hR]) h1 (by omega)
    have e3 := WExec.dec (cap := cap) rNz (τ1.sets C (frame (binary w (v + 1)))) (by simp [WState.sets, a2]; omega)
    refine ⟨_, WExec.mono (WExec.seq e1 (WExec.ifrT (by rw [a2]; omega) (WExec.seq e2 e3))) (by unfold ctrCost; omega),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_pos h1]; simp [WState.sets, WState.setv]
    · simp [WState.sets, WState.setv, a1]
    · rw [if_pos h1]; simp [WState.sets, WState.setv, Function.update_apply, hgo1, a6 go hgo1 hgo2, hg]
    · simp [WState.sets, WState.setv, a2]
    · simp [WState.sets, WState.setv, Function.update_apply, hsn, a3]
    · simp [WState.sets, WState.setv, Function.update_apply, hfn, a6 rF (by decide) (by decide), hF]
    · simp [WState.sets, WState.setv, Function.update_apply, hrn, a6 rR (by decide) (by decide), hR]
    · intro i hi
      simp only [WState.sets, WState.setv, Function.update_apply, if_neg hi]
      exact ⟨by rw [a4], a5 i hi⟩
    · intro r h1' h2 h3
      simp only [WState.sets, WState.setv, Function.update_apply, if_neg h2]
      exact a6 r h2 h3
    · simp [WState.sets, WState.setv, a7]
  · rw [if_neg h1] at a2
    have e3 := WExec.dec (cap := cap) go τ1 (by rw [a6 go hgo1 hgo2, hg]; omega)
    refine ⟨_, WExec.mono (WExec.seq e1 (WExec.ifrF a2 e3)) (by unfold ctrCost; omega),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_neg h1]; simp [WState.setv, a4, hN.1]
    · simp [WState.setv, a1]
    · rw [if_neg h1]; simp [WState.setv, a6 go hgo1 hgo2, hg]
    · simp [WState.setv, Function.update_apply, Ne.symm hgo1, a2]
    · simp [WState.setv, Function.update_apply, Ne.symm hgo2, a3]
    · simp [WState.setv, Function.update_apply, Ne.symm hgo3, a6 rF (by decide) (by decide), hF]
    · simp [WState.setv, Function.update_apply, Ne.symm hgo4, a6 rR (by decide) (by decide), hR]
    · intro i hi
      simp only [WState.setv]
      exact ⟨by rw [a4], a5 i hi⟩
    · intro r h1' h2 h3
      simp only [WState.setv, Function.update_apply, if_neg h1']
      exact a6 r h2 h3
    · simp [WState.setv, a7]

end Ctr

/-! ## Transfers -/

section Tr
variable {s b h tl : ℕ} {σ0 σ : WState GS GR} {OFFw ELc ERc : List Bool} {L R : ℕ} {out : List Bool} {gR gL : ℕ}

theorem upd_ne {r q : Fin GR} (x : ℕ) (hne : q ≠ r) : (σ.setv r x).val q = σ.val q := by
  simp [WState.setv, Function.update_apply, hne]

theorem FS.setGoR (hf : FS s b h tl σ0 σ OFFw ELc ERc L R out gR gL) (x : ℕ) :
    FS s b h tl σ0 (σ.setv rGoR x) OFFw ELc ERc L R out x gL :=
  ⟨hf.lOF, hf.lEL, hf.lER, hf.stOF, hf.shOF, hf.stEL, hf.shEL, hf.stER, hf.shER, hf.nL, hf.nR, hf.nT, hf.sO, hf.hO,
    hf.sIN, by rw [upd_ne x (RD_goR 0), hf.vS], by rw [upd_ne x (RD_goR 1), hf.vB], by rw [upd_ne x (RD_goR 2), hf.vH],
    by rw [upd_ne x (RD_goR 3), hf.vT], fun i hi => by rw [upd_ne x (RD_goR i), hf.vZ i hi],
    by rw [upd_ne x (by decide), hf.vAcc], by rw [upd_ne x (by decide), hf.vCnt], by rw [upd_ne x (by decide), hf.vNz],
    by rw [upd_ne x (by decide), hf.vScn], by rw [upd_ne x (by decide), hf.vF], by rw [upd_ne x (by decide), hf.vR],
    by simp [WState.setv], by rw [upd_ne x (by decide), hf.vgL]⟩

theorem FS.setCR (hf : FS s b h tl σ0 σ OFFw ELc ERc L R out gR gL) (R' : ℕ) :
    FS s b h tl σ0 (σ.sets sCR (frame (binary (s * h) R'))) OFFw ELc ERc L R' out gR gL := by
  have e : ∀ i, i ≠ sCR → (σ.sets sCR (frame (binary (s * h) R'))).st i = σ.st i := fun i hi => by
    simp [WState.sets, Function.update_apply, hi]
  exact ⟨hf.lOF, hf.lEL, hf.lER, by rw [e _ (by decide), hf.stOF], hf.shOF, by rw [e _ (by decide), hf.stEL], hf.shEL,
    by rw [e _ (by decide), hf.stER], hf.shER, ⟨by rw [e _ (by decide), hf.nL.1], hf.nL.2⟩,
    ⟨by simp [WState.sets], hf.nR.2⟩, ⟨by rw [e _ (by decide), hf.nT.1], hf.nT.2⟩, by rw [e _ (by decide), hf.sO],
    hf.hO, by rw [e _ (by decide), hf.sIN], hf.vS, hf.vB, hf.vH, hf.vT, hf.vZ, hf.vAcc,
    hf.vCnt, hf.vNz, hf.vScn, hf.vF, hf.vR, hf.vgR, hf.vgL⟩

end Tr

/-! ## The counter steps on the invariant -/

section Loops
variable (cap : ℕ) (s b h tl : ℕ) (σ0 : WState GS GR) (OFFw : List Bool)

theorem ctrR_step (σ : WState GS GR) (ELc ERc : List Bool) (L R : ℕ) (out : List Bool) (gL : ℕ)
    (hR : R < 2 ^ (s * h)) (hf : FS s b h tl σ0 σ OFFw ELc ERc L R out 1 gL) (hcap : 2 * (s * h) + 2 ≤ cap) :
    ∃ τ, WExec cap (stepCtr sCR rGoR) σ τ (ctrCost (s * h)) ∧
      FS s b h tl σ0 τ OFFw ELc ERc L (if R + 1 < 2 ^ (s * h) then R + 1 else R) out
        (if R + 1 < 2 ^ (s * h) then 1 else 0) gL := by
  obtain ⟨τ, e, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := stepCtr_spec cap sCR rGoR (by decide) (by decide)
    (by decide) (by decide) (by decide) (s * h) R hR σ hf.nR hf.nT hf.vNz hf.vScn hf.vF hf.vR hf.vgR hcap
  refine ⟨τ, e, ⟨hf.lOF, hf.lEL, hf.lER, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨a1, a2⟩, ⟨?_, ?_⟩, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, a4, a5, a6, a7, a3, ?_⟩⟩
  · rw [(a8 sOFF (by decide)).1, hf.stOF]
  · rw [(a8 sOFF (by decide)).2, hf.shOF]
  · rw [(a8 sEL (by decide)).1, hf.stEL]
  · rw [(a8 sEL (by decide)).2, hf.shEL]
  · rw [(a8 sER (by decide)).1, hf.stER]
  · rw [(a8 sER (by decide)).2, hf.shER]
  · rw [(a8 sCL (by decide)).1, hf.nL.1]
  · rw [(a8 sCL (by decide)).2, hf.nL.2]
  · rw [(a8 sTOT (by decide)).1, hf.nT.1]
  · rw [(a8 sTOT (by decide)).2, hf.nT.2]
  · rw [(a8 gOUT (by decide)).1, hf.sO]
  · rw [(a8 gOUT (by decide)).2, hf.hO]
  · rw [(a8 gIN (by decide)).1, hf.sIN]
  · rw [a9 _ (RD_goR 0) (RD_nz 0) (RD_scn 0), hf.vS]
  · rw [a9 _ (RD_goR 1) (RD_nz 1) (RD_scn 1), hf.vB]
  · rw [a9 _ (RD_goR 2) (RD_nz 2) (RD_scn 2), hf.vH]
  · rw [a9 _ (RD_goR 3) (RD_nz 3) (RD_scn 3), hf.vT]
  · intro i hi; rw [a9 _ (RD_goR i) (RD_nz i) (RD_scn i), hf.vZ i hi]
  · rw [a9 _ (by decide) (by decide) (by decide), hf.vAcc]
  · rw [a9 _ (by decide) (by decide) (by decide), hf.vCnt]
  · rw [a9 _ (by decide) (by decide) (by decide), hf.vgL]

theorem ctrL_step (σ : WState GS GR) (ELc ERc : List Bool) (L R : ℕ) (out : List Bool) (gR : ℕ)
    (hL : L < 2 ^ (s * h)) (hf : FS s b h tl σ0 σ OFFw ELc ERc L R out gR 1) (hcap : 2 * (s * h) + 2 ≤ cap) :
    ∃ τ, WExec cap (stepCtr sCL rGoL) σ τ (ctrCost (s * h)) ∧
      FS s b h tl σ0 τ OFFw ELc ERc (if L + 1 < 2 ^ (s * h) then L + 1 else L) R out gR
        (if L + 1 < 2 ^ (s * h) then 1 else 0) := by
  obtain ⟨τ, e, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := stepCtr_spec cap sCL rGoL (by decide) (by decide)
    (by decide) (by decide) (by decide) (s * h) L hL σ hf.nL hf.nT hf.vNz hf.vScn hf.vF hf.vR hf.vgL hcap
  refine ⟨τ, e, ⟨hf.lOF, hf.lEL, hf.lER, ?_, ?_, ?_, ?_, ?_, ?_, ⟨a1, a2⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, a4, a5, a6, a7, ?_, a3⟩⟩
  · rw [(a8 sOFF (by decide)).1, hf.stOF]
  · rw [(a8 sOFF (by decide)).2, hf.shOF]
  · rw [(a8 sEL (by decide)).1, hf.stEL]
  · rw [(a8 sEL (by decide)).2, hf.shEL]
  · rw [(a8 sER (by decide)).1, hf.stER]
  · rw [(a8 sER (by decide)).2, hf.shER]
  · rw [(a8 sCR (by decide)).1, hf.nR.1]
  · rw [(a8 sCR (by decide)).2, hf.nR.2]
  · rw [(a8 sTOT (by decide)).1, hf.nT.1]
  · rw [(a8 sTOT (by decide)).2, hf.nT.2]
  · rw [(a8 gOUT (by decide)).1, hf.sO]
  · rw [(a8 gOUT (by decide)).2, hf.hO]
  · rw [(a8 gIN (by decide)).1, hf.sIN]
  · rw [a9 _ (RD_goL 0) (RD_nz 0) (RD_scn 0), hf.vS]
  · rw [a9 _ (RD_goL 1) (RD_nz 1) (RD_scn 1), hf.vB]
  · rw [a9 _ (RD_goL 2) (RD_nz 2) (RD_scn 2), hf.vH]
  · rw [a9 _ (RD_goL 3) (RD_nz 3) (RD_scn 3), hf.vT]
  · intro i hi; rw [a9 _ (RD_goL i) (RD_nz i) (RD_scn i), hf.vZ i hi]
  · rw [a9 _ (by decide) (by decide) (by decide), hf.vAcc]
  · rw [a9 _ (by decide) (by decide) (by decide), hf.vCnt]
  · rw [a9 _ (by decide) (by decide) (by decide), hf.vgR]

/-! ## The column loop -/

/-- One column: its right errors, the cell's four corners, the column counter's step. -/
def rBody : WM GS GR := .seq (decStage true sCR sER RD) (.seq cornersW (stepCtr sCR rGoR))

/-- The column loop. -/
def rLoop : WM GS GR := .whr rGoR rBody

/-- One column's cost. -/
def rBodyCost (s b h tl : ℕ) : ℕ :=
  decStageCost s b h tl + 1 + (cornersCost (h * b + h * b + tl) + 1 + ctrCost (s * h))

/-- The row `L`'s columns `< R`: their cells' corners. -/
def outR (s b h tl : ℕ) (OFFw : List Bool) (L R : ℕ) : List Bool :=
  (List.range R).flatMap fun R' => blk OFFw (elW s b h tl L) (erW s b h tl R')

theorem outR_succ (L R : ℕ) : outR s b h tl OFFw L (R + 1) =
    outR s b h tl OFFw L R ++ blk OFFw (elW s b h tl L) (erW s b h tl R) := by
  simp [outR, List.range_succ, List.flatMap_append]

/-- The loops' capacity needs. -/
def LoopCap (s b h tl cap : ℕ) : Prop := DecCap s b h tl cap ∧ 2 * (h * b + h * b + tl) + 2 ≤ cap ∧
  2 * (s * h) + 2 ≤ cap

theorem rBody_spec (hbs : b + 1 = 2 ^ s) (hc : LoopCap s b h tl cap) (σ : WState GS GR) (ERc : List Bool)
    (L R : ℕ) (out : List Bool) (gL : ℕ) (hR : R < 2 ^ (s * h))
    (hf : FS s b h tl σ0 σ OFFw (elW s b h tl L) ERc L R out 1 gL) :
    ∃ τ, WExec cap rBody σ τ (rBodyCost s b h tl) ∧
      FS s b h tl σ0 τ OFFw (elW s b h tl L) (erW s b h tl R) L (if R + 1 < 2 ^ (s * h) then R + 1 else R)
        (out ++ blk OFFw (elW s b h tl L) (erW s b h tl R)) (if R + 1 < 2 ^ (s * h) then 1 else 0) gL := by
  obtain ⟨τ1, e1, f1⟩ := decR_step cap s b h tl σ0 OFFw hbs hc.1 σ _ ERc L R out 1 gL hf
  obtain ⟨τ2, e2, f2⟩ := corners_step cap s b h tl σ0 OFFw τ1 _ _ L R out 1 gL f1 hc.2.1
  obtain ⟨τ3, e3, f3⟩ := ctrR_step cap s b h tl σ0 OFFw τ2 _ _ L R _ gL hR f2 hc.2.2
  exact ⟨τ3, WExec.seq e1 (WExec.seq e2 e3), f3⟩

theorem rLoop_spec (hbs : b + 1 = 2 ^ s) (hc : LoopCap s b h tl cap) (L : ℕ) (out0 : List Bool) (gL : ℕ)
    (m : ℕ) : ∀ (R : ℕ) (σ : WState GS GR) (ERc : List Bool), R + m + 1 = 2 ^ (s * h) →
      FS s b h tl σ0 σ OFFw (elW s b h tl L) ERc L R (out0 ++ outR s b h tl OFFw L R) 1 gL →
      ∃ τ ERc', WExec cap rLoop σ τ ((m + 1) * (rBodyCost s b h tl + 2) + 1) ∧
        FS s b h tl σ0 τ OFFw (elW s b h tl L) ERc' L (2 ^ (s * h) - 1)
          (out0 ++ outR s b h tl OFFw L (2 ^ (s * h))) 0 gL := by
  induction m with
  | zero =>
    intro R σ ERc hRm hf
    obtain ⟨τ, e, f⟩ := rBody_spec cap s b h tl σ0 OFFw hbs hc σ ERc L R _ gL (by omega) hf
    have hn : ¬(R + 1 < 2 ^ (s * h)) := by omega
    rw [if_neg hn, if_neg hn, List.append_assoc, ← outR_succ, show R + 1 = 2 ^ (s * h) by omega] at f
    have hR' : R = 2 ^ (s * h) - 1 := by omega
    rw [hR'] at f
    exact ⟨τ, _, WExec.mono (WExec.whrT (by rw [hf.vgR]; omega) e (WExec.whrF f.vgR)) (by omega), f⟩
  | succ m ih =>
    intro R σ ERc hRm hf
    obtain ⟨τ1, e1, f1⟩ := rBody_spec cap s b h tl σ0 OFFw hbs hc σ ERc L R _ gL (by omega) hf
    have hy : R + 1 < 2 ^ (s * h) := by omega
    rw [if_pos hy, if_pos hy, List.append_assoc, ← outR_succ] at f1
    obtain ⟨τ, ERc', e2, f2⟩ := ih (R + 1) τ1 _ (by omega) f1
    exact ⟨τ, ERc', WExec.mono (WExec.whrT (by rw [hf.vgR]; omega) e1 e2) (by ring_nf; omega), f2⟩

/-! ## The row loop -/

/-- One row: its left errors, the column loop, the column counter reset, the row counter's step. -/
def lBody : WM GS GR :=
  .seq (decStage false sCL sEL RD) (.seq (.inc rGoR) (.seq rLoop (.seq (zeroCNT sCR sTOT rF rR) (stepCtr sCL rGoL))))

/-- The row loop. -/
def lLoop : WM GS GR := .whr rGoL lBody

/-- One row's cost. -/
def lBodyCost (s b h tl : ℕ) : ℕ :=
  decStageCost s b h tl + 1 + (3 + 1 + ((2 ^ (s * h) - 1 + 1) * (rBodyCost s b h tl + 2) + 1 + 1 +
    (41 * (s * h) + 3 + 1 + ctrCost (s * h))))

/-- The rows `< L`: every cell's corners, left-major. -/
def outL (s b h tl : ℕ) (OFFw : List Bool) (L : ℕ) : List Bool :=
  (List.range L).flatMap fun L' => outR s b h tl OFFw L' (2 ^ (s * h))

theorem outL_succ (L : ℕ) : outL s b h tl OFFw (L + 1) = outL s b h tl OFFw L ++ outR s b h tl OFFw L (2 ^ (s * h)) := by
  simp [outL, List.range_succ, List.flatMap_append]

theorem lBody_spec (hbs : b + 1 = 2 ^ s) (hc : LoopCap s b h tl cap) (σ : WState GS GR) (ELc ERc : List Bool)
    (L : ℕ) (out : List Bool) (hL : L < 2 ^ (s * h)) (hf : FS s b h tl σ0 σ OFFw ELc ERc L 0 out 0 1) :
    ∃ τ ERc', WExec cap lBody σ τ (lBodyCost s b h tl) ∧
      FS s b h tl σ0 τ OFFw (elW s b h tl L) ERc' (if L + 1 < 2 ^ (s * h) then L + 1 else L) 0
        (out ++ outR s b h tl OFFw L (2 ^ (s * h))) 0 (if L + 1 < 2 ^ (s * h) then 1 else 0) := by
  have hN : 1 ≤ 2 ^ (s * h) := Nat.one_le_two_pow
  obtain ⟨τ1, e1, f1⟩ := decL_step cap s b h tl σ0 OFFw hbs hc.1 σ ELc ERc L 0 out 0 1 hf
  have e2 := WExec.inc (cap := cap) rGoR τ1 (by rw [f1.vgR]; have := hc.2.2; omega)
  rw [f1.vgR] at e2
  have f2 := f1.setGoR (0 + 1)
  have f2' : FS s b h tl σ0 (τ1.setv rGoR (0 + 1)) OFFw (elW s b h tl L) ERc L 0
      (out ++ outR s b h tl OFFw L 0) 1 1 := by simpa [outR] using f2
  obtain ⟨τ3, ERc', e3, f3⟩ := rLoop_spec cap s b h tl σ0 OFFw hbs hc L out 1 (2 ^ (s * h) - 1) 0 _ ERc
    (by omega) f2'
  have e4 := SelectionMachine.Sort.zeroCNT_spec cap (s * h) (show sCR ≠ sTOT by decide) (show rF ≠ rR by decide) τ3
    (2 ^ (s * h) - 1) 0 f3.nR f3.nT f3.vF f3.vR (by have := hc.2.2; omega)
  have f4 := f3.setCR 0
  obtain ⟨τ5, e5, f5⟩ := ctrL_step cap s b h tl σ0 OFFw _ _ _ L 0 _ 0 hL f4 hc.2.2
  exact ⟨τ5, ERc', WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))), f5⟩

theorem lLoop_spec (hbs : b + 1 = 2 ^ s) (hc : LoopCap s b h tl cap) (out0 : List Bool) (m : ℕ) :
    ∀ (L : ℕ) (σ : WState GS GR) (ELc ERc : List Bool), L + m + 1 = 2 ^ (s * h) →
      FS s b h tl σ0 σ OFFw ELc ERc L 0 (out0 ++ outL s b h tl OFFw L) 0 1 →
      ∃ τ ELc' ERc', WExec cap lLoop σ τ ((m + 1) * (lBodyCost s b h tl + 2) + 1) ∧
        FS s b h tl σ0 τ OFFw ELc' ERc' (2 ^ (s * h) - 1) 0 (out0 ++ outL s b h tl OFFw (2 ^ (s * h))) 0 0 := by
  induction m with
  | zero =>
    intro L σ ELc ERc hLm hf
    obtain ⟨τ, ERc', e, f⟩ := lBody_spec cap s b h tl σ0 OFFw hbs hc σ ELc ERc L _ (by omega) hf
    have hn : ¬(L + 1 < 2 ^ (s * h)) := by omega
    rw [if_neg hn, if_neg hn, List.append_assoc, ← outL_succ, show L + 1 = 2 ^ (s * h) by omega] at f
    have hL' : L = 2 ^ (s * h) - 1 := by omega
    rw [hL'] at f
    exact ⟨τ, _, _, WExec.mono (WExec.whrT (by rw [hf.vgL]; omega) e (WExec.whrF f.vgL)) (by omega), f⟩
  | succ m ih =>
    intro L σ ELc ERc hLm hf
    obtain ⟨τ1, ERc1, e1, f1⟩ := lBody_spec cap s b h tl σ0 OFFw hbs hc σ ELc ERc L _ (by omega) hf
    have hy : L + 1 < 2 ^ (s * h) := by omega
    rw [if_pos hy, if_pos hy, List.append_assoc, ← outL_succ] at f1
    obtain ⟨τ, ELc', ERc', e2, f2⟩ := ih (L + 1) τ1 _ _ (by omega) f1
    exact ⟨τ, ELc', ERc', WExec.mono (WExec.whrT (by rw [hf.vgL]; omega) e1 e2) (by ring_nf; omega), f2⟩

end Loops

end NearCubicWires.WireExponent3_5.PrimT.Flips
