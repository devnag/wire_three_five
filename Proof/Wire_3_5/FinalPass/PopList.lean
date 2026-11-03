import Proof.Wire_3_5.FinalPass.Pop
import Proof.Wire_3_5.FinalPass.Lift
import Proof.Wire_3_5.MachineModel.BlockCost
import Proof.Wire_3_5.FinalPass.ListEvalMain

/-! # Final pass: stage 3 then stage 5, C2's point evaluator over the corners

"C2's point evaluator = C5's stage 3 (corners → Z±) followed by stage 5/7" (P3:2782-2783: the
expansions are polynomials in the corner threshold atoms). This module is that evaluator for stage 5 in C2's
`PointEval` shape: one machine `stage35Machine` on `2 + 19` tapes for every row and both signs.

- tape 0: the framed corners `frame X`, four per gate occurrence (`Pop.popBits`);
- tape 1: the result cell;
- tapes `2..20` (`stage35Data`): the table word, the compared state `1^s 0`, the scratch, the sign cell `[sgn]`, and
  15 registers; the scratch and the registers are blank (`replicate (c+1) false`) for any `c ≥ capOf …`.

The program `comp35` runs stage 3 (`pop`: the scratch becomes `frameP (popBits sgn X)`), then stage 5's register
program lifted onto the scratch (`RExec.lift`: the padded scratch reads like `frame Z`), then `blankOut` (the scratch is
blank again, so the evaluator is self-restoring).

**`stage35_step`**: the cell becomes `[reportRef M J W row (popBits sgn X) = s]`, every other tape is returned
exactly and every head returns to `0`, within `stage35Cost` (one bound for all points). `reportRef` is
`ListFast.listReportFast` (`reportRef_eq_fast`). **`stage35_cost_le`**: `≤ 36576·q³` at the description size. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Block

/-- Stage 5's streams inside the composite: its point is the scratch (stream 3). -/
def fs5 : Fin 3 → Fin 5 := ![3, 1, 2]

theorem fs5_inj : Function.Injective fs5 := by decide

/-- **The composite program**: stage 3, stage 5 on the scratch, blank the scratch. -/
def comp35 : WM 4 15 := .seq (pop 0 3 4 0) (.seq (ListEval.main.lift fs5) (blankOut 0 3 4 0))

/-- **The stage-3∘5 machine** (one for every table, state, sign and point). -/
def stage35Machine : Machine (2 + 19) comp35.toProg.size := comp35.toProg.compile

section
variable (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (L s : ℕ) (sgn : Bool) (c : ℕ)

/-- The evaluator's own tapes: the table word, the compared state, the scratch, the sign cell, 15 registers. -/
def stage35Data : Fin 19 → List Bool := fun i =>
  if i.val = 0 then levelWord M J W row
  else if i.val = 1 then unary s
  else if i.val = 3 then [sgn]
  else List.replicate (c + 1) false

/-- One step bound for every point of `L` occurrences. -/
def stage35Cost : ℕ := passCost L + 1 + (mainCost (capOf M J W row L) + 1 + passCost L)

end

/-- The stream contents of the composite at entry. -/
def st35 (X lw : List Bool) (s : ℕ) (sgn : Bool) (c : ℕ) : Fin 5 → List Bool :=
  ![frame X, lw, unary s, List.replicate (c + 1) false, [sgn]]

theorem readTapeBit_frame_pad (w : List Bool) (k p : ℕ) :
    readTapeBit (frameP w ++ List.replicate k false) p = readTapeBit (frame w) p := by
  rw [readTapeBit_pad, frame_eq_frameP, show [false] = List.replicate 1 false from rfl, readTapeBit_pad]

/-- **The stage-3∘5 evaluator** (C2's `PointEval.step` for `f X = [reportRef M J W row (popBits sgn X) = s]`). -/
theorem stage35_step (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (L s : ℕ) (sgn : Bool) (c : ℕ)
    (hrows : ∀ j ≤ J, (row j).length = L) (hs : s ≤ M) (hc : capOf M J W row L ≤ c)
    (X : List Bool) (b : Bool) (hX : X.length = 4 * L) :
    Step stage35Machine (stage35Cost M J W row L) (fun _ => 0)
      (Fin.addCases (m := 2) (n := 19) ![frame X, [b]] (stage35Data M J W row s sgn c)) (fun _ => 0)
      (Fin.addCases (m := 2) (n := 19) ![frame X, [decide (reportRef M J W row (popBits sgn X) = s)]]
        (stage35Data M J W row s sgn c)) := by
  have hcL : 4 * L + 4 ≤ c := by unfold capOf at hc; omega
  have hZl : (popBits sgn X).length = L := popBits_length sgn L X hX
  generalize hd : decide (reportRef M J W row (popBits sgn X) = s) = d
  -- the entry state
  obtain ⟨σ0, hσ0⟩ : ∃ σ : WState 4 15, σ = ⟨fun _ => 0, st35 X (levelWord M J W row) s sgn c, fun _ => 0, b⟩ :=
    ⟨_, rfl⟩
  -- stage 3
  have e1 := pop_spec c 0 3 4 0 (by decide) (by decide) (by decide) sgn L X [] (List.replicate (c + 1) false) σ0 hX
    (by rw [hσ0]; simp [st35, frame_eq_frameP]) (by rw [hσ0]) (by rw [hσ0]; rfl) (by rw [hσ0]) (by simp; omega)
    (by rw [hσ0]; rfl) (by rw [hσ0]) (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ σ : WState 4 15,
      σ = σ0.sets 3 (frameP (popBits sgn X) ++ (List.replicate (c + 1) false).drop (2 * L)) := ⟨_, rfl⟩
  rw [← hσ1] at e1
  -- stage 5, lifted
  have m5 := main_spec M J W row (popBits sgn X) s b (fun j hj => (hrows j hj).trans hZl.symm) hs
  rw [hZl, hd] at m5
  have hrel : LiftRel fs5 (streams M J W row (popBits sgn X) s) σ1 (blank b) := by
    refine ⟨fun i => by rw [hσ1, hσ0]; rfl, fun i p => ?_, by rw [hσ1, hσ0]; rfl, by rw [hσ1, hσ0]; rfl⟩
    fin_cases i
    · rw [hσ1]
      simp only [WState.sets_st, fs5, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Function.update_self,
        List.drop_replicate, streams]
      exact readTapeBit_frame_pad _ _ _
    · rw [hσ1, hσ0]; rfl
    · rw [hσ1, hσ0]; rfl
  obtain ⟨ω2, e2, r2, o2⟩ := RExec.lift _ _ c hc fs5 fs5_inj m5 σ1 hrel
  -- the state after stage 5
  have hω2 : ω2 = ⟨fun _ => 0, σ1.st, fun _ => 0, d⟩ := by
    refine WState.eq ?_ o2.1 r2.val r2.cell
    funext j
    fin_cases j
    · show ω2.sh 0 = 0
      rw [o2.2 0 (by decide), hσ1, hσ0]; rfl
    · exact r2.sh 1
    · exact r2.sh 2
    · exact r2.sh 0
    · show ω2.sh 4 = 0
      rw [o2.2 4 (by decide), hσ1, hσ0]; rfl
  subst hω2
  have hst3 : σ1.st 3 = frameP (popBits sgn X) ++ (List.replicate (c + 1) false).drop (2 * L) := by
    rw [hσ1]; simp
  -- blank the scratch
  have e3 := blank_spec c 0 3 4 0 (by decide) (by decide) (by decide) sgn L X [] _
    (⟨fun _ => 0, σ1.st, fun _ => 0, d⟩ : WState 4 15) hX
    (by show σ1.st 0 = _; rw [hσ1, hσ0]; simp [st35, frame_eq_frameP]) rfl hst3 rfl
    (by simp [hZl]) (by show readTapeBit (σ1.st 4) 0 = sgn; rw [hσ1, hσ0]; rfl) rfl (by omega)
  have hfin : (⟨fun _ => 0, σ1.st, fun _ => 0, d⟩ : WState 4 15).sets 3
      (List.replicate (2 * L) false ++ (frameP (popBits sgn X) ++ (List.replicate (c + 1) false).drop (2 * L)).drop
        (2 * L)) = ⟨fun _ => 0, st35 X (levelWord M J W row) s sgn c, fun _ => 0, d⟩ := by
    rw [blank_restore L (c + 1) _ (by simp [hZl]) (by omega)]
    refine WState.eq rfl ?_ rfl rfl
    funext j
    simp only [WState.sets_st, Function.update_apply]
    split_ifs with hj
    · subst hj; rfl
    · rw [hσ1, hσ0]; simp [Function.update_of_ne hj]
  rw [hfin] at e3
  have hs5 := (WExec.exec c (WExec.seq e1 (WExec.seq e2 e3))).step
  refine Step.congr (Step.congr_in hs5 ?_ ?_) ?_ ?_
  · funext j; rw [hσ0]; simp only [wenc]; split <;> rfl
  · funext j; rw [hσ0]; fin_cases j <;> simp [wenc, role, st35, regTape_zero] <;> rfl
  · funext j; simp only [wenc]; split <;> rfl
  · funext j; fin_cases j <;> simp [wenc, role, st35, regTape_zero] <;> rfl

end NearCubicWires.WireExponent3_5.FinalPass.Pop
