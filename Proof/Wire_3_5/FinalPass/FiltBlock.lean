import Proof.Wire_3_5.FinalPass.FiltEval
import Proof.Wire_3_5.FinalPass.PopList

/-! # Final pass, stage 7 as blocks: the regular filter at a point, alone and after stage 3

**`stage7_step`**: the regular filter's per-point evaluator in C2's `PointEval` shape: one machine
`stage7Machine` on `2 + 9` tapes (the framed point, the result cell, the seed's table word, the threshold `1^thr 0`,
7 blank registers of capacity `c + 1` for any `c ≥ capOf7`), the cell becomes `[tabEval thr tbl Z]`.
**`stage7_filter`**: at the seed's table (`filterTable P e L`) and the majority threshold, the cell is the regular
filter `filterBits P e Z` of `filt:gap` (`filterBits_eq_tab`).

**`stage37_step`** / **`stage37_filter`**: C2's corner-point evaluator for the filter: stage 3
(`pop`) writes the population bits `popBits sgn X` on a scratch tape, stage 7 runs on it (`RExec.lift`), the scratch is
blanked again (`blankOut`, self-restoring); the cell becomes `[filterBits P e (popBits sgn X)]`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.SupplierWalk
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Block

/-! ## Stage 7 alone -/

/-! ## Stage 3 then stage 7 -/

/-- **The composite program**: stage 3, stage 7 on the scratch, blank the scratch. -/
def comp37 : WM 4 7 := .seq (pop 0 3 4 0) (.seq (main7.lift fs5) (blankOut 0 3 4 0))

/-- **The stage-3∘7 machine** (one for every table, threshold, sign and point). -/
def stage37Machine : Machine (2 + 11) comp37.toProg.size := comp37.toProg.compile

/-- The evaluator's own tapes: the table word, the threshold, the scratch, the sign cell, 7 registers. -/
def stage37Data (tbl : List (List (List Bool))) (thr : ℕ) (sgn : Bool) (c : ℕ) : Fin 11 → List Bool := fun i =>
  if i.val = 0 then tableWord tbl
  else if i.val = 1 then ListEval.unary thr
  else if i.val = 3 then [sgn]
  else List.replicate (c + 1) false

/-- One step bound for every point of `L` occurrences. -/
def stage37Cost (W thr L : ℕ) : ℕ := passCost L + 1 + (cost7 W thr + 1 + passCost L)

/-- **The stage-3∘7 evaluator** (C2's `PointEval.step` for `f X = [tabEval thr tbl (popBits sgn X)]`). -/
theorem stage37_step (tbl : List (List (List Bool))) (thr L : ℕ) (sgn : Bool) (c : ℕ)
    (hlen : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ L) (hc : capOf7 L tbl thr ≤ c)
    (X : List Bool) (b : Bool) (hX : X.length = 4 * L) :
    Step stage37Machine (stage37Cost (tableWord tbl).length thr L) (fun _ => 0)
      (Fin.addCases (m := 2) (n := 11) ![frame X, [b]] (stage37Data tbl thr sgn c)) (fun _ => 0)
      (Fin.addCases (m := 2) (n := 11) ![frame X, [tabEval thr tbl (popBits sgn X)]] (stage37Data tbl thr sgn c)) := by
  have hcL : 2 * L + 40 ≤ c := by unfold capOf7 at hc; omega
  have hZl : (popBits sgn X).length = L := popBits_length sgn L X hX
  generalize hd : tabEval thr tbl (popBits sgn X) = d
  obtain ⟨σ0, hσ0⟩ : ∃ σ : WState 4 7, σ = ⟨fun _ => 0, st35 X (tableWord tbl) thr sgn c, fun _ => 0, b⟩ :=
    ⟨_, rfl⟩
  -- stage 3
  have e1 := pop_spec c 0 3 4 0 (by decide) (by decide) (by decide) sgn L X [] (List.replicate (c + 1) false) σ0 hX
    (by rw [hσ0]; simp [st35, frame_eq_frameP]) (by rw [hσ0]) (by rw [hσ0]; rfl) (by rw [hσ0]) (by simp; omega)
    (by rw [hσ0]; rfl) (by rw [hσ0]) (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ σ : WState 4 7,
      σ = σ0.sets 3 (frameP (popBits sgn X) ++ (List.replicate (c + 1) false).drop (2 * L)) := ⟨_, rfl⟩
  rw [← hσ1] at e1
  -- stage 7, lifted
  have m7 := main7_spec c (popBits sgn X) tbl thr b (fun vs hvs cs hcs => (hlen vs hvs cs hcs).trans hZl.symm.le)
    (by rw [hZl]; exact hc)
  rw [hd] at m7
  have hrel : LiftRel fs5 (streams7 (popBits sgn X) tbl thr) σ1 (S7 0 0 0 0 0 0 0 b) := by
    refine ⟨fun i => by rw [hσ1, hσ0]; fin_cases i <;> rfl, fun i p => ?_, by rw [hσ1, hσ0]; funext i; fin_cases i <;> rfl,
      by rw [hσ1, hσ0]; rfl⟩
    fin_cases i
    · rw [hσ1]
      simp only [WState.sets_st, fs5, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Function.update_self,
        List.drop_replicate, streams7]
      exact readTapeBit_frame_pad _ _ _
    · rw [hσ1, hσ0]; rfl
    · rw [hσ1, hσ0]; rfl
  obtain ⟨ω2, e2, r2, o2⟩ := RExec.lift _ _ c le_rfl fs5 fs5_inj m7 σ1 hrel
  have hω2 : ω2 = ⟨fun _ => 0, σ1.st, fun _ => 0, d⟩ := by
    refine WState.eq ?_ o2.1 (r2.val.trans (by funext i; fin_cases i <;> rfl)) r2.cell
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
    (⟨fun _ => 0, σ1.st, fun _ => 0, d⟩ : WState 4 7) hX
    (by show σ1.st 0 = _; rw [hσ1, hσ0]; simp [st35, frame_eq_frameP]) rfl hst3 rfl
    (by simp [hZl]) (by show readTapeBit (σ1.st 4) 0 = sgn; rw [hσ1, hσ0]; rfl) rfl (by omega)
  have hfin : (⟨fun _ => 0, σ1.st, fun _ => 0, d⟩ : WState 4 7).sets 3
      (List.replicate (2 * L) false ++ (frameP (popBits sgn X) ++ (List.replicate (c + 1) false).drop (2 * L)).drop
        (2 * L)) = ⟨fun _ => 0, st35 X (tableWord tbl) thr sgn c, fun _ => 0, d⟩ := by
    rw [blank_restore L (c + 1) _ (by simp [hZl]) (by omega)]
    refine WState.eq rfl ?_ rfl rfl
    funext j
    simp only [WState.sets_st, Function.update_apply]
    split_ifs with hj
    · subst hj; rfl
    · rw [hσ1, hσ0]; simp [Function.update_of_ne hj]
  rw [hfin] at e3
  have hs7 := (WExec.exec c (WExec.seq e1 (WExec.seq e2 e3))).step
  refine Step.congr (Step.congr_in hs7 ?_ ?_) ?_ ?_
  · funext j; rw [hσ0]; simp only [wenc]; split <;> rfl
  · funext j; rw [hσ0]; fin_cases j <;> simp [wenc, role, st35, regTape_zero] <;> rfl
  · funext j; simp only [wenc]; split <;> rfl
  · funext j; fin_cases j <;> simp [wenc, role, st35, regTape_zero] <;> rfl

/-! ## Costs -/

end NearCubicWires.WireExponent3_5.FinalPass.Filt
