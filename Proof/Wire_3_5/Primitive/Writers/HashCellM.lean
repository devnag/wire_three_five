import Proof.Wire_3_5.Primitive.Writers.HashCellP
import Proof.Wire_3_5.Primitive.Writers.HashCellF

/-! # HASH setup (C), P2b part 6: the HASH cell as one machine

P3:3011-3016 (the setup before the loop): the HASH cell is one machine on its own tapes: the fill (`fillX`, the
registers at capacity `2W + 2`), then, beside the fill's two tapes, part A (`cAW`), the two docks (`docksM`), part B
and the populations program (`cBW ; popsW`), then PA's masked reset (every head back at `0`, a log tape of falses).
**`cell_step`**: from the cell's entry bank, given the three stages' runs at capacity `2W + 2`, the final tapes are the
last state's encoding, the fill's two tapes and the log.

* `cellPW`, `cellInner`, `cellP`, **`cellM`**, `cellCost`, **`cell_step`**.

Paper quantity of the main type: none (the machine's tapes carry the consumers' words: the kept words writer's
inputs on the cell's streams). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout

section Machine
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp) (cr : ℕ)

/-- Part B and the populations program. -/
noncomputable def cellPW : WM (LNS (cX T N)) LNR :=
  .seq (cBW (cX T N)) (HashPops.popsW (hPL (cX T N)) (HashPops.rowW (hPL (cX T N)) FinalPass.DigsBody.digsWImpl))

/-- The cell's program part on the layout's tapes: part A, the docks, part B and the populations. -/
noncomputable def cellInner :=
  Composition.machine (cAW (cX T N) cr).toProg.compile (Composition.machine (docksM T N) (cellPW T N).toProg.compile)

/-- The fill, then the program part beside the fill's two tapes. -/
noncomputable def cellP := Composition.machine (fillX (cX T N)).compile (TapeEmbedding.machine 2 (cellInner T N cr))

/-- **The HASH cell**: under the masked reset (every head back at `0`). -/
noncomputable def cellM := MaskedReset.machine (cellP T N cr) (fun _ => true)

/-- The cell's step bound from its stages'. -/
def cellCost (W cA cD cB : ℕ) : ℕ := 2 * (11 * W + 20 + 1 + 1 + 1 + (cA + 1 + (cD + 1 + cB))) + 2

/-- **The HASH cell, run**: given part A's run from the fresh cell, the docks' run and part B's and the populations'
run at capacity `2W + 2`. -/
theorem cell_step (w u : List Bool) (V W : ℕ) (τA τD τF : WState (LNS (cX T N)) LNR) (cA cD cB : ℕ)
    (hA : WExec (2 * W + 2) (cAW (cX T N) cr) (CellLoopD.blankCellD (cX T N) w [] V u) τA cA)
    (hD : Step (docksM T N) cD (wenc (2 * W + 2) τA).H (wenc (2 * W + 2) τA).A (wenc (2 * W + 2) τD).H
      (wenc (2 * W + 2) τD).A)
    (hB : WExec (2 * W + 2) (cellPW T N) τD τF cB) :
    ∃ m, Step (cellM T N cr) (cellCost W cA cD cB) (fun _ => 0)
      (Fin.addCases (rawX (cX T N) w u V W) (fun _ : Fin 1 => [])) (fun _ => 0)
      (Fin.addCases (Fin.addCases (wenc (2 * W + 2) τF).A (xB W)) (fun _ : Fin 1 => List.replicate m false)) := by
  have s0 := Exec.step (fillX_exec (cX T N) w u V W)
  have sA := Exec.step (WExec.exec (2 * W + 2) hA)
  have sB := Exec.step (WExec.exec (2 * W + 2) hB)
  have sI : Step (cellInner T N cr) (cA + 1 + (cD + 1 + cB)) (wenc (2 * W + 2) (CellLoopD.blankCellD (cX T N) w [] V u)).H
      (wenc (2 * W + 2) (CellLoopD.blankCellD (cX T N) w [] V u)).A (wenc (2 * W + 2) τF).H (wenc (2 * W + 2) τF).A :=
    Step.seq sA (Step.seq hD sB)
  have s1 := sI.embed (fun _ : Fin 2 => 0) (xB W)
  have core : Step (cellP T N cr) (11 * W + 20 + 1 + 1 + 1 + (cA + 1 + (cD + 1 + cB))) (fun _ => 0)
      (rawX (cX T N) w u V W) (Fin.addCases (wenc (2 * W + 2) τF).H (fun _ : Fin 2 => 0))
      (Fin.addCases (wenc (2 * W + 2) τF).A (xB W)) := s0.seq s1
  obtain ⟨m, hm⟩ := ListMachine.Row.maskBlank core (fun _ => true) (fun _ _ => rfl) 0
  have eh : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (BX (cX T N) + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have eh' : (Fin.addCases (fun i : Fin (BX (cX T N)) => if (fun _ => true) i = true then 0 else
      (Fin.addCases (wenc (2 * W + 2) τF).H (fun _ : Fin 2 => 0) : Fin (BX (cX T N)) → ℕ) i)
      (fun _ : Fin 1 => 0) : Fin (BX (cX T N) + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  exact ⟨m, (hm.congr_in eh rfl).congr eh' rfl⟩

end Machine

end NearCubicWires.WireExponent3_5.PrimAsm.HashCell
