import Lean
import Proof.Wire_3_5.FinalPass.CoreJ10
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.CoreJ11


noncomputable section
set_option maxRecDepth 4096


/-! # S5Core over the writers with arbitrary residues, part J15: the core half's exit (P3:3044-3048, 3170-3181)

* **`exitA L r`**: the front's exit bank (`FrontOut` at `frontWordsW2`): the words on their tapes, `Num = 0` and
  `Den = fpDen` in `Tf`-bit binary on `tN`, `tD`, every other tape `0^{blOf2}`; `exitA_wd`, `exitA_tN`, `exitA_tD`,
  `exitA_blank`;
* **`stageFJ`**: the final pad (every register tape off the words and the numbers padded against `TcJ`, then `TcJ`
  erased).

Paper quantities: the front's words and the printed numbers' start (P3:3044-3048, 3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Exit

end Exit

section Final
variable {l : Literals} (W : CoreWritersJ l) {mTh : ℕ} (L : S5Lay Sw0.nw) (hR : Bank.HalfRoom2 L mTh (mCoreOfJ W))

/-- **The final pad.** -/
theorem stageFJ (c : ℕ) (A6 : Fin L.t → List Bool) (hT : A6 (TcJ W L hR) = sent c)
    (hlen : ∀ y ∈ regList L (TcJ W L hR), (A6 y).length ≤ c + 1) :
    Step (finPJ W L hR).compile (finCost (regList L (TcJ W L hR)).length c) (fun _ => 0) A6 (fun _ => 0)
      (Function.update (fun i => if i ∈ regList L (TcJ W L hR) then List.replicate (c + 1) false else A6 i)
        (TcJ W L hR) (List.replicate (c + 1) false)) := by
  classical
  have hTn : TcJ W L hR ∉ regList L (TcJ W L hR) := fun h => ((mem_regList L _ _).1 h).2.2.2.2 rfl
  have e1 := padList_exec (TcJ W L hR) c (regList L (TcJ W L hR)) ⟨fun _ => 0, A6⟩ (regList_nodup L _) hTn hT rfl
    (fun j hj => ⟨rfl, hlen j hj⟩)
  have e2 := eraseS_exec (TcJ W L hR) c ⟨fun _ => 0, fun i => if i ∈ regList L (TcJ W L hR) then
    List.replicate (c + 1) false else A6 i⟩ (by simp only [if_neg hTn]; exact hT) rfl
  exact Exec.step (Exec.seq e1 e2)

end Final

end NearCubicWires.WireExponent3_5.FinalPass.Core

end
