import Lean
import Proof.Wire_3_5.FinalPass.DigsIface
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup2
import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellIface
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.UnionMachine.RadSpecBase
import Proof.Wire_3_5.UnionMachine.ThrDecIfaceBase
import Proof.Wire_3_5.Primitive.Writers.SymDecEmit
import Proof.Wire_3_5.UnionMachine.ThrDecIface
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split


noncomputable section
set_option maxRecDepth 4096


/-! # THRTAIL, part 1: the THR tape is the writer loop's units

P3:3011-3016 (C4's `BAT` word of the call: the entries of every state and star row), the THR twin of
`SymFlat.symTape_flat` / `SymDec.sym_loop_tape`: the THR tape `thrTape` (the blocks of `thrEnts`, the chunked THR
batch) is the writer loop's emission over `thrTOT = thrNT·N²·thrEU` units, each entry `thrEU = (nc+1)·3 + 2` units
(`[true]`, per row `[true]`, the row's request `thrCallUnit`, `[false]`, then `[false]`), closed by `false`
(`chunk_batchOf`, `units_blockWord` at `R = nc + 1`, `M = 0`); past `thrTOT` the loop prints nothing
(`flatMap_unitE`).

* **`thrTape_flat`**, **`thr_loop_tape`**.

Paper quantity of the main type: the THR tape `thrTape` (P3:3011-3016). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrTail
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ}
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)

/-- **The THR tape is the writer loop's units, closed.** -/
theorem thrTape_flat :
    (List.range (UnionMachine.ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers)).flatMap
      (SymFlat.symEmit (carriers.length + 1) 0 (UnionMachine.ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation)) ++
      [false] = WriterIface.thrTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation := by
  unfold WriterIface.thrTape WriterIface.thrEnts WriterIface.thrExprs WriterIface.batchExprs WriterIface.thrBatchE
  rw [SymFlat.chunk_batchOf _ _ _ _ (fun t row => WriterIface.thrGrp_length _ _ hs Cs carriers translation t row)]
  unfold UnionMachine.ThrDec.thrTOT UnionMachine.ThrDec.thrEU UnionMachine.ThrDec.thrN2
  refine SymFlat.units_blockWord (carriers.length + 1) 0 _ _ _
    (fun e _ => WriterIface.thrGrp_length _ _ hs Cs carriers translation _ _) (fun e _ r _ => ?_)
  simp only [Nat.zero_add, List.range_one, List.flatMap_singleton]
  rfl

/-- **The THR writer loop's output is the THR tape**: `b ≥ thrTOT` units, closed by `false`. -/
theorem thr_loop_tape (b : ℕ) (hb : UnionMachine.ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers ≤ b) :
    (List.range b).flatMap (SymDec.unitE (UnionMachine.ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers)
      (carriers.length + 1) 0 (UnionMachine.ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation)) ++
      [false] = WriterIface.thrTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation := by
  rw [SymDec.flatMap_unitE _ _ _ _ _ hb]
  exact thrTape_flat l F kclk coef A a ha hs Cs carriers translation

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.ThrTail

end
