import Proof.Wire_3_5.Primitive.SeedFix.C4HkI
import Proof.Wire_3_5.FinalPass.HashFreeBase

/-! # The HASH stage, part 10: one stage for every THR call, and its run at a call

"Greedily choose a child with no larger value [...] the printed decisions are the fixed hash's bits" (P3:2327-2336).
The HASH stage's machine does not depend on the call: its loop is the loop of the proof-free family `famUH A wa`
(`C4Hf.chFamH`'s machine fields depend only on C6's assembler and the printer's algorithm; `hash_uniform`, by `rfl`), so
one `Stage3` (**`hashStageU`**) serves every call. **`hash_call_run`**: at a THR call, with the free numbers
(`HashFreeOk2`: `HashEAt` and `caps_ge`) and any setup run to a C4H-a `HBank2` bank at the call's words, the stage
ends with `frame (thrIn …)` (the THR writer's input) within any budget above its steps.

* `famUH`, `hashStageU`, `hash_uniform`, **`hash_call_run`**.

Paper quantity of the main type: the THR writer's input `req.word ++ frame hashBits` at a call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hk
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapM wrapCost)

/-- **The HASH loop's family without call data**: the machine fields of every HASH child family. -/
noncomputable def famUH (A0 : C4Iface.AsmStage) (wa : RepairRepresentation.WilliamsAlgorithm) : C4Loop.ChildFam where
  t := C4H.CTH A0 wa + 1
  s := _
  M := C4Hf.chMHs A0 wa
  cost := 0
  PFX := C4Hf.hPfxT A0 wa
  SUM := C4Hf.hSumP A0 wa
  keep := C4Hf.hKeepF A0 wa
  hPFX := C4Hf.hKeepF_pfx A0 wa
  hSUM := C4Hf.hKeepF_sum A0 wa
  K := fun _ => []
  W := 0
  bound := 0
  val := fun _ => 0
  run := fun _ _ h => absurd h (Nat.not_lt_zero _)

/-- **The HASH stage** at the uniform family (the setup `M0`, its layout and kept tapes). -/
noncomputable def hashStageU {x s0 : ℕ} (L : C4Set.Lay) (hLx : L.N ≤ 3 + x) (M0 : Machine (3 + x) s0)
    (wa : RepairRepresentation.WilliamsAlgorithm) (hkT : Fin 94 → Fin (3 + x)) (hqT : Fin (3 + x)) (off : ℕ)
    (hroom : off + 12 + ((famUH UnionMachine.TailAsm.asmStage wa).T + 1 + 1 + 1) + (2 + 2 + 0 + 1) ≤ 3 + x) :
    SeedFixTypes.Stage3 :=
  ⟨x, _, wrapM (setupH L hLx M0 hkT off (by omega) ((famUH UnionMachine.TailAsm.asmStage wa).T + 1 + 1 + 1))
    (famUH UnionMachine.TailAsm.asmStage wa) (off + 12) (by omega)
    (hashExt L hLx UnionMachine.TailAsm.asmStage wa hkT hqT off (by omega) (famUH UnionMachine.TailAsm.asmStage wa).T)
    finM (off + 12 + ((famUH UnionMachine.TailAsm.asmStage wa).T + 1 + 1 + 1)) hroom (finExtH off (by omega))⟩

section Call

end Call

end NearCubicWires.WireExponent3_5.PrimT.C4Hk
