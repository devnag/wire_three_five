import Proof.Wire_3_5.UnionMachine.ThrPipesBase
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

/-! # The THR unit machine at a gate and its run at every unit of a THR call (#186; THRU3's `ok`)

`thrUnitM` = the decode front `D.M` ; branch on register `398` into the RADIX pipe `ThrPipes.radP R`
(`RadSetupSpecB5`), else on `399` into the lifted FILTER pipe `FiltLift.filtP W hx F5`, else nothing ; the counter
increment (`UnitG.unitMG`). At a THR call:

* **`measC`**: the call's measure: the decode's need and bound at `n`, the counts' length, the RADIX measures
  `radMeas5` over every prime and star row (`rSup`), the FILTER setup's arguments over every row and star row
  (`fSup`), and the FILTER pipeline's bound `Kf·(fSup+2)^(Df·(e+2))` (`FiltPipeLe2`);
* `needU X = X + K_R·(X+1)^D_R + C_F·(X+1)^D_F`, `nUU` (the decode, the pipes at the capacity, the counter);
* **`unit_ok`**: `Shell.UnitOK cap x thrUnitM (nUU (measC + cap)) …` at every unit `j` and every
  `cap ≥ needU (measC) + j` (THRU3's `ok`): the decode's exit (`ThrDec.ThrDecOut`) is `UnitG.DecOKG`: idle units print
  their marker, RADIX request units run `radP` (`ThrPipes.radP_ok`, `emit_req`, `callUnit_rad`), FILTER request units
  run `filtP` (`FiltLift.filtP_ok`, `callUnit_filt`).

Paper quantity of the main type: the THR tape's unit `j` printed by the unit machine (the batch's markers and rows,
row:radix P3:2585-2623, row:matrix P3:1523-1526). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrUnitRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup NearCubicWires.WireExponent3_5.PrimT.WalkBank

theorem pipeOK_mono {cap x s : ℕ} {P : Machine (PrimAsm.CellLoop.TT x) s} {σ : WState (LNS x) LNR} {out e : List Bool}
    {B B' : ℕ} (h : UnitG.PipeOK cap P σ out e B) (hB : B ≤ B') : UnitG.PipeOK cap P σ out e B' := by
  obtain ⟨σF, s1, h1⟩ := h
  exact ⟨σF, s1.enlarge hB, h1⟩

section Gate

section Call

end Call

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.ThrUnitRun
