import Proof.Wire_3_5.UnionMachine.FiltLift
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
import Proof.Wire_3_5.UnionMachine.RadNeed
import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.UnionMachine.RadSpecBase
import Proof.Wire_3_5.UnionMachine.ThrDecIfaceBase
import Proof.Wire_3_5.UnionMachine.RadPipeB

/-! # The THR unit's pipes and emissions: RADIX (398) and FILTER (399) at a THR request unit

The THR tape's unit `j` (entry `e = j / EU`, `EU = thrEU |carriers|`; a request unit when `IsReqU`): its printed body
is row `r = rowOfU j` of the THR entry `(stOfU j, rowOfS j)` (`SymDec.symEmit_req`, `WriterIface.thrGrp`,
`Records.thrGroups`): `r < |carriers|` a FILTER row, `r = |carriers|` the RADIX row.

* `emit_req`, `callUnit_rad`, `callUnit_filt`: the unit's emission at a RADIX / FILTER request unit;
* `stOfU_lt`, `rowOfS_lt`, `rowOfU_le`: the index decode's ranges;
* **`radP R`** = the RADIX setup `R.M` (`RadSetupSpecB5`) ; the RADIX pipe `RadPipe.radPipeM`; **`radP_ok`**: from
  `RsIn4` at `(g, pr, s, row)` and `R.need (radMeas5 …) ≤ cap`, the RADIX row's body printed within
  `R.bound cap + 1 + (R.pipe (radMeas5 …) + 2)` (`UnitG.PipeOK`).

Paper quantity of the main type: the THR entry's rows printed at their units (row:radix P3:2585-2623, row:matrix
P3:1523-1526). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrPipes
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup

/-! ## The index decode's ranges -/

theorem thrEU_eq (nc : ℕ) : ThrDec.thrEU nc = 3 * nc + 5 := by unfold ThrDec.thrEU; ring

theorem rowOfU_le (nc j : ℕ) (h : j % ThrDec.thrEU nc < ThrDec.thrEU nc - 1) : ThrDec.rowOfU nc j ≤ nc := by
  unfold ThrDec.rowOfU
  rw [thrEU_eq] at h ⊢
  omega

section Call

end Call

/-! ## The RADIX pipe -/

section Rad

end Rad

end NearCubicWires.WireExponent3_5.UnionMachine.ThrPipes
