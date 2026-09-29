import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup

/-! # THR, W7 seam v2: the RADIX setup's entry with `ncar` and `cap_T` (`RsIn2`, `RadSetupSpec2`)

P3:2585-2623 (row:radix), as `RadSetup`: the RADIX row's setup docks the equation writer (`EqW.EqWPort`) and the THR
numbers (`NumsP.NumsPort`), whose in-ports need the carrier count and the THR filter's cap. `RsIn` has
neither, so v2 adds them:

* `rNcK = 430`, `rCapK = 431`;
* **`RsIn2`**: `RsIn` with `ncar` in `430` and `cap_T` in `431` (registers outside `250 … 399` and `410 … 431` zero);
* **`RadSetupSpec2 x l F`**: `RadSetupSpec` from `RsIn2` at `ncar = |carriers|`, `cap_T = (filterParams .thr n).cap`.

Paper quantity of the main type: the RADIX row's C2 request (`RadSetup.radReqOf`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.RadSetup2
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup

/-- The carrier count's register. -/
def rNcK : Fin LNR := ⟨430, by decide⟩
/-- The THR filter cap's register. -/
def rCapK : Fin LNR := ⟨431, by decide⟩

end NearCubicWires.WireExponent3_5.PrimThrW.RadSetup2
