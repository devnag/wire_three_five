import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.Primitive.Writers.FiltSetupIface2
import Proof.Wire_3_5.Primitive.Writers.CellLoopD
import Proof.Wire_3_5.Primitive.Writers.SymDecBr
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3

/-! # The THR unit's decode front: the contract between the decode (T3) and the unit machine (C6b)

P3:2543-2558 (the THR call's numbers once per call), P3:2019-2054 (the FILTER rows), P3:2585-2623 (the RADIX row);
the THR tape's units as in `SymFlat.symEmit (|carriers|+1) 0` (per entry `[true]`, per row `[true]`, the row's
request, `[false]`, then `[false]`; `thrEU nc = (nc+1)·3 + 2` units per entry). From the unit's fresh cell
`CellLoopD.blankCellD x w out j u` (the call's request word `w`, the counts `u` on `113`), the decode front leaves:

* at a RADIX request unit (row `r = nc`): register `rRadK ≠ 0`, `rFltK = 0`, and the RADIX setup's entry
  `RadSetupB3.RsIn4` at the unit's `(g, p, s, row)` (W6's words on `130 … 132`, the payloads on `133 … 136`);
* at a FILTER request unit (row `r < nc`): `rRadK = 0`, `rFltK ≠ 0`, and the FILTER setup's entry `FiltSetup.FsIn2` at
  the unit's seed and row slice (`FiltDock5.thrFilt_dock5`'s form);
* at every other unit: both registers `0`, the flags `150`, `151` blank and the unit's emission (a marker, or nothing
  past the call's units) printed: `CellUnit.DecOK`'s first disjunct;
* in every case: the request kept (head `0`) and the counter `1^j` (head `0`).

**`ThrDecFront x l F`**: one machine on the cell layout `LNS x` per gate, quasi-bounded capacity `need` and cost
`bound` in `n`, running at every THR call, every unit `j` and every capacity `≥ need n + j`.

Paper quantity of the main type: the THR call's rows (FILTER and RADIX) at each unit of the THR tape. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
open NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB3

/-- The RADIX branch's marker register. -/
def rRadK : Fin LNR := ⟨398, by decide⟩

/-- The FILTER branch's marker register. -/
def rFltK : Fin LNR := ⟨399, by decide⟩

/-- The units per entry of the THR tape: `[true]`, per row `[true]`, the request, `[false]`, then `[false]`. -/
def thrEU (nc : ℕ) : ℕ := (nc + 1) * (0 + 3) + 2

/-- Unit `j` is a request unit (the middle unit of a row) of the first `TOT` units. -/
def IsReqU (TOT nc j : ℕ) : Prop :=
  j < TOT ∧ j % thrEU nc ≠ 0 ∧ j % thrEU nc < thrEU nc - 1 ∧ (j % thrEU nc - 1) % 3 = 1

/-- A request unit's row index `r` (`r < nc`: FILTER, `r = nc`: RADIX). -/
def rowOfU (nc j : ℕ) : ℕ := (j % thrEU nc - 1) / 3

section Call


end Call

end NearCubicWires.WireExponent3_5.UnionMachine.ThrDec
