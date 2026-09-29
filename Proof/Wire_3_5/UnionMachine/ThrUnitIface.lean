import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellIface
import Proof.Wire_3_5.Primitive.Writers.HashLeafIface4
import Proof.Wire_3_5.UnionMachine.ThrDecIface

/-! # The THR unit machine's contract: the split between the unit and the THR leaf's tail

P3:2543-2558 (the THR call's numbers once per call), P3:2019-2054 (the FILTER rows), P3:2585-2623 (the RADIX row); the
THR tape `thrTape` is the units' emissions `SymDec.unitE (thrTOT) (|carriers|+1) 0 thrCallUnit`, one unit per cell of
the shell's loop (`PrimThrW.Shell.UnitOK`, from the fresh cell `CellLoopD.blankCellD x w out j u`).

* **`ThrUnitSpec l F`**: one unit machine per gate on the cell layout `LNS x`, with quasi-bounded capacity `need`
  and unit budget `nU`, meeting `UnitOK` at every THR call, every output `out`, every unit `j` and capacity
  `≥ need n + j`, with the request word `ThrDec.thrCallW` (request, then the fixed hash's bits, framed), the counts
  `ThrDec.thrCallU` on the data tape (the v4 data stage's word) and the emission `SymDec.unitE … thrCallUnit`;
* **`ThrUnitU l`**: `ThrUnitSpec` in the order of choice of `WritersJoin.ThrLeafJ2` (`Seams.StageU`: the exponents
  `Dn, Kn, Du, Ku` with the envelope, from `(l, fe)` only; the coefficients `Cn, Cu` after `F`);
* **`ThrLeafOfU l`**: the v4 data stage (`ThrStage4U`) and the unit machines give the THR writer's leaf;
* **`ThrUnitOf l`** (the producer statement): the uniform decode fronts (`ThrDec.ThrDecFront`) and RADIX setups
  (`RadSetupB3.RadSetupSpecB3`) on the unit cells `xF F ≥ W.x`, the FILTER setup `FiltSetupSpec5 W` and its pipe
  bound give the unit machines (inside: `radPipe_readyB`, the FILTER setup lifted to `xF F`, the pipes, `incW`).

Paper quantity of the main type: the THR tape's units (each unit's printed row of the THR batch). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.RadSetup

/-- The decode front's exponents and coefficients. -/
def decDeg {x : ℕ} {l : Literals} {F : GateFree l} (D : ThrDec.ThrDecFront x l F) : ℕ :=
  max (max D.Dn D.Kn) (max D.Db D.Kb)

def decCf {x : ℕ} {l : Literals} {F : GateFree l} (D : ThrDec.ThrDecFront x l F) : ℕ := D.Cn + D.Cb

end NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
