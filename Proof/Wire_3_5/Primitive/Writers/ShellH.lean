import Proof.Wire_3_5.Primitive.Writers.ShellERun
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3

/-! # The THR/HASH writer shell over `ThrDataStage3` (the THR numbers on the data tape)

The shell over a `ThrDataStage2` (`ShellEBoot`/`ShellERun`: `st8E`, `pre_stepE`, `x0_stepE`, `bootX_stepE`,
`shell_runE`) with the data stage v3 (`ThrData.ThrDataStage3`, the producer): the machines take `M3`
(`M8TH`, `preMTH`, `MX0TH`, `bootXMGH`, `shellMGH`), the proofs are the with `S.run3` (the data word
`hashNums ++ thrCounts`, W6's numbers once per call, ruling (B) of) and the size hypotheses `ThrDataOK2` plus the
longer word's fill (`hcu3`), the call envelope's description bound (`hdesc`) and W6's need (`hneed`).

* `M8TH`, `preMTH`, `MX0TH`, `bootXMGH`, `shellMGH`;
* `st8H`, **`pre_stepH`**, `x0_stepH`, **`bootX_stepH`** (any `DimOK` stage), **`shell_runH`** (any unit machine with
  `UnitOK` over the data tape `unaryList (hashNums ++ thrCounts)`).

Paper quantity of the main type: the THR call's slice lengths and THR numbers (the aux filter's `e`, the fixed hash's
`M, A, B_*, J, t`, the primes, `τ₀`) on the writer's data tape (lem:primitive P3:3068-3084; filt:soft P3:2220-2231). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.Shell (install_eq dockH_eq)
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.CellUnit
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimAsm.ShellD
open NearCubicWires.WireExponent3_5.PrimAsm.ShellX NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.Streaming (marks)

section Machines

end Machines

section Data

end Data

section Pre

end Pre

section Boot

end Boot

section Run

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.ShellT
