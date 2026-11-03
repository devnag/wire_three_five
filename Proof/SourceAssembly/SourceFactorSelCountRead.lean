import Proof.MachineModel.ClosureLocalSupport
import Proof.SourceAssembly.SourceRequestTermCompose

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.SourceFactorSel.CountRead
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RadixSemantics CanonicalBinary CanonicalWitnessCodec
open NearCubicWires.SourceRequest.TermSeg NearCubicWires.SourceRequest.TermReader NearCubicWires.SourceRequest.TermBridge

/-! ## One fixed machine, exact banks (`Fin 379`) -/

/-- Segment A on `0..190`. -/
def cA (i : Fin 191) : Fin 379 := ⟨i.val, by omega⟩
/-- Segment-B core: its input `0` on A's sum-code output `189`, its other tapes on `191..378`. -/
def cB (i : Fin 189) : Fin 379 := if i.val = 0 then ⟨189, by omega⟩ else ⟨190 + i.val, by omega⟩

noncomputable def countM :=
  Composition.machine (RecoveryFocus.machine cA machineA) (RecoveryFocus.machine cB SourceRequest.TermSegB.machine)

def countCost (bits : List Bool) (j : Nat) : Nat :=
  costA bits.length j + 1 + SourceRequest.TermSegB.cost bits.length

/-! ## Padded and docked: the `cntT` half of `ReaderRun` -/

end NearCubicWires.SourceFactorSel.CountRead

