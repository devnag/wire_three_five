import Proof.Rows.CellGatePalette

/-! Actual paid gate call from eight resident masters. Fanout constructs the
entire evaluator bank, the canonical native evaluator appends its verdict,
and a bounded sweep restores the exact cleared bank for the next call. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_CellGate
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.P1Closure NearCubicWires.ExtIncidence
open NearCubicWires.RepairRepresentation
open PCJ45bee56da9f34d5a_CellGatePalette
noncomputable section
attribute [local irreducible] OffsetSourceGate.machine

def move (up : Bool) := RecoveryFocus.machine gates (HardwireReusable.move up)
def evaluate := RecoveryFocus.machine gates OffsetSourceGate.machine
def wipeSlots (i : Fin 99) : Fin 108 := ⟨8+i.val,by omega⟩
def wipe := RecoveryFocus.machine wipeSlots (RecoveryScratchErase.resetMachine 97)
def machine := Composition.machine fanout (Composition.machine (move true)
  (Composition.machine evaluate (Composition.machine (move false) wipe)))

end
end PCJ45bee56da9f34d5a_CellGate
