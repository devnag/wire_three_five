import Proof.Packets.PacketsXLiteralCache

/-! Paid between-cache preparation. Every private tape is physically cleared,
then actual resident tag/count templates are copied into the metadata and
counted-loop driver. The cache output has reserved zero backing on reentry. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheReload
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.ProjectionNormalization Completion
noncomputable section


def scratchSlots (i : Fin 63) : Fin 68 :=
  if h : i.val<59 then ⟨i.val,by omega⟩ else (![61,63,66,67] : Fin 4→Fin 68) ⟨i.val-59,by omega⟩
def clearSlots : Fin 65→Fin 68 := Fin.addCases (m:=63) (n:=2) scratchSlots (![59,60])
def moveSlots : Fin 2→Fin 68 := ![1,61]
def tagSlots : Fin 3→Fin 68 := ![64,0,63]
def indexSlots : Fin 3→Fin 68 := ![65,1,66]
def driverSlots : Fin 3→Fin 68 := ![65,61,67]
def phase1 := RecoveryFocus.machine moveSlots (PhysicalDriverMoves.machine 2 .left)
def phase2 := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 63)
def phase3 := RecoveryFocus.machine tagSlots (UWalkUnary.machine true false)
def phase4 := RecoveryFocus.machine indexSlots (UWalkUnary.machine true false)
def phase5 := RecoveryFocus.machine driverSlots (UWalkUnary.machine true false)
def phase6 := RecoveryFocus.machine moveSlots (PhysicalDriverMoves.machine 2 .right)
def machine := Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine phase1 phase2) phase3) phase4) phase5) phase6

end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheReload
