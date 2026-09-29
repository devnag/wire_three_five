import Proof.MachineModel.TopDownWorkspaceSelectedEntryInit

/-! Original admitted data supplies one fixed prologue plus physically selected
cache-count/append initializer. The count comes from the original PCPP header,
not the prologue's envelope. The repeat driver receives its paid head bump. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntryReady
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration CanonicalWitnessCodec
open WorkspaceGuardedWorker (entry reference)
open WorkspaceSelectedAdmission (originalTapes preFuel coldCutoff capacity)
open WorkspaceSelectedEntry (size output outputHeads)
open RecoveryRootRound
noncomputable section
attribute [local irreducible] WorkspaceSelectedProgram.admission

variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r extra : Nat)

theorem old_size : 2≤originalTapes sources p k := by
  dsimp [originalTapes,WorkspaceBoundedGateEntry.originalTapes,WorkspaceBoundedAdmission.tapes,HeaderDock.tapes]
  omega

def cache (mode : Bool) : Fin 19→Fin (originalTapes sources p k) :=
  CloseoutFinalC10ColdCacheAtAdmission.cacheSlot (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    k p.clauseDegree p.degree (capacity sources p).E mode

def driver (hspace : size sources k r p.clauseDegree+96≤extra) :
    Fin (originalTapes sources p k+1+1+extra) :=
  ⟨originalTapes sources p k+2+(size sources k r p.clauseDegree+51),by omega⟩

end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntryReady
