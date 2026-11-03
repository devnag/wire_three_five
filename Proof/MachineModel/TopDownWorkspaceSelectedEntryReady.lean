import Proof.MachineModel.TopDownWorkspaceSelectedEntryInit
import Proof.CaseAnalysis.RowsOriginalSwitch

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
open WorkspaceSelectedProgram (finalBank lengthFlag)
open WorkspaceSelectedEntry (size output outputHeads)
open RecoveryRootRound
open private NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry.cache_injective from Proof.CaseAnalysis.FinalAdmittedEntry
open private NearCubicWires.P1TopDown.WorkspaceSelectedOriginals.tapes_unique from Proof.MachineModel.TopDownWorkspaceSelectedOriginals
noncomputable section
attribute [local irreducible] WorkspaceSelectedProgram.admission

variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r extra : Nat)

theorem old_size : 2≤originalTapes sources p k := by
  dsimp [originalTapes,WorkspaceBoundedGateEntry.originalTapes,WorkspaceBoundedAdmission.tapes,HeaderDock.tapes]
  omega

def cache (mode : Bool) : Fin 19→Fin (originalTapes sources p k) :=
  CloseoutFinalC10ColdCacheAtAdmission.cacheSlot (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    k p.clauseDegree p.degree (capacity sources p).E mode

def proPort (hspace : size sources k r p.clauseDegree+96≤extra) :=
  WorkspaceSelectedEntry.slots (old_size sources p k) (show size sources k r p.clauseDegree≤extra by omega)

def initPort (hspace : size sources k r p.clauseDegree+96≤extra) (mode : Bool) :=
  WorkspaceSelectedEntryInit.ports (size sources k r p.clauseDegree)
    (by dsimp [size];omega) hspace (cache sources p k mode)

def modePort : Fin (originalTapes sources p k+1+1+extra) :=
  (((WorkspaceSelectedOriginals.headerPort sources p k 142).castAdd 1).castAdd 1).castAdd extra

def heads (hspace : size sources k r p.clauseDegree+96≤extra) :=
  dockH (proPort sources p k r extra hspace) (fun _=>0) (outputHeads sources k r p.clauseDegree)

def post (hspace : size sources k r p.clauseDegree+96≤extra)
    (A : Fin (originalTapes sources p k)→List Bool) (L n : Nat) (x bits : List Bool) (w : Nat→List Bool) :=
  install (proPort sources p k r extra hspace) (finalBank A L extra)
    (output sources k r p.clauseDegree n x bits w)

def initializer (hspace : size sources k r p.clauseDegree+96≤extra) :=
  CloseoutRowsOriginalSwitch.machine
    (RecoveryFocus.machine (initPort sources p k r extra hspace true) WorkspaceSelectedEntryCount.machine)
    (RecoveryFocus.machine (initPort sources p k r extra hspace false) WorkspaceSelectedEntryCount.machine)
    (modePort sources p k extra)

def driver (hspace : size sources k r p.clauseDegree+96≤extra) :
    Fin (originalTapes sources p k+1+1+extra) :=
  ⟨originalTapes sources p k+2+(size sources k r p.clauseDegree+51),by omega⟩

def bump (hspace : size sources k r p.clauseDegree+96≤extra) :=
  DecompositionCountPosition.move (fun i=>if i=driver sources p k r extra hspace then .right else .stay)

def finalHeads (hspace : size sources k r p.clauseDegree+96≤extra)
    (i : Fin (originalTapes sources p k+1+1+extra)) :=
  if i=driver sources p k r extra hspace then heads sources p k r extra hspace i+1
    else heads sources p k r extra hspace i

@[irreducible] def program (hspace : size sources k r p.clauseDegree+96≤extra) :
    Σ s,Machine (originalTapes sources p k+1+1+extra) s :=
  ⟨_,Composition.machine
    (RecoveryFocus.machine (proPort sources p k r extra hspace) (WorkspaceSelectedEntry.program sources k r p.clauseDegree).2)
    (Composition.machine (initializer sources p k r extra hspace) (bump sources p k r extra hspace))⟩

theorem driver_at_init (hspace : size sources k r p.clauseDegree+96≤extra) (mode : Bool) :
    initPort sources p k r extra hspace mode (WorkspaceSelectedEntryCount.count 70)=
      driver sources p k r extra hspace := by
  apply Fin.ext
  simp [initPort,WorkspaceSelectedEntryInit.ports,WorkspaceSelectedEntryCount.count,driver]

theorem bump_run (hspace : size sources k r p.clauseDegree+96≤extra)
    (A : Fin (originalTapes sources p k+1+1+extra)→List Bool) :
    Step (bump sources p k r extra hspace) 1 (heads sources p k r extra hspace) A
      (finalHeads sources p k r extra hspace) A := by
  obtain ⟨rr,hr,hf,_hs⟩:=DecompositionCountPosition.move_run
    (fun i=>if i=driver sources p k r extra hspace then .right else .stay)
    (heads sources p k r extra hspace) A
  apply Step.of_run hr
  · rw [hf]
    funext i
    simp only [finalHeads]
    split_ifs <;>rfl
  · exact congrArg Configuration.tapes hf

end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntryReady
