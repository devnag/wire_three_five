import Proof.MachineModel.CappedLegalAdmission
import Proof.MachineModel.TopDownSelectedAssembly

/-! Paper A.8 chooses a positive wire coefficient after the saving parameter
(paper.tex:2310-2324). Keep that choice in the actual parser as well as the
headline consumer. Reuse the existing tape layout, retained cache, cold parser,
rewind, ordinary rejection runs, and caller's SAME continuation. No supplier
execution or whole-machine cost is inferred from these construction choices. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.ControllerCappedSelected
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.SelectedRecoveryIntegration
open P1Independent.CappedConsumer
open WorkspaceGuardedWorker (input entry below_run rejected_run)
open WorkspaceSelectedAdmission (capacity originalTapes coldCutoff Cached input_blank zero_heads)
noncomputable section
attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine
  CloseoutFinalC10ColdCacheRewind.machine

/-- The reference is used only to select a legal-witness onset, never executed. -/
def reference (den : Nat) (hden : 0<den) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) : WorkerData where
  den := den
  hden := hden
  k := k
  clock := clock
  tapes := 2
  states := 2
  worker := C10LengthGate.counter 0 0 1
  result := 1
  fuel := fun _=>0
  onset := 0
  passed := fun _ _ _=>false

@[irreducible] def originalProgram (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) :
    Σ states, Machine (originalTapes sources p k) states :=
  ⟨_,(WorkspaceBoundedAdmission.program (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    k (SelectedSource.hierarchy sources k clock).coefficient (padding sources k clock)
    (coldCutoff sources) p.clauseDegree p.degree p.copies (capacity sources p).E
    (capacity sources p).K den den (CompetitorRationalGap.zeta (constantsOf sources))
    (SelectedSource.code sources k clock)).2⟩

def admission (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) (extra : Nat) :=
  TapeEmbedding.machine extra (TapeEmbedding.machine 1
    (CloseoutFinalC10ColdCacheRewind.machine (originalProgram sources p den k clock).2))

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes admission

end
end NearCubicWires.P1TopDown.ControllerCappedSelected
