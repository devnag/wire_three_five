import Proof.MachineModel.ControllerCappedSelected
import Proof.MachineModel.TopDownSelectedRuntime
import Proof.MachineModel.ControllerSelectedContinuation

/-! Preserve the C.10 choice order and complete runtime obligation at the
capped physical parser. Reuse the existing additive ledger and same three-phase
continuation syntax. This supplies no estimate for the still-unbuilt supplier. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.ControllerCappedRuntime
open RepairOrdinary RepairSource SourceInterfaces
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
open ControllerCappedSelected
noncomputable section

theorem degree_before_hierarchy (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) (den : Nat) :
    ∃ degree,∀ (k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))),
      ∃ coefficient,∀ n,preFuel sources p den k clock n≤coefficient*(n+1)^degree := by
  obtain ⟨degree,hdegree⟩:=AdmissionBudget.degree_before_hierarchy
    (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    (WorkspaceSelectedAdmission.coldCutoff sources) p.clauseDegree p.degree p.copies
    (WorkspaceSelectedAdmission.capacity sources p).E (WorkspaceSelectedAdmission.capacity sources p).K
    den den (CompetitorRationalGap.zeta (constantsOf sources)) p.hD
  exact ⟨degree,fun k clock=>hdegree (CloseoutWitness.SelectedSource.hierarchy sources k clock) (padding sources k clock)⟩

def prepDegree (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den : Nat) : Nat :=
  Classical.choose (degree_before_hierarchy sources p den)

/-- Choose both admission and remaining source-length degrees before k. The
previously accepted complete continuation program is reused without alteration. -/
def hierarchyIndex (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den remainingDegree : Nat) :=
  max (prepDegree sources p den) (WorkspaceSelectedEntryRuntime.degree sources p remainingDegree)

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

def continuation (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den remainingDegree r base scratch : Nat)
    (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
      LocalBitMultitape.Machine (ControllerSelectedContinuation.bodyTapes sources p
        (hierarchyIndex sources p den remainingDegree) r scratch) states)
    (remainingFuel : Nat→Nat) : SelectedAssembly.ContinuationData sources p := by
  let k:=hierarchyIndex sources p den remainingDegree
  let X:=ControllerSelectedContinuation.extra sources p k r scratch
  let built:=ControllerSelectedContinuation.program sources p k r scratch site
  exact {
    k := k
    clock := PolynomialClock.ordinaryClock k
    base := base
    extra := X
    states := _
    machine := built.2
    result:=⟨WorkspaceSelectedAdmission.originalTapes sources p k+2+217,by
      have hP : 302≤WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
        unfold WorkspaceSelectedEntry.size; omega
      dsimp [X,ControllerSelectedContinuation.extra]; omega⟩
    fuel:=WorkspaceSelectedEntryRuntime.fuel sources p k r remainingFuel }

end
end NearCubicWires.P1TopDown.ControllerCappedRuntime
