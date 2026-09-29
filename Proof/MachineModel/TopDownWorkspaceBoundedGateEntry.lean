import Proof.MachineModel.TopDownWorkspaceBoundedAdmission
import Proof.CaseAnalysis.FinalCacheRewind

/-! The existing bounded parser inhabits the guarded worker's exact admission
entry. A distinct final tape holds the outer gate flag and is retained. All
original parser output heads and tapes remain visible in the receipt. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceBoundedGateEntry
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
open RepairSource.CloseoutFinal.C10LengthGate (exitTapes)
open WorkspaceGuardedWorker (input entry reference)
noncomputable section

def originalTapes (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k E : Nat) :=
  WorkspaceBoundedAdmission.tapes (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    k p.clauseDegree p.degree E

def originalProgram (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (coldCutoff E K : Nat) :=
  WorkspaceBoundedAdmission.program (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    k (SelectedSource.hierarchy sources k clock).coefficient (padding sources k clock)
    coldCutoff p.clauseDegree p.degree p.copies E K 1 1
    (CompetitorRationalGap.zeta (constantsOf sources)) (SelectedSource.code sources k clock)

def fuel (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (coldCutoff E K : Nat) : Nat → Nat :=
  WorkspaceBoundedAdmission.uniformFuel (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    (SelectedSource.hierarchy sources k clock) (padding sources k clock) coldCutoff
    p.clauseDegree p.degree p.copies E K 1 1 (CompetitorRationalGap.zeta (constantsOf sources))

end
end NearCubicWires.P1TopDown.WorkspaceBoundedGateEntry
