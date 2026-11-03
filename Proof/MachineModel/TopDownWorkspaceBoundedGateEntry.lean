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

theorem entry_embed {t : Nat} (ht : 2≤t) (x bits : List Bool) :
    Fin.addCases (input x bits : Fin t → List Bool) (fun _ : Fin 1 => [true]) =
      entry (Fin.last t) x bits := by
  funext i
  refine Fin.addCases (m:=t) (n:=1) ?_ ?_ i
  · intro j
    have hne : j.castAdd 1 ≠ Fin.last t := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd,Fin.val_last] at this
      omega
    simp only [Fin.addCases_left,entry,exitTapes,hne,if_false,input,Fin.val_castAdd]
    rfl
  · intro j
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    have hv : (0 : Fin 1).natAdd t=Fin.last t := Fin.ext (by simp)
    rw [Fin.addCases_right,hv]
    simp [entry,exitTapes,input,Fin.val_last,Nat.ne_of_gt (show 0<t by omega),
      Nat.ne_of_gt (show 1<t by omega),writeTapeBit]

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

def flag (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k E : Nat) :
    Fin (originalTapes sources p k E+1) :=
  (BoundedFamilySupport.flag (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    k p.clauseDegree p.degree E).castAdd 1

def fuel (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (coldCutoff E K : Nat) : Nat → Nat :=
  WorkspaceBoundedAdmission.uniformFuel (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    (SelectedSource.hierarchy sources k clock) (padding sources k clock) coldCutoff
    p.clauseDegree p.degree p.copies E K 1 1 (CompetitorRationalGap.zeta (constantsOf sources))

end
end NearCubicWires.P1TopDown.WorkspaceBoundedGateEntry
