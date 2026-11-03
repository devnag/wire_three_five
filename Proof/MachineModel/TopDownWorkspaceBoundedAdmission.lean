import Proof.MachineModel.TopDownWorkspaceGuardedWorker
import Proof.CaseAnalysis.WitnessBoundedFamilyBudget

/-! A sealed state-count package for the existing bounded parser, exposing its
actual total receipt without normalizing the source compiler's state arithmetic
through every later composition. No new parser or semantic advice is added. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceBoundedAdmission
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal
open WorkspaceGuardedWorker (input entry)
noncomputable section
attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine

def tapes (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (k D G E : Nat) : Nat :=
  HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1

@[irreducible] def program (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies E K symDen thrDen : Nat)
    (delta : Rat) (code : List Bool) : Sigma (fun s => Machine (tapes source a k D G E) s) :=
  ⟨_,BoundedFamilySupport.actualMachine source a k CH Cpad cutoff D G copies E K symDen thrDen
    (CloseoutMassThreshold.literalWidth delta copies) delta
    (CloseoutSampledWitness.massCap delta copies) code⟩

theorem input_eq (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (k D G E : Nat) (x bits : List Bool) :
    BoundedFamilySupport.input source a k D G E x bits = input x bits := by
  funext j
  change SupportDock.lift (HeaderDock.input (BoundedFamily.workspace source a k D G E)
    (CompetitorWitnessBounded.input x bits)) [] j = _
  refine Fin.addCases (m:=HeaderDock.tapes (BoundedFamily.workspace source a k D G E)) (n:=1) ?_ ?_ j
  · intro j
    rw [SupportDock.lift,Fin.addCases_left]
    refine Fin.addCases (m:=150) (n:=BoundedFamily.workspace source a k D G E+1) ?_ ?_ j
    · intro j
      simp only [HeaderDock.input,Fin.addCases_left,input,Fin.val_castAdd]
      exact CompetitorWitnessBounded.input_eq x bits j
    · intro j
      simp only [HeaderDock.input,Fin.addCases_right,input,Fin.val_castAdd,Fin.val_natAdd]
      rw [if_neg (by omega),if_neg (by omega)]
  · intro j
    simp only [SupportDock.lift,Fin.addCases_right,input,Fin.val_natAdd]
    rw [if_neg (by dsimp [HeaderDock.tapes];omega),if_neg (by dsimp [HeaderDock.tapes];omega)]

def uniformFuel (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) {k : Nat} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad cutoff D G copies E K symDen thrDen : Nat) (delta : Rat) (n : Nat) : Nat :=
  2*(ColdNative.bound source a D G copies cutoff delta (HierarchyBudget.scale source H Cpad n)+
    BoundedFamily.outerBound source a G D copies E K symDen thrDen delta n)

end
end NearCubicWires.P1TopDown.WorkspaceBoundedAdmission
