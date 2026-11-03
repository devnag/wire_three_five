import Proof.SourceAssembly.SourceSkelInitRest

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator RepairRepresentation
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.InitS
noncomputable section

/-- The resident map of the whole init. -/
def valAll (mode : Bool) (L q Rc DD CD Dcw Ccw CL DL : Nat) : Nat → Option (List Bool) := fun i =>
  if i = 15 then some (ZeroPadding.pad Rc (frame (List.replicate (normalizedLiveCount q L) true)))
  else if i = 14 then some (ZeroPadding.pad Rc (frame (List.replicate q true)))
  else if i = 9 then some (ZeroPadding.pad Rc (List.replicate (Ccw*(q+1)^Dcw) true))
  else if i = 8 then some (ZeroPadding.pad Rc (List.replicate (cwidOf mode (CL*(q+1)^DL)) true))
  else valR Rc DD CD q i

/-- The extension scratch the whole init uses. -/
def uAll (DD Dcw : Nat) : Nat := 18 + 14 + 2*DD + 81 + 14 + 2*Dcw + 4 + 8

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

def initAllCost (L C cVc cS cR DP CP DW CW DL CL : Nat) (mode : Bool) (target q b DD CD Dcw Ccw : Nat) : Nat :=
  initRCost pl L C cVc cS cR DP CP DW CW DL CL mode target q b DD CD + 1 + cwCost mode (CL*(q+1)^DL) + 1 +
    PCPSerializerCapacity.Power.budget Dcw Ccw q + 1 + ((2*q+6) + 1 + (2*(q+q)+6)) + 1 +
    ((2 * (List.replicate 2 true).length + 2) + 1 + SourceRequest.CurComp.subCost (InitPost.Ms L q))

end
end NearCubicWires.SourceSkeleton.InitS
end
