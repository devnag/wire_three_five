import Proof.SourceAssembly.SourceSkelInitAll
import Proof.SourceAssembly.SourceFirstFront3

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

def initResVal (Rc q L CP DP CW DW CL DL : Nat) (mode : Bool) (tg : Nat) (val : Nat → Option (List Bool)) (i : Nat) :
    List Bool :=
  if i = 0 then ZeroPadding.pad Rc (UnaryTemplate.tape q)
  else if i = 1 then ZeroPadding.pad Rc (List.replicate (CP*(q+1)^DP) true)
  else if i = 2 then ZeroPadding.pad Rc (List.replicate (CW*(q+1)^DW) true)
  else if i = 3 then ZeroPadding.pad Rc (List.replicate (CL*(q+1)^DL) true)
  else if i = 4 then ZeroPadding.pad Rc (SourceFactorSel.Nat.tagWord mode)
  else if i = 5 then ZeroPadding.pad Rc (frame (natWord q))
  else if i = 6 then ZeroPadding.pad Rc (frame (natWord L))
  else if i = 7 then ZeroPadding.pad Rc (frame (natWord tg))
  else slotVal Rc val i

end
end NearCubicWires.SourceSkeleton.InitS
end
