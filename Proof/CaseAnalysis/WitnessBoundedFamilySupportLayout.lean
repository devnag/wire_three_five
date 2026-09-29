import Proof.CaseAnalysis.WitnessBoundedFamilyLayout
import Proof.CaseAnalysis.WitnessFamilySupportLayout

/-! The original bounded header selects one strengthened cold family.
Its two modes share one added support tape and preserve every old address. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamilySupport
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def slots (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool):=
  SupportDock.slots (BoundedFamily.slots source a k D G E sym)
def first (a : PointwisePCPPAlgorithm) (k D G E : ℕ):=TapeEmbedding.machine 1 (BoundedFamily.first source a k D G E)
def branch {s : ℕ} (supplier : Machine 3244 s) (a : PointwisePCPPAlgorithm)
    (k CH Cpad cutoff D G copies E K symDen thrDen : ℕ) (delta : ℚ) (code : List Bool) (sym : Bool):=
  RecoveryFocus.machine (slots source a k D G E sym)
    (ColdFamilySupport.machine source supplier a k CH Cpad cutoff D G copies (BoundedFamily.exponent sym) E K
      (BoundedFamily.denominator sym symDen thrDen) delta code sym)
def good (a : PointwisePCPPAlgorithm) (k D G E : ℕ)
    (cells : Fin (HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1)→Bool):=
  cells ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 147).castAdd 1)
def mode (a : PointwisePCPPAlgorithm) (k D G E : ℕ)
    (cells : Fin (HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1)→Bool):=
  cells ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 142).castAdd 1)
def machine (suppliers : Bool→Σ s,Machine 3244 s) (a : PointwisePCPPAlgorithm)
    (k CH Cpad cutoff D G copies E K symDen thrDen : ℕ) (delta : ℚ) (code : List Bool):=
  HeaderSwitch.machine (first source a k D G E)
    (branch source (suppliers true).2 a k CH Cpad cutoff D G copies E K symDen thrDen delta code true)
    (branch source (suppliers false).2 a k CH Cpad cutoff D G copies E K symDen thrDen delta code false)
    (good source a k D G E) (mode source a k D G E)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamilySupport
