import Proof.CaseAnalysis.WitnessNativePipeline

/-! Five retained outputs of the original cold oracle prefix are the only
live inputs to the complete guarded native pipeline. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativePipeline.Dock
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev extra (a : PointwisePCPPAlgorithm) (D G : ℕ):=NativePipeline.base G+NativePolicy.Call.extra a D

def old (a : PointwisePCPPAlgorithm) (D G : ℕ) {t : ℕ} (i : Fin t) : Fin (t+extra a D G):=i.castAdd _
def remap (a : PointwisePCPPAlgorithm) (D G : ℕ) (i : Fin (extra a D G)) : Fin (5+extra a D G):=
  if i.val=0 then (0 : Fin 5).castAdd _ else if i.val=13 then (1 : Fin 5).castAdd _
  else if i.val=14 then (2 : Fin 5).castAdd _ else if i.val=48 then (3 : Fin 5).castAdd _
  else if i.val=49 then (4 : Fin 5).castAdd _ else i.natAdd 5
def bank (a : PointwisePCPPAlgorithm) (D G : ℕ) {t : ℕ} (fields : Fin 5→Fin t) :
    Fin (5+extra a D G)→Fin (t+extra a D G):=
  Fin.addCases (motive:=fun _=>Fin (t+extra a D G)) (fun i=>old a D G (fields i)) (fun i=>i.natAdd t)
def slots (a : PointwisePCPPAlgorithm) (D G : ℕ) {t : ℕ} (fields : Fin 5→Fin t):=
  bank a D G fields ∘ remap a D G
def machine (a : PointwisePCPPAlgorithm) (D G copies : ℕ) (delta : ℚ) {t : ℕ} (fields : Fin 5→Fin t):=
  RecoveryFocus.machine (slots a D G fields) (NativePipeline.machine a D G copies delta)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativePipeline.Dock
