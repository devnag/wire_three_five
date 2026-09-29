import Proof.CaseAnalysis.WitnessNativePolicyInput

/-! Alias the ten measured fields into the complete cache and policy worker.
The unrelated stream/counter heads stay outside this local cold workspace. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativePolicy.Call
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev extra (a : PointwisePCPPAlgorithm) (D : ℕ):=NativePolicy.tapes a D
def remap (a : PointwisePCPPAlgorithm) (D : ℕ) (i : Fin (extra a D)) : Fin (75+extra a D):=
  if i.val=0 then (45 : Fin 75).castAdd _ else if i.val=1 then (32 : Fin 75).castAdd _
  else if i.val=2 then (48 : Fin 75).castAdd _ else if i.val=18 then (71 : Fin 75).castAdd _
  else if i.val=19 then (53 : Fin 75).castAdd _ else if i.val=20 then (58 : Fin 75).castAdd _
  else if i.val=95 then (0 : Fin 75).castAdd _ else if i.val=96 then (52 : Fin 75).castAdd _
  else if i.val=291 then (57 : Fin 75).castAdd _ else if i.val=363 then (72 : Fin 75).castAdd _
  else i.natAdd 75
def old (a : PointwisePCPPAlgorithm) (D : ℕ) {t : ℕ} (i : Fin t) : Fin (t+extra a D):=i.castAdd _
def bank (a : PointwisePCPPAlgorithm) (D : ℕ) {t : ℕ} (counter : Fin 75→Fin t) :
    Fin (75+extra a D)→Fin (t+extra a D):=
  Fin.addCases (motive:=fun _=>Fin (t+extra a D)) (fun i=>old a D (counter i)) (fun i=>i.natAdd t)
def slots (a : PointwisePCPPAlgorithm) (D : ℕ) {t : ℕ} (counter : Fin 75→Fin t):=
  bank a D counter ∘ remap a D
def machine (a : PointwisePCPPAlgorithm) (D copies : ℕ) (delta : ℚ) {t : ℕ}
    (counter : Fin 75→Fin t):=RecoveryFocus.machine (slots a D counter) (NativePolicy.machine a D copies delta)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativePolicy.Call
