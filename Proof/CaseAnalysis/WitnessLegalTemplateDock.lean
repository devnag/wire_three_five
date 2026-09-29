import Proof.CaseAnalysis.WitnessLegalTemplate

/-! Four retained actual source-policy fields enter the legal-policy worker
by tape aliasing, with the source domain kept at its documented head one. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.LegalTemplate.Call
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev extra (e : ℕ):=LegalTemplate.tapes e

def old (e : ℕ) {t : ℕ} (i : Fin t) : Fin (t+extra e):=i.castAdd _
def remap (e : ℕ) (i : Fin (extra e)) : Fin (4+extra e):=
  if i.val=0 then (0 : Fin 4).castAdd _
  else if i.val=5+LegalPolicy.M e then (1 : Fin 4).castAdd _
  else if i.val=5+LegalPolicy.M e+16 then (2 : Fin 4).castAdd _
  else if i.val=5+LegalPolicy.M e+138 then (3 : Fin 4).castAdd _ else i.natAdd 4
def bank (e : ℕ) {t : ℕ} (fields : Fin 4→Fin t) : Fin (4+extra e)→Fin (t+extra e):=
  Fin.addCases (motive:=fun _=>Fin (t+extra e)) (fun i=>old e (fields i)) (fun i=>i.natAdd t)
def slots (e : ℕ) {t : ℕ} (fields : Fin 4→Fin t):=bank e fields ∘ remap e
def machine (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool) {t : ℕ} (fields : Fin 4→Fin t):=
  RecoveryFocus.machine (slots e fields) (LegalTemplate.machine e den delta copies sym)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.LegalTemplate.Call
