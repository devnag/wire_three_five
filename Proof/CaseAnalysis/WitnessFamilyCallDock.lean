import Proof.CaseAnalysis.WitnessFamilySparsePorts

/-! The paid policy and mass store enter the whole family by direct tape
aliasing. All private tapes are fresh; no metadata serialization is run. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCold.Call
open LocalBitMultitape FamilySparse
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev extra:=3243
def remap (i : Fin 3243) : Fin (104+3243):=
  if h:∃ j,port j=i then (Classical.choose h).castAdd 3243 else i.natAdd 104



def old {t : ℕ} (i : Fin t) : Fin (t+extra):=i.castAdd extra
def bank {t : ℕ} (fields : Fin 104→Fin t) : Fin (104+3243)→Fin (t+extra):=
  Fin.addCases (m:=104) (n:=3243) (motive:=fun _=>Fin (t+extra))
    (fun i=>old (fields i)) (fun i=>i.natAdd t)
def slots {t : ℕ} (fields : Fin 104→Fin t):=bank fields ∘ remap


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCold.Call
