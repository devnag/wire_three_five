import Proof.CaseAnalysis.WitnessLegalTemplateDock

/-! The six legal metadata ports and existing mass bank form the exact
retained input needed by the family call. Their indices stay symbolic. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyPolicyPorts
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def header (e : ℕ) : Fin 6→Fin (LegalTemplate.tapes e):=
  ![LegalTemplate.templateSlots e 0,
    LegalTemplate.slots e (LegalPolicy.modeSlots e (ModeWire.dimensionSlots e 5)),
    LegalTemplate.slots e (LegalPolicy.wireSlot e),
    LegalTemplate.slots e (LegalPolicy.descriptionSlots e 91),
    LegalTemplate.slots e (LegalPolicy.termSlots e 42),
    LegalTemplate.slots e (LegalPolicy.massSlots e 1)]
def mass (e : ℕ) (i : Fin 94):=LegalTemplate.slots e (LegalPolicy.massSlots e (MassCold.nativeSlots i))
def port (e : ℕ) : Fin 100→Fin (LegalTemplate.tapes e):=
  Fin.addCases (m:=6) (n:=94) (motive:=fun _=>Fin (LegalTemplate.tapes e)) (header e) (mass e)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyPolicyPorts
