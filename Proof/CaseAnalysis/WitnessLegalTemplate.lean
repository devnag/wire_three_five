import Proof.CaseAnalysis.RowsCircuitBottomReturned
import Proof.CaseAnalysis.WitnessCorePolicy
import Proof.CaseAnalysis.WitnessLegalPolicy

/-! The retained actual cache template supplies the original legal-policy
worker through the existing paid unary copy. No source field is serialized. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.LegalTemplate
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open CompetitorSumFold
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev L (e : ℕ):=LegalPolicy.tapes e
def tapes (e : ℕ):=5+L e
def templateSlots (e : ℕ) (i : Fin 5) : Fin (tapes e):=i.castAdd (L e)
def slots (e : ℕ) (i : Fin (L e)) : Fin (tapes e):=
  if i.val=0 then templateSlots e 1 else i.natAdd 5
def template (e : ℕ):=RecoveryFocus.machine (templateSlots e) PCPPNativeTemplateRaw.machine
def policy (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool):=
  RecoveryFocus.machine (slots e) (LegalPolicy.machine e den delta copies sym)
def machine (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool):=
  Composition.machine (template e) (policy e den delta copies sym)
def budget (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool) (R q0 cb b : ℕ):=
  4*R+16+1+LegalPolicy.budget e den delta copies sym R q0 cb b


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.LegalTemplate
