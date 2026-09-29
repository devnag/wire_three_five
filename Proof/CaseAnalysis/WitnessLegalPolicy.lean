import Proof.CaseAnalysis.WitnessModeWire
import Proof.CaseAnalysis.WitnessDescriptionPolicy
import Proof.CaseAnalysis.WitnessTermPolicy
import Proof.CaseAnalysis.WitnessMass

/-! The complete legal-family policy uses the actual source fields once.
The original wire, description, term and mass workers share their produced
values directly; each policy and the zero accumulator remain available. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.LegalPolicy
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open CompetitorSumFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev M (e : ℕ):=ModeWire.tapes e
def tapes (e : ℕ):=M e+256
def modeSlots (e : ℕ) (i : Fin (M e)) : Fin (tapes e):=i.castAdd 256
def termSlots (e : ℕ) (i : Fin 44) : Fin (tapes e):=⟨M e+i.val,by dsimp only [tapes];omega⟩
def wireSlot (e : ℕ):=modeSlots e (ModeWire.valueSlot e)
def descriptionSlots (e : ℕ) (i : Fin 93) : Fin (tapes e):=
  if i.val=0 then termSlots e 0 else if i.val=34 then wireSlot e
  else if i.val=76 then modeSlots e (ModeWire.dimensionSlots e 1)
  else ⟨M e+44+i.val,by dsimp only [tapes];omega⟩
def massSlots (e : ℕ) (i : Fin 119) : Fin (tapes e):=
  if i.val=0 then termSlots e 42 else ⟨M e+137+i.val,by dsimp only [tapes];omega⟩
def mode (e den : ℕ):=RecoveryFocus.machine (modeSlots e) (ModeWire.machine e den)
def terms (e : ℕ) (delta : ℚ) (copies : ℕ):=RecoveryFocus.machine (termSlots e) (TermPolicy.machine delta copies)
def description (e : ℕ) (sym : Bool):=RecoveryFocus.machine (descriptionSlots e) (DescriptionPolicy.machine sym)
def mass (e : ℕ):=RecoveryFocus.machine (massSlots e) MassCold.machine
def first (e den : ℕ) (delta : ℚ) (copies : ℕ):=Composition.machine (mode e den) (terms e delta copies)
def second (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool):=
  Composition.machine (first e den delta copies) (description e sym)
def machine (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool):=
  Composition.machine (second e den delta copies sym) (mass e)
def W (e den R : ℕ):=R^3/(den*logScale R^e)
def T (delta : ℚ) (copies q0 cb : ℕ):=(2*2^cb)*xorTermBound delta q0 copies
def budget (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool) (R q0 cb b : ℕ):=
  ModeWire.budget e den R+1+TermPolicy.budget delta copies q0 cb+1+
    DescriptionPolicy.budget sym R q0 (W e den R)+1+MassCold.budget (T delta copies q0 cb) b


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.LegalPolicy
