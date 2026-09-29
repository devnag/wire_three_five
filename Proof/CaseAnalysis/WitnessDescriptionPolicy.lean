import Proof.CaseAnalysis.WitnessBaseDescription
import Proof.CaseAnalysis.WitnessRestrictedDescription

/-! Complete exact mode description policy from actual core, q0 and W.
All intermediate caps, bit lengths, factors and templates are produced by
the same execution; no exponential normalization parameter is expanded. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DescriptionPolicy
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open RecoveryWitnessPolicy ComponentwiseCircuitRestriction
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def baseSlots (i : Fin 76) : Fin 93:=i.castAdd 17
def restrictionSlots (i : Fin 16) : Fin 93:=
  ⟨if i.val=0 then 76 else if i.val=1 then 42 else if i.val=2 then 74
    else if i.val=3 then 14 else 77+i.val,by split_ifs <;> omega⟩
def first (sym : Bool):=RecoveryFocus.machine baseSlots (BaseDescription.machine sym)
def second (sym : Bool):=RecoveryFocus.machine restrictionSlots (RestrictedDescription.machine sym)
def machine (sym : Bool):=Composition.machine (first sym) (second sym)
def value (sym : Bool) (R n W : ℕ):=
  if sym then restrictedSymmetricDescriptionCap R n (2^symmetricDescriptionCap n W) W
  else restrictedThresholdDescriptionCap R n (2^thresholdDescriptionCap n W) (thresholdDescriptionCap n W)
def budget (sym : Bool) (R n W : ℕ):=BaseDescription.budget sym n W+1+
  RestrictedDescription.budget sym R W (BaseDescription.value sym n W) (natBitLength (n+1))


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.DescriptionPolicy
