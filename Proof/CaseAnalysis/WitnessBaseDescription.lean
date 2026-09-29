import Proof.CaseAnalysis.WitnessGateDescription

/-! The original normalized-circuit description cap is produced exactly
for each fixed mode. Both short arguments come from the actual source
policy; no weight-size exponential is constructed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BaseDescription
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open ProjectionNormalization VerifierDecoding RecoveryWitnessPolicy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def sourceSlots (i : Fin 34) : Fin 76:=i.castAdd 42
def wireSlots (i : Fin 34) : Fin 76:=⟨if i.val=0 then 34 else 35+i.val,by split_ifs <;> omega⟩
def templateSlots : Fin 3→Fin 76:=![32,69,70]
def productSlots (sym : Bool) : Fin 4→Fin 76:=![if sym then 42 else 34,69,71,72]
def sumSlots (sym : Bool) : Fin 4→Fin 76:=![71,if sym then 73 else 67,74,75]
def source:=RecoveryFocus.machine sourceSlots GateDescription.machine
def wire:=RecoveryFocus.machine wireSlots GateDescription.machine
def template (sym : Bool):=RecoveryFocus.machine templateSlots (DimensionTemplate.machine sym)
def product (sym : Bool):=RecoveryFocus.machine (productSlots sym) ClockUnaryProduct.machine
def sum (sym : Bool):=RecoveryFocus.machine (sumSlots sym) ClockUnarySum.machine
def first:=Composition.machine source wire
def second (sym : Bool):=Composition.machine first (template sym)
def third (sym : Bool):=Composition.machine (second sym) (product sym)
def machine (sym : Bool):=Composition.machine (third sym) (sum sym)
def factor (sym : Bool) (W : ℕ):=if sym then W+1 else W
def offset (sym : Bool) (W : ℕ):=if sym then 0 else normalizedGateDescriptionCap W
def value (sym : Bool) (n W : ℕ):=
  factor sym W*(normalizedGateDescriptionCap n+sym.toNat)+offset sym W
def budget (sym : Bool) (n W : ℕ):=GateDescription.budget n+1+GateDescription.budget W+1+
  (2*normalizedGateDescriptionCap n+8)+1+
  WilliamsUnaryProduct.budget (factor sym W) (normalizedGateDescriptionCap n+sym.toNat)+1+
  (2*value sym n W+6)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BaseDescription
