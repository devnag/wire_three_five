import Proof.CaseAnalysis.WitnessGateDescription

/-! The exact restricted description is evaluated in factored form from
the already produced source fields. Every template and multiplication is
paid; the bit-length shift never materializes the exponential parameter. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RestrictedDescription
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open ProjectionNormalization VerifierDecoding RecoveryWitnessPolicy ComponentwiseCircuitRestriction
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def copySlots : Fin 3→Fin 16:=![3,4,5]
def sumSlots : Fin 4→Fin 16:=![2,4,6,7]
def coreSlots : Fin 3→Fin 16:=![0,8,9]
def firstSlots : Fin 4→Fin 16:=![6,8,10,11]
def factorSlots (sym : Bool) : Fin 3→Fin 16:=![if sym then 1 else 2,12,13]
def lastSlots : Fin 4→Fin 16:=![10,12,14,15]
def copy:=RecoveryFocus.machine copySlots (UWalkUnary.machine false true)
def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
def core:=RecoveryFocus.machine coreSlots (DimensionTemplate.machine true)
def firstProduct:=RecoveryFocus.machine firstSlots ClockUnaryProduct.machine
def factorProgram (sym : Bool):=RecoveryFocus.machine (factorSlots sym) (DimensionTemplate.machine (!sym))
def lastProduct:=RecoveryFocus.machine lastSlots ClockUnaryProduct.machine
def first:=Composition.machine copy sum
def second:=Composition.machine first core
def third:=Composition.machine second firstProduct
def fourth (sym : Bool):=Composition.machine third (factorProgram sym)
def machine (sym : Bool):=Composition.machine (fourth sym) lastProduct
def factor (sym : Bool) (W L : ℕ):=if sym then W+1 else L+1
def factorInput (sym : Bool) (W L : ℕ):=if sym then W+1 else L
def height (L b : ℕ):=L+(b+1)
def budget (sym : Bool) (core W L b : ℕ):=(2*b+6)+1+(2*height L b+6)+1+(2*core+8)+1+
  WilliamsUnaryProduct.budget (height L b) (core+1)+1+(2*factorInput sym W L+8)+1+
    WilliamsUnaryProduct.budget (height L b*(core+1)) (factor sym W L)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.RestrictedDescription
