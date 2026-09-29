import Proof.CaseAnalysis.WitnessDescriptionHorner

/-! The exact gate description polynomial and the source bit length are
produced from actual n alone. The two fixed Horner steps avoid constructing
any exponential normalization bound. All scratch starts blank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.GateDescription
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open ProjectionNormalization VerifierDecoding RecoveryWitnessPolicy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def baseSlots (i : Fin 16) : Fin 34:=i.castAdd 18
def templateSlots : Fin 3→Fin 34:=![0,16,17]
def firstSlots : Fin 8→Fin 34:=![7,16,20,21,22,23,24,25]
def lastSlots : Fin 8→Fin 34:=![24,16,28,29,30,31,32,33]
def base:=RecoveryFocus.machine baseSlots (DimensionPolynomial.machine 1 1)
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def first:=RecoveryFocus.machine firstSlots (DescriptionHorner.machine 2)
def last:=RecoveryFocus.machine lastSlots (DescriptionHorner.machine 1)
def initial:=Composition.machine base template
def middle:=Composition.machine initial first
def machine:=Composition.machine middle last
def budget (n : ℕ):=DimensionPolynomial.budget 1 1 n+1+(2*n+8)+1+
  DescriptionHorner.budget 2 (n+1) n+1+DescriptionHorner.budget 1 ((n+1)*n+2) n

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.GateDescription
