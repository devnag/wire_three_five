import Proof.CaseAnalysis.WitnessLegalTemplateDock

/-! The retained input-length counter physically produces both capacities.
The existing polynomial, successor-template and copy workers are paid once. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCapacity
open LocalBitMultitape RecoveryRootRound RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev A (E : ℕ):=DimensionPolynomial.tapes E
def tapes (E : ℕ):=A E+8
def powerSlots (E : ℕ) (i : Fin (A E)) : Fin (tapes E):=i.castAdd 8
def pSlot (E : ℕ):=powerSlots E (DimensionPolynomial.rawSlot E)
def templateSlots (E : ℕ) (i : Fin 3) : Fin (tapes E):=
  if i.val=0 then pSlot E else ⟨A E+i.val,by dsimp only [tapes];omega⟩
def copySlots (E : ℕ) (i : Fin 5) : Fin (tapes E):=
  if i.val=0 then ⟨A E+1,by dsimp only [tapes];omega⟩ else ⟨A E+3+i.val,by dsimp only [tapes];omega⟩
def hSlot (E : ℕ):=copySlots E 1
def power (E K : ℕ):=RecoveryFocus.machine (powerSlots E) (DimensionPolynomial.machine E K)
def template (E : ℕ):=RecoveryFocus.machine (templateSlots E) (DimensionTemplate.machine true)
def copy (E : ℕ):=RecoveryFocus.machine (copySlots E) MatrixTemplateCopy.resetMachine
def first (E K : ℕ):=Composition.machine (power E K) (template E)
def machine (E K : ℕ):=Composition.machine (first E K) (copy E)
def value (E K N : ℕ):=DimensionPolynomial.value E K N
def budget (E K N : ℕ):=DimensionPolynomial.budget E K N+1+(2*value E K N+8)+1+(4*(value E K N+1)+12)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCapacity
