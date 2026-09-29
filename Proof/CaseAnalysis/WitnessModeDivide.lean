import Proof.CaseAnalysis.WitnessModeDimensions

/-! The exact mode quotient uses the paid short numerator and logarithm.
Both original fields survive; divisor construction and division are ordinary
workers with all copying, polynomial evaluation and rewinds charged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ModeDivide
open LocalBitMultitape RecoveryRootRound RepairSource ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (e : ℕ):=13+2*e
def copySlots (e : ℕ) : Fin 3→Fin (tapes e):=![⟨1,by dsimp [tapes];omega⟩,
  ⟨2,by dsimp [tapes];omega⟩,⟨3,by dsimp [tapes];omega⟩]
def templateSlots (e : ℕ) : Fin 3→Fin (tapes e):=![⟨2,by dsimp [tapes];omega⟩,
  ⟨4,by dsimp [tapes];omega⟩,⟨5,by dsimp [tapes];omega⟩]
def powerSlots (e : ℕ) (i : Fin (DimensionPower.tapes e)) : Fin (tapes e):=
  ⟨if i.val=0 then 4 else 6+i.val,by
    have hi:=i.isLt;dsimp only [DimensionPower.tapes,tapes] at *;split_ifs <;> omega⟩
def denominatorSlot (e : ℕ) : Fin (tapes e):=⟨7+2*e,by dsimp [tapes];omega⟩
def divisorSlot (e : ℕ) : Fin (tapes e):=⟨9+2*e,by dsimp [tapes];omega⟩
def valueSlot (e : ℕ) : Fin (tapes e):=⟨11+2*e,by dsimp [tapes];omega⟩
def divisorSlots (e : ℕ) : Fin 3→Fin (tapes e):=![denominatorSlot e,divisorSlot e,
  ⟨10+2*e,by dsimp [tapes];omega⟩]
def divideSlots (e : ℕ) : Fin 4→Fin (tapes e):=![⟨0,by dsimp [tapes];omega⟩,
  divisorSlot e,valueSlot e,⟨12+2*e,by dsimp [tapes];omega⟩]
def copy (e : ℕ):=RecoveryFocus.machine (copySlots e) (UWalkUnary.machine false false)
def template (e : ℕ):=RecoveryFocus.machine (templateSlots e) (DimensionTemplate.machine false)
def power (e den : ℕ):=RecoveryFocus.machine (powerSlots e) (DimensionPower.machine e den)
def divisor (e : ℕ):=RecoveryFocus.machine (divisorSlots e) (DimensionTemplate.machine false)
def divide (e : ℕ):=RecoveryFocus.machine (divideSlots e) MatrixBucketDivide.machine
def first (e : ℕ):=Composition.machine (copy e) (template e)
def second (e den : ℕ):=Composition.machine (first e) (power e den)
def third (e den : ℕ):=Composition.machine (second e den) (divisor e)
def machine (e den : ℕ):=Composition.machine (third e den) (divide e)
def budget (e den n L : ℕ):=(2*L+6)+1+(2*L+8)+1+DimensionPower.cost den L e+1+
  (2*(den*L^e)+8)+1+(8*n+6)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ModeDivide
