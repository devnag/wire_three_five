import Proof.CaseAnalysis.WitnessCoefficientBits

/-! One exact coefficient-bit policy is physically produced from the
actual source q0 and clause-bit count. The numeric clause count and the
numeric coefficient cap are never materialized. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CoefficientBits
open LocalBitMultitape RecoveryRootRound RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def polySlots (i : Fin (DimensionPolynomial.tapes 1)) : Fin 21:=⟨i.val,by
  have hi:=i.isLt;dsimp only [DimensionPolynomial.tapes] at hi;omega⟩
def copySlots : Fin 3→Fin 21:=![polySlots (DimensionPolynomial.widthSlot 1),17,18]
def sumSlots : Fin 4→Fin 21:=![16,17,19,20]
def width (delta : ℚ) (copies q0 clauseBits : ℕ):=
  clauseBits+natBitLength (DimensionPolynomial.value 1 (factor delta copies) q0)
noncomputable def poly (delta : ℚ) (copies : ℕ):=
  RecoveryFocus.machine polySlots (DimensionPolynomial.machine 1 (factor delta copies))
noncomputable def copy:=RecoveryFocus.machine copySlots (UWalkUnary.machine false false)
noncomputable def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def first (delta : ℚ) (copies : ℕ):=Composition.machine (poly delta copies) copy
noncomputable def machine (delta : ℚ) (copies : ℕ):=Composition.machine (first delta copies) sum
def budget (delta : ℚ) (copies q0 clauseBits : ℕ):=
  DimensionPolynomial.budget 1 (factor delta copies) q0+1+
    (2*natBitLength (DimensionPolynomial.value 1 (factor delta copies) q0)+6)+1+
      (2*width delta copies q0 clauseBits+6)

end NearCubicWires.RepairOrdinary.CloseoutWitness.CoefficientBits
