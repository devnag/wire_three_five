import Proof.CaseAnalysis.WitnessModeDivide

/-! The original actual native arity alone produces the exact natural
wire cap. The binary arity and the reusable domain template are retained
for the enclosing sum and circuit guards. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ModeWire
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open ProjectionNormalization VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (e : ℕ):=47+ModeDivide.tapes e
def dimensionSlots (e : ℕ) (i : Fin 47) : Fin (tapes e):=i.castAdd (ModeDivide.tapes e)
def divideSlots (e : ℕ) (i : Fin (ModeDivide.tapes e)) : Fin (tapes e):=
  ⟨if i.val=0 then 45 else if i.val=1 then 36 else 47+i.val,by
    dsimp only [tapes];split_ifs <;> have hi:=i.isLt <;> dsimp [ModeDivide.tapes] at * <;> omega⟩
def valueSlot (e : ℕ):=divideSlots e (ModeDivide.valueSlot e)
def first (e : ℕ):=RecoveryFocus.machine (dimensionSlots e) ModeDimensions.machine
def second (e den : ℕ):=RecoveryFocus.machine (divideSlots e) (ModeDivide.machine e den)
def machine (e den : ℕ):=Composition.machine (first e) (second e den)
def budget (e den R : ℕ):=ModeDimensions.budget R+1+ModeDivide.budget e den (R^3) (logScale R)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ModeWire
