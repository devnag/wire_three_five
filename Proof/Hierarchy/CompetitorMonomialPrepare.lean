import Proof.Hierarchy.CompetitorMonomialWidthFields

/-! The native monomial caller is prepared from a canonical coefficient,
count and normalization-denominator record. Both global cursors survive the
physical scratch clear and runtime-width preparation. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorMonomialProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store (b t : ℕ) (source output : List Bool) (ambient : Fin 88 → List Bool) : Prop where
  source : ambient 79=source
  output : ambient 74=output
  inputWidth : ambient 81=List.replicate (width b) true
  targetWidth : ambient 82=List.replicate (width t) true
  shortWidth : ambient 83=List.replicate t true
  eraseDriver : ambient 84=List.replicate (capacity t) true
  eraseReset : ambient 85=List.replicate (capacity t+1) false
  support : ∀ j,(ambient (workSlot j)).length≤capacity t

def allWidths : List (Fin 3) := [0,1,2]
def allFields : List (Fin 6) := [0,1,2,3,4,5]
noncomputable def widthPrepareProgram := Composition.machine (clearProgram workSlot) (widthsProgram allWidths)
noncomputable def prepareProgram := Composition.machine widthPrepareProgram (fieldsProgram allFields)



end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
