import Proof.CaseAnalysis.WitnessFamilyCount
import Proof.CaseAnalysis.ScheduleClauseWidth

/-! The actual native arity supplies every short common mode dimension:
binary R for exact sum arity, logScale R and the numerator R^3. All copies,
templates, arithmetic and head resets are existing paid ordinary workers. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ModeDimensions
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open ProjectionNormalization CloseoutSchedule VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def binarySlots (i : Fin 10) : Fin 47:=i.castAdd 37
def logSlots (i : Fin (Clause.tapes 1)) : Fin 47:=
  ⟨if i.val=0 then 2 else 10+i.val,by dsimp [Clause.tapes] at *;split_ifs <;> omega⟩
def powerSlots (i : Fin (DimensionPower.tapes 3)) : Fin 47:=
  ⟨if i.val=0 then 3 else 38+i.val,by dsimp [DimensionPower.tapes] at *;split_ifs <;> omega⟩
def binaryProgram:=RecoveryFocus.machine binarySlots MatrixDimensionBinary.resetMachine
def logarithm:=RecoveryFocus.machine logSlots (Clause.machine 1)
def power:=RecoveryFocus.machine powerSlots (DimensionPower.machine 3 1)
def first:=Composition.machine binaryProgram logarithm
def machine:=Composition.machine first power
def budget (R : ℕ):=(16*R^2+72*R+32)+1+Clause.budget 1 R+1+DimensionPower.cost 1 R 3


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ModeDimensions
