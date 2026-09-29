import Proof.Supplier.EquationCutLayout

/-! The agreed common twenty-one-tape bank for both passes of one cut. -/
namespace NearCubicWires.RepairOrdinary.EquationCut.Ambient
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def slots : Fin 5→Fin 21 := ![0,14,17,18,19]
def restoreSlots : Fin 6→Fin 21 := ![0,14,17,18,19,20]
def weightProgram := RecoveryFocus.machine slots weightMachine
def restoreProgram := RecoveryFocus.machine restoreSlots restored
def scalarProgram (negate : Bool) := TapeEmbedding.machine 4 (EquationScalarStream.machine negate)
def secondTail := Composition.machine (scalarProgram false) (scalarProgram true)
def second := Composition.machine weightProgram secondTail
def machine := Composition.machine restoreProgram second


end
end NearCubicWires.RepairOrdinary.EquationCut.Ambient
