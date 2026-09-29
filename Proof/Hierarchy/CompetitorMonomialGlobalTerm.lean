import Proof.Hierarchy.CompetitorMonomialTargetDenominator

/-! Whole actual coefficient/count-to-term producer. It computes the three
exact integer products, widens all fields to the global width, and appends the literal
negative/positive/denominator record consumed by the cold rational fold. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalDecision CompetitorMonomialProducts CompetitorRawFieldEmit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sources : List (Fin 79) := [71,68,76]
noncomputable def emitProgram := listProgram (74 : Fin 79) 70 sources
noncomputable def machine := Composition.machine targetProgram emitProgram


end NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
