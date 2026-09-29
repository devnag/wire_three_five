import Proof.Hierarchy.CompetitorMonomialPrepare

/-! Exact docking of the paid monomial-record preparation to the accepted
native multiplication/widening/append run, retaining both ambient cursors
and the next iteration's physical scratch-support bound. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorMonomialProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlot (i : Fin 79) : Fin 88 := i.castAdd 9
noncomputable def nativeProgram := RecoveryFocus.machine nativeSlot CompetitorMonomialTarget.machine


end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
