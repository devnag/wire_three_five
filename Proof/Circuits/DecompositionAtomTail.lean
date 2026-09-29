import Proof.Circuits.DecompositionAtomReset

/-! The signed-atom caller physically appends the framed integer result and
then erases its bank. Its original source cursor and global unary
capacity survive; the append cursor alone advances. -/
namespace NearCubicWires.RepairOrdinary.DecompositionAtomReuse
open LocalBitMultitape RecoveryRootRound
open PCPSerializerReuse (copyMachine copyEntry copy_run)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true



end NearCubicWires.RepairOrdinary.DecompositionAtomReuse
