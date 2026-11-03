import Proof.Packets.PacketsXReusableArithmeticNat
import Proof.Packets.PacketsXSubstitutionCensus
import Proof.Packets.PhysicalEraseInto

/-! The final packet's outer normalization is executed literally. Even a
normal input must be normalized again: this reverses its monomial list.
The old left operand is physically cleared before the existing addition
worker folds the right operand into zero. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketOuterNormalize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
open ReusableArithmetic (heads state natState)
attribute [local irreducible] ReusableArithmetic.machine NormalizedAddition.machine PhysicalEraseInto.machine

def clearSlots : Fin 4→Fin 34 := ![25,28,32,33]
noncomputable def clearLeft := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 2)
attribute [local irreducible] clearLeft


attribute [local irreducible] ReusableArithmetic.state

noncomputable def machine := Composition.machine clearLeft (ReusableArithmetic.machine NormalizedAddition.machine)
attribute [local irreducible] machine

end PCJ9eff70d512234a4c_Fixed.Materializer.PacketOuterNormalize
