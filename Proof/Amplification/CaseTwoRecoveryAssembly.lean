import Proof.Amplification.CaseOneRecoveryAssembly

/-!
# Published Case-2 recovery assembly

This module isolates the only semantic bridge required from the concrete
balanced approximation machine.  Once that machine accepts every legal
approximation of the scheduled seed and rejects the selected refuter word, the
published XOR contract produces one common hard core for both circuit families.
-/

namespace NearCubicWires.CaseTwoRecoveryAssembly

open NearCubicWires
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseOneScheduleLedger
open NearCubicWires.CircuitRestriction
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PhysicalHardness
open NearCubicWires.PhysicalRecovery
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

/-! ## One target function at the executable-language seam -/

/-! ## Public pointwise values of the Case-2 branch

The Case-2 half of the canonical target is assembled from `private`
constructors above.  The two theorems below are the only public window on that
branch: at every requested point the canonical target equals the XOR power of
the scheduled Case-2 seed read on the low raw-core coordinates.  They mention
neither `PaddedPhysicalModeHardness` nor any private declaration, so an
executable language linker can state its `hexecutes` obligation outside this
module. -/

end NearCubicWires.CaseTwoRecoveryAssembly
