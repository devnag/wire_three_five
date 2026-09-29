import Proof.Amplification.CaseTwoRecoveryAssembly
import Proof.Circuits.PhysicalHeadlineAdapters
import Proof.Amplification.RecoveryWitnessNormalization
import Proof.Amplification.RecoveryWitnessShape

/-!
# Scheduled capacity of canonical recovery witnesses

This module freezes the exact Case-2 decoder limits for both published
schedules and proves that their complete canonical encodings eventually fit
the executable `n / 16` witness shape.  The capacity proof is derived from the
fixed-delta XOR syntax envelopes and source schedule; callers supply no bound
on an encoded witness.
-/

namespace NearCubicWires.RecoveryWitnessScheduleCapacity

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PhysicalHardness
open NearCubicWires.PhysicalHeadlineAdapters
open NearCubicWires.PolynomialSchedule
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RecoveryWitnessNormalization
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RecoveryWitnessShape
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.HeadlineClosure

/-! ## Direct `RecoveredPerClassFacts` schedule fields -/

end NearCubicWires.RecoveryWitnessScheduleCapacity
