import Proof.Foundations.ScheduledRecovery

/-!
# Case-one schedule ledger

The STV branch receives the pairing-clock oracle bound selected by the common
outer split.  This file records the two quantitative consequences needed by
closed recovery assembly: a chosen polynomial power survives the STV integer
root, and the corresponding STV advantage is at most the matching inverse
power.  Both facts are derived from the exact pairing-clock lower bound.
-/

namespace NearCubicWires.CaseOneScheduleLedger

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

end NearCubicWires.CaseOneScheduleLedger
