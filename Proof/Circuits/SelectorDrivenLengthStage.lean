import Proof.MachineModel.SourceDrivenNumeralBank

/-!
# The length stage that discharges the source-driven bank's residual

`SourceDrivenNumeralBank` reduced both roots' diagonal to one purely executable
obligation: a program that emits `Nat.pair (scheduleLength …) code` from the
request (`FixedScheduledLengthRuns` / `InverseScheduledLengthRuns`).  That
obligation is *satisfiable* — unlike every form of `hdiagonal` — because the
schedule's index is exactly what the envelope's executable selector computes.

This module builds the supplier on the **fixed** schedule, where no
`inverseSourceIndex` scan is needed:
`FixedScheduleAtomLoop.fixedScheduleLength` is `sourceLength` of the selected
source itself, so the length is

```
requestCode ↦ encodeUnary length      (build the selector's unary request)
            ↦ selector output          (ScheduledRecovery.run_selector)
            ↦ source + 1               (extract .source, increment)
            ↦ 2 ^ (source + 1)         (CanonicalTwoPowProgram)
```

with the request code preserved on the right of the frame throughout by
`PreserveRightProgram`.  §1 is the unary builder, §2 the source extractor, §3
the assembled program and its run, §4 the discharged `FixedScheduledLengthRuns`.

The inverse schedule's supplier is the same pipeline with one extra stage — the
`RecoveryScheduleEnvelope.inverseSourceIndex` bounded scan — inserted between the
extractor and the two-power; that stage is named at the end of §4.
-/

namespace NearCubicWires.SelectorDrivenLengthStage

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 0. `encodeUnary` bookkeeping -/

/-! ## 1. The unary request builder

From `initialNPOracleState length code` emit `Nat.pair (encodeUnary length)
code`: the exact request state `ScheduledRecovery.run_selector` reads, with the
request code retained on the right.
-/

/-! ## 2. The source extractor

From `Nat.pair selectorCode code`, where `selectorCode` is a
`ScheduledRecovery.ExecutableScheduleSelection.code`, emit
`Nat.pair (source + 1) code`: the exponent the source length is a power of.
-/

/-! ## 3. The fixed schedule's length program, assembled -/

/-! ## 4. `FixedScheduledLengthRuns`, discharged -/

end NearCubicWires.SelectorDrivenLengthStage
