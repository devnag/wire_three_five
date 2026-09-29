import Proof.MachineModel.BankEmittedAtomLoop

/-!
# The frame-lowering adapter of the bank-framed emitter

`BankEmittedAtomLoop.inverseEmitterRuns_ofCompiler` consumes one stage between
the numeral bank's frame and the atom loop's own input frame:

`InverseFrameAdapterRuns` — started on
`publishedBankFrame outer pcppSource rate target code`, the stage must return

`pair (generatedBalancedRangeInput count context) (that same frame)`,

where `count` and `context` are the schedule's structural atom count and public
request context at `target`.

Two things are bundled there, and this module separates them.

* **Frame retention.**  The bank's frame is both the stage's input and the
  point code the atom loop carries beside its generated range.  §1–§3 discharge
  that half outright: the adapter is the frame duplicator followed by the
  shape stage run under `PreserveRightProgram.preserveRightProgram`, so the
  retained copy is never touched by the arithmetic.  Nothing about the shape
  stage is used except its own run.
* **The atom shape.**  What remains is `InverseAtomShapeRuns` (§3): from the
  bank's frame, produce `generatedBalancedRangeInput count context`.  This is
  the projection-runner table together with the compiled formula length, and it
  is the one residual of the adapter.

§4 records exactly what that residual has to compute, and which half of it the
tree already executes.  Two points are worth stating explicitly because they
constrain any construction.

1. The context is *pure pairing* over the runner table and three numerals
   (`inverseAtomContext_eq`), and the table's balanced encoding is literally the
   left component of `ProjectionRunnerBalancedProgram`'s output
   (`run_inverseProjectionRunnerBalancedProgram`).  The formula length is not
   pairing: it counts the compiled nodes of every decision row, so it reads the
   table's contents and not only the shape numerals.
2. The available table run is stated at the *PCP input's* public length
   `inverseScheduleLength …`, while the adapter runs at the request's public
   length `target`.  Those coincide exactly on the schedule's diagonal.  The
   identification is **not** asserted here: `BankScheduleDiagonal` records that
   the consumer of `bodyRun` does not pin `target` to a scheduled source length,
   so a construction of `InverseAtomShapeRuns` must either carry the diagonal
   hypothesis explicitly or produce the scheduled numerals off the diagonal as
   well.  §4 threads the identification as a hypothesis of the one lemma that
   needs it.
-/

namespace NearCubicWires.BankFrameLoweringAdapter

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The frame duplicator -/

/-! ## 2. The adapter and its resource envelopes -/

/-! ## 3. The frame retention, discharged -/

/-! ## 4. What the atom-shape stage has to compute -/

end NearCubicWires.BankFrameLoweringAdapter
