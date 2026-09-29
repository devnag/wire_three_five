import Proof.MachineModel.SourceDrivenNumeralBank

/-!
# The inverse schedule's `inverseSourceIndex`, executed

`SelectorDrivenLengthStage` discharged the *fixed* schedule's length residual,
where the length is `sourceLength` of the selected source itself.  The *inverse*
schedule applies one more map — `RecoveryScheduleEnvelope.inverseSourceIndex` —
between the selected source and the source length:

```
inverseScheduleLength … target =
  sourceLength (inverseSourceIndex (inverseSelectedSource … target)).
```

`inverseSourceIndex k = Nat.findGreatest (fun j => inverseSourceMeasure j ≤ k+2)
(k+1)` with `inverseSourceMeasure j = (j+1) · logScale (j+1) = (j+1) · clog₂(j+3)`.
This module supplies the executable scan.

## The design

The predicate is a monotone threshold, so the answer is the largest `j` with
`measure j ≤ k+2`; §0 proves the two-inequality characterization that turns a
program output into `inverseSourceIndex k`, and the clog-crossing arithmetic the
loop's register discipline needs.  §1 is the loop: four data registers
`j`, `c = clog₂(j+3)`, `q = 2^c`, `prod = (j+1)·c = measure j`, advanced by
*additions only* — no inner multiply and no inner clog loop — with the crossing
test the equality `q = j+3` and `prod` updated by `prod += c` (no cross) or
`prod += c + (j+2)` (cross).  §2 assembles the inverse length program and §3
discharges `SourceDrivenNumeralBank.InverseScheduledLengthRuns`.
-/

namespace NearCubicWires.InverseSourceIndexScan

open NearCubicWires
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope

/-! ## 0. The scan is correct once it reports the threshold -/

/-! ### clog-crossing arithmetic -/

/-! ## 1. The functional scan and its correctness

The scan is written first as a pure state transition, proved equal to
`Nat.findGreatest` — hence to `inverseSourceIndex` by definition.  §2's program
then only has to reproduce this transition register for register.
-/

end NearCubicWires.InverseSourceIndexScan
