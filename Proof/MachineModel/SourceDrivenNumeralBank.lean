import Proof.Circuits.FixedScheduleAtomLoop

/-!
# The numeral bank driven by a supplied scheduled length

`ScheduleDiagonalObstruction` and `ScheduleImageDiagonalObstruction` between
them refute every restatement of `hdiagonal`: the numeral bank decodes its
source index from the request's public length
(`RecoveryScheduleEnvelope.sourceIndexOfLength`), the two chains take theirs
from the envelope's first-crossing selector, and no restriction of the request
makes the two agree above an onset.  The repair therefore has to change the
*bank*, not the binder.

This module performs the structural half of that repair, and it turns out to be
a re-composition rather than a new arithmetic.

## The observation that makes it cheap

Read `RuntimeScheduleNumeralBank` §5–§6 as a pipeline:

```
bankLengthProgram  ⊕  dupLeft ⊕ width ⊕ dup ⊕ copies ⊕ callFrame ⊕ shape ⊕ queryCount
```

Only the *first* stage looks at the request.  Every later stage is arithmetic in
the length that stage produced: `bankWidth` is `widthValue … (bankSourceLength …)`,
`bankCopyCount` is `copyCountValue … (bankWidth …)`, and the shape runner is
called at `bankSourceLength …` in both its length and its code register.  The
public length register is never read again.

So the bank is `lengthStage ⊕ f`, with `f` closed in the emitted length.  §1
below re-composes exactly that `f` against a **parameter** length stage, whose
only obligation is

```
run lengthProgram … (initialNPOracleState inputLength code) =
  some (Nat.pair sourceLen code).
```

Nothing else in the bank changes: every stage lemma of
`RuntimeScheduleNumeralBank` is already stated at an arbitrary `sourceLen`.

## Why this deletes the diagonal

`RuntimeScheduleNumeralBank` §8 already proves the three identities the chains
want — `bankWidth_at_sourceLength`, `bankCopyCount_at_sourceLength`,
`bankSourceLength_sourceLength` — **unconditionally in the source index**.  They
were unusable only because the bank re-derived that index from the request, so a
consumer had to assume the request's length was the scheduled one.  Feed the
scheduled length *in* and §2's published run emits

```
scheduleNumeralBankOutput (sourceLength scheduleIndex)
  (scheduledWidth outer scheduleIndex)
  (outer.pcp.queryCount (sourceLength scheduleIndex))
  (inverseCopies outer pcppSource rate scheduleIndex) code
```

for an arbitrary `scheduleIndex`, with no hypothesis relating `scheduleIndex` to
`inputLength`.  That is verbatim the right-hand side of
`BankScheduleDiagonal.publishedBankFrame_of_eq_sourceLength`, so §3 instantiates
`scheduleIndex` at each chain's *own* index and the frame identification becomes
`rfl` — `hdiagonal` is gone, not restated.

## What is left

Exactly one obligation, and it is purely executable with no schedule semantics
in it: `InverseScheduledLengthRuns` / `FixedScheduledLengthRuns` of §4 — a
program that emits `Nat.pair (inverseScheduleLength …) code` from the request.
Its intended supplier is the selector-driven decode
(`UnaryPolynomialSelector.executableEnvelopeSchedule.selector`, an
`ExponentialNatProgram`, then `RecoveryScheduleEnvelope.inverseSourceIndex`'s
bounded `Nat.findGreatest` scan, then `CanonicalTwoPowProgram`), which is a
program-construction task rather than a hypothesis.  On the fixed schedule the
scan is not even needed: `fixedScheduleLength` is `sourceLength` of the selected
source itself.
-/

namespace NearCubicWires.SourceDrivenNumeralBank

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The bank, re-composed against a supplied length stage -/

/-! ## 2. The published bank at a supplied scheduled index -/

/-! ## 3. The frame the chains work at, definitionally -/

/-! ## 4. The one remaining obligation, at both published schedules -/

end NearCubicWires.SourceDrivenNumeralBank
