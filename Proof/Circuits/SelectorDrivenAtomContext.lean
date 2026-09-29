import Proof.Circuits.FixedScheduleDiagonalClosure
import Proof.MachineModel.SourceDrivenNumeralBank

/-!
# The atom-shape context from the selector-driven registers

`BankAtomContextRegisters.inverseAtomContext_ofRegisters` is the *only* place in
the inverse cluster that consumes the schedule diagonal, and
`BankAtomContextRegisters`'s own header says so: "§5 is the only place in the
reduction that needs a hypothesis, and it needs two — the presentation premise
and the diagonal".

`SourceDrivenNumeralBank` removes the reason for the second one.  Its bank is
driven by a supplied scheduled length, so the registers a consumer reads are
already indexed by the *chain's* source index rather than by
`RecoveryScheduleEnvelope.sourceIndexOfLength` of the request.  This module
restates §5 at those registers.

The restatement is the same proof with two steps deleted.  The old proof opened
with

```
hindex   : sourceIndexOfLength target = inverseSourceIndex (inverseSelectedSource … target)
hlength  : bankSourceLength target = inverseScheduleLength … target
```

both derived from `hdiagonal`.  At the selector-driven registers those two facts
are `rfl` — the width register *is* `scheduledWidth outer (inverseSourceIndex …)`
and the length register *is* `inverseScheduleLength …` — so the hypothesis has
no work left to do and is dropped from the signature.  The size-cap step, which
previously needed `hindex` before its `rfl`, is now `rfl` outright.

**Output contract unchanged.**  `inverseAtomContext_ofSelectorRegisters` proves
the identical equation against the identical right-hand side
(`BankEmittedAtomLoop.inverseAtomContext`); only the register names on the left
and the premise list change.
-/

namespace NearCubicWires.SelectorDrivenAtomContext

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces

/-! ## 1. The selector-driven registers -/

/-! ## 2. §5 of `BankAtomContextRegisters`, without the diagonal -/

/-! ## 3. The fixed schedule's twin

The fixed chain's index is the selected source itself, with no
`inverseSourceIndex` in front of it, so the same two registers are one
application shorter.  `FixedScheduleDiagonalClosure.fixedAtomContext_ofRegisters`
loses its diagonal in exactly the same way.
-/

end NearCubicWires.SelectorDrivenAtomContext
