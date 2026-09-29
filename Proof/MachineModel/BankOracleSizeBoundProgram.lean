import Proof.MachineModel.BankRecoveryCodeProgram

/-!
# The small-oracle size cap, read from the numeral bank

The branch query of `CanonicalBranchSelectorProgram` is the canonical
bounded-oracle recovery code of the scheduled refuter word *at the scheduled
size cap*

`RecoveryScheduleEnvelope.oracleSizeBound requiredDegree
  (scheduledWidth outer sourceIndex)`,

and `oracleSizeBound requiredDegree` is by definition the pairing clock
`pairClock (oracleDepth requiredDegree)`.  The numeral bank already leaves the
scheduled width in a register and `RuntimeScheduleNumeralBank.pairIterProgram`
is that clock as a fixed instruction stream, so the cap is a register
computation rather than an immediate.

This module performs it.  §2 lifts the bank's width register in front of the
retained frame, §3 runs the clock on it, §4 installs the resulting cap beside
the retained point code inside the frame, and §5 links the published
refuter-word frame of `BankRefuterWordFrameProgram` on top, producing

`pair (encodeBitInput word) (pair sourceLength (pair sizeBound pointCode))`,

the exact context the structural atom emitter of
`BankRecoveryCodeProgram` consumes.  Only the machine description remains an
immediate, and the machine-dependence analysis of
`ExecutableTargetLanguagePackaging` already licenses that one as frozen.
-/

namespace NearCubicWires.BankOracleSizeBoundProgram

open NearCubicWires
open NearCubicWires.BankRefuterWordFrameProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping -/

/-! ## 2. Lifting the bank's width register -/

/-! ## 3. Installing the computed cap beside the point code -/

/-! ## 4. The bank's frame with the scheduled size cap -/

/-! ## 5. The emitter's context: refuter word, scheduled length, size cap -/

end NearCubicWires.BankOracleSizeBoundProgram
