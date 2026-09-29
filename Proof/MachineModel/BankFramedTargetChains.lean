import Proof.MachineModel.BankFrameLoweringAdapter
import Proof.PCP.PaddedProjectionPresentation

/-!
# The two target chains at the numeral bank's frame

`PaddedProjectionPresentation.inverse_bodyRun_ofPresentation` consumes its two
chain premises `hchainOne`/`hchainTwo` at the numeral bank's own frame

`publishedBankFrame outer pcppSource rate target (encodeBitInput input)`,

whereas every closed chain run in the tree
(`BranchTargetLanguageProgram.run_inverseCaseOneChainProgram`,
`CaseTwoBlockOccurrenceProgram.run_caseTwoTargetBitFromPointRangeProgram_inverse_closed`)
is stated at the bare requested point code `encodeBitInput input`.  This module
removes that gap once and for all.

## The frame half is unconditional

`RuntimeScheduleNumeralBank.scheduleNumeralBankOutput` puts the retained point
code in the innermost right position of a four-register pairing, and
`publishedBankFrame` is that word at the length-decoded registers.  Recovering
the point code is therefore four right projections — no schedule numeral is
read, no source index is decoded, and **no diagonal identification is needed**:
the projection is correct at every public length, on or off the schedule's
diagonal.  §2 executes it and §3 wraps an arbitrary chain behind it.

This is the one reusable call frame of the bank-framed body: any stage already
verified from the requested point code is re-framed to the bank's frame by
`run_bankFramedChainProgram_published`, at one extra link and five instructions,
with no hypothesis about the stage beyond its own run.

## What is left after it

§4 names the two residual premises in their point-code form
(`InverseCaseOnePointRuns`, `InverseCaseTwoPointRuns`) and §5 discharges
`hchainOne` and `hchainTwo` from them.  Both residuals are *frame free*: they
say nothing about the bank, the registers, or the diagonal.  What they still
demand — and what this module deliberately does not hide — is that the chain be
**one fixed instruction stream for every target**, whereas
`inverseCaseOneChainProgram` and the Case-2 occurrence callee are still indexed
by the request's own target through their scheduled immediates.  That residue is
a property of those chains, not of the frame, and it is now the only thing
between the closed chain runs and `bodyRun`.
-/

namespace NearCubicWires.BankFramedTargetChains

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. Bookkeeping -/

/-! ## 2. The bank frame's point-code projection -/

/-! ## 3. The re-framing wrapper -/

/-! ## 4. The two chain premises, frame free -/

/-! ## 5. The dispatcher's chain premises, discharged -/

end NearCubicWires.BankFramedTargetChains
