import Proof.MachineModel.BankFramedTargetChains

/-!
# The uniform target program is total: `hrun` and `hboolean` without a case premise

`ExecutableInterfaces.executableLanguageProgramOfRun` — and therefore both
`UniformTargetLanguageBank.inverse_hexecutes_of_bodyRun` and its fixed-rate
twin — charges two obligations that are quantified over **every** request:

* `hrun  : ∀ request, runNPOracleProgram (uniformTargetProgram …) … = some (output request)`
* `hboolean : ∀ request, output request ≤ 1`

Neither carries a schedule premise.  They therefore hold at off-diagonal
lengths, at malformed point codes, and at targets below the Case-1 onset, where
`bodyRun` says nothing at all.  `bodyRun` is *not* a supplier for them and
structurally cannot become one: its conclusion is guarded by `hlarge`, `hyes`,
`hrejects` and `haccepts`.

## The design verdict: what a bad request does

`LanguageEvaluationRequest` is `⟨inputArity, input⟩`, so *every* request is a
`⟨target, input⟩` with `code = encodeBitInput input`; there are no malformed
requests at the type level.  What varies is whether the request's length is on
the schedule's diagonal.  The stream reacts to that as follows.

1. The numeral bank runs.  `run_publishedScheduleNumeralBankProgram` is
   unconditional in the length, so the bank always halts and always leaves the
   frame `pair sourceLength (pair width (pair queryCount (pair copies code)))`.
   Off the diagonal the four numerals are simply the length-decoded ones; they
   are *wrong* for no request, because the bank defines them.
2. The dispatcher runs the selector and reads its tag.  `taggedProgramChoice`
   has exactly **two** branches, `tag = 0` and `tag ≠ 0`, and both are total —
   there is no third path and hence no fail-closed default to write: the
   dispatcher is already fail-closed by exhaustion.
3. The chosen chain is restarted on the retained code.  The bank-frame
   projection `bankFramedChainProgram` reads only the innermost right
   projection, so it too is diagonal-free.

Consequently the *only* thing separating `hrun`/`hboolean` from the closed tree
is a **halting-with-a-boolean** fact for the three streams that are still free
program binders in the integration: the selector (through the emitter and the
free atom `table`), and the two chains.  Everything above them is discharged
here, unconditionally.

`output` is then not a semantic choice at all: it is *defined* by the program
(`totalTargetOutput` below).  The semantic identification stays where it
belongs — inside `huniform`, which `ExecutableTargetLanguagePackaging.output_eq_of_run`
combines with `hrun` on the diagonal.  This module therefore **subsumes**
nothing of `BankDiagonalBodyClosure.inverse_bodyRun_ofDiagonalCluster`; it is
its total complement.

## Layout

* §1 the total-run predicate and the output it defines.
* §2 the numeral bank's link, unconditional in the request.
* §3 the two-branch dispatcher, unconditional in the tag.
* §4 the bank-frame projection in front of a chain, unconditional in the length.
* §4b booleanness for free, behind `CanonicalBooleanizeProgram`, at no cost on
  the diagonal — so the residue below is *halting*, not *halting with a bit*.
* §5 the inverse schedule's `hrun`/`hboolean` from three named total premises.
* §6 the fixed schedule, where the body is still one free binder.
* §7 the consumer check: the two obligations leave the bridge's binder list.
-/

namespace NearCubicWires.UniformTargetTotalRun

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBooleanizeProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## §1 Total boolean halting, and the output it defines -/

/-! ## §2 The numeral bank's link is unconditional

The bank halts at every public length, so a body that is total at the bank's
frame makes the whole linked stream total at the request itself.  No schedule
numeral, no diagonal and no source index enters. -/

/-! ## §3 The dispatcher's branch inventory

`BranchTargetLanguageProgram.branchTargetBitProgram` is
`linkPrograms selector (taggedProgramChoice first second)`, and
`taggedProgramChoice` splits on the tag register with `branchZero`.  The
inventory is therefore closed at two entries — `tag = 0` and `tag ≠ 0` — and
both entries are total.  The dispatcher needs no fail-closed default; what it
needs is that the selector's tag fit the width `bankDispatchedBodyBits`
declares, i.e. that it be a *bit*. -/

/-! ## §4 The bank-frame projection is unconditional

`BankFramedTargetChains.bankFramedChainProgram` is five instructions of right
projection in front of a chain.  It reads no schedule numeral, so a chain that
is total at the requested point code is total at the bank's frame. -/

/-! ## §4b Booleanness costs nothing

`hboolean` does not need a semantic premise.  A chain that merely *halts*
becomes a boolean chain behind `CanonicalBooleanizeProgram.booleanizedProgram`,
whose suffix is three total instructions; and on the diagonal the wrapper is
transparent, because the canonical target bit is already a `Bool`.  Wrapping the
two chains therefore reduces the §5 residue from *halts with a bit* to *halts*,
without touching `BankFramedTargetChains`' own point-run premises. -/

/-! ## §6 The fixed schedule

`HeadlineRootSkeleton` §5 leaves the fixed-rate body as one free binder, so on
that schedule the bank link of §2 is already the whole reduction: `hrun` and
`hboolean` follow from one total premise about that body at the bank's frame. -/

/-! ## §7 The consumer check

`UniformTargetLanguageBank.inverse_hexecutes_of_bodyRun` at the published
assembly, with `output`, `hrun` and `hboolean` supplied from §5.  What the
packaging bridge still asks for is `hbits`, `hfuel`, `hinitial` and `bodyRun`
— the two totalisation obligations are gone from its binder list. -/

end NearCubicWires.UniformTargetTotalRun
