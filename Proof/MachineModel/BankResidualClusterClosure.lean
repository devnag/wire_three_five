import Proof.MachineModel.BankProjectionTableStage
import Proof.MachineModel.BankRegisterCaseTwoChain

/-!
# The bank/diagonal cluster's three residuals, discharged together

`BankDiagonalBodyClosure.inverse_bodyRun_ofDiagonalCluster` consumes exactly
three cluster-specific premises beside the six width budgets and the compiler's
run:

* `BankAtomContextRegisters.InverseAtomTableRuns`,
* `BankFramedTargetChains.InverseCaseOnePointRuns`,
* `BankFramedTargetChains.InverseCaseTwoPointRuns`.

`BankProjectionTableStage`, `BankRegisterCaseOneChain` and
`BankRegisterCaseTwoChain` each discharge one of them.  The consumer shares a
*single* pair of envelopes between the two chains, so the three cannot simply be
quoted side by side: this module supplies the two monotonicity lemmas that let
one shared envelope cover both branches, and states the triple at that shared
envelope.

After it, the cluster's remaining obligations are

* `InverseScheduledRowRuns` — one decision-row stage, target uniform;
* `InverseScheduledOccurrenceRuns` — the Case-2 per-block occurrence callee;
* `InverseCaseTwoBankEnvelopes` — a resource domination statement;

together with the two hypotheses the cluster already threads, the executable
presentation and the onset-restricted schedule diagonal.
-/

namespace NearCubicWires.BankResidualClusterClosure

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. Both chain premises are monotone in their envelopes -/

/-! ## 2. The shared chain envelope -/

/-! ## 3. The three residuals, at the shared envelope -/

end NearCubicWires.BankResidualClusterClosure
