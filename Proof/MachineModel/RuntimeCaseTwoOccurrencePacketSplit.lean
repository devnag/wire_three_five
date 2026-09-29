import Proof.MachineModel.RuntimeCaseTwoOccurrenceClosure
import Proof.MachineModel.RuntimeScheduleQuadNumeralProgram

/-!
# The occurrence packet, split into its schedule and oracle halves

`RuntimeCaseTwoOccurrenceClosure` reduced the Case-2 occurrence residual to
`InverseScheduledOccurrencePacket`: one fixed program emitting the seven
numerals of the per-block callee from the target's public length.  The premise
was all-or-nothing, yet its two halves are of completely different character.

`RuntimeCaseTwoBlockOccurrenceProgram.occurrencePacket` is *literally*
`Nat.pair (quad) (triple)`:

* the **schedule quad** — `seedArity`, the outer native width, the width
  envelope and the clause-address envelope — is arithmetic in the scheduled
  source length alone.  `RuntimeScheduleQuadNumeralProgram` builds it, and §2
  instantiates that stream at the published contracts, leaving *no* premise:
  the only hypothesis is the schedule diagonal the cluster already carries.
* the **oracle triple** — the published factory's clause width at the
  substituted circuit, that circuit's size, and its encoding — is recovered
  from the accepting oracle rather than computed from the request.

§1 records the split.  §2 discharges the quad.  §3 states the oracle triple as
the residual premise.  §4 pairs the two streams and re-proves
`InverseScheduledOccurrencePacket` from the triple alone, and §5 restates the
cluster closure at the smaller premise.

## What the oracle triple still needs

The encoder is
`recovered description bits ↦ encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)`,
and §6 reduces it to three named pieces by proving the two codec identities the
tree lacked.  `caseTwoSubstitutedCircuit caseTwo` is
`(outer.substitution.circuit ⟨n, input, restrictPaddedOracle caseTwo.circuit _⟩).padToArity`,
so:

* `encodeBooleanCircuit_padSize` turns the outer `padToArity` into one
  `encodeBalancedList` **append** of a constant list — and
  `CanonicalBalancedFlattenProgram.balancedAppendProgram` is that append;
* `encodeBooleanCircuit_restrictBooleanCircuit` turns the inner
  `restrictPaddedOracle` into one **map** of a per-node transform over the
  encoded node list — and `CanonicalBalancedCall.balancedCallProgram` is that
  map;
* the substitution runner's own `ExecutableProjectionSubstitution.computes`
  then supplies the encoding of the substituted circuit itself.

What is left open is exactly: the per-node callee for `restrictBooleanNode`,
the constant-node generator for the padding suffix, and the assembler that
turns the recovered bounded-circuit description into `encodeBooleanCircuit` of
the oracle it describes.
-/

namespace NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit

open NearCubicWires
open NearCubicWires.BankCaseTwoEnvelopeClosure
open NearCubicWires.CanonicalBinary
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.BankResidualClusterClosure
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.BankScheduledRowStageClosure
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOnePadding
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoBlockOccurrenceProgram
open NearCubicWires.RuntimeCaseTwoOccurrenceClosure
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.RuntimeScheduleQuadNumeralProgram
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The packet is one pair of its two halves -/

/-! ## 2. The schedule quad at the published contracts -/

/-! ## 3. The oracle triple -/

/-! ## 4. Pairing the two halves -/

/-! ## 5. What the cluster closure still needs -/

/-! ## 6. The two codec identities the oracle triple needs

`caseTwoSubstitutedCircuit caseTwo` is the substitution runner's own circuit
wrapped in two syntactic transforms — an inner restriction of the recovered
oracle to the native face, and an outer arity padding.  Neither had an
encoding-level lemma anywhere in the tree, so the encoder could not even be
decomposed.  The two lemmas below supply them, and each lands on a canonical
balanced-list operation that already has a fixed program. -/

end NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
