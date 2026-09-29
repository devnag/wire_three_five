import Proof.MachineModel.CanonicalBooleanCircuitValidationProgram
import Proof.MachineModel.CanonicalLegalTermValidationProgram
import Proof.MachineModel.CanonicalNatBitCapProgram
import Proof.MachineModel.CanonicalNormalizedCircuitDescriptionProgram
import Proof.MachineModel.CanonicalRationalMassProgram
import Proof.MachineModel.CanonicalRecoveryProgram

/-!
# Canonical executable recovery-witness validator construction

The weak verifier receives an untrusted canonical witness code.  Its limits are
trusted configuration derived from the public input arity by the surrounding
schedule controller.  The internal linked stages carry that derived value
through registers so the parser has one uniform ABI; it is not an additional
field of the public weak witness.

No decoded object, validity bit, validation formula, or expected output is
present in the request.  In particular, the limits encoding below contains only
the fields of `RecoveryWitnessLimits`; all nested canonicality and resource
checks are performed by the register program.
-/

namespace NearCubicWires.CanonicalRecoveryValidatorProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalLegalTermValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalNatBitCapProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalNormalizedCircuitDescriptionProgram
open NearCubicWires.CanonicalNormalizedCircuitResourceProgram
open NearCubicWires.CanonicalNormalizedCircuitValidationProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalRationalMassProgram
open NearCubicWires.CanonicalRationalValidationProgram
open NearCubicWires.CanonicalRecoveryProgram
open NearCubicWires.CanonicalSupportedGateRelationProgram
open NearCubicWires.CanonicalSupplierCompressedGateProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## Validated-summary bridge to the wire and description programs

The staged validator's per-term circuit call emits the unique public
normalized-circuit validator output.  The compiled wire and description
programs consume that same value through their shared projection ABI, so their
hypotheses have to be discharged once, here, from validator acceptance alone.

Every statement below is conditional on the owning gate having accepted: a
rejected term never reaches a projection, so no sentinel is unpaired.  Nothing
in this section re-decodes circuit syntax or introduces a second validator
path; the typed refinements consume the existing canonical codecs. -/

/-! ### Exact wire and description semantics of one validated term

These are the two resource coordinates the staged validator still had to reach.
For an accepted term the compiled wire program returns the selected circuit's
exact physical wire count and the compiled description program returns its exact
encoding length, both computed from the retained summary ABI alone. -/

/-! ### Executable wire and description results for one validated term -/

/-! ### Hostile boundary classes for the two new resource coordinates

Each entry is a kernel-checked minimal counterexample: one validated term whose
exact resource value is exactly one unit past the schedule-selected cap
collapses the whole mapped stage summary to zero. -/

/-! ## Internal trusted-configuration syntax -/

/-!
The parser uses a compact failure convention: every validation subroutine
returns zero on failure and a nonzero structural payload on success.  The
top-level output is nevertheless the unique existing
`recoveryWitnessValidatorOutput`; these internal payloads never become a second
semantic result.
-/

/-! ## Fixed outer handoff -/

/-! ## Canonical nested handoff

The envelope proof deliberately returns the original bytes.  The following
fixed stage projects the two nested component codes only after that proof has
accepted the exact three-cell outer syntax.  This avoids maintaining a second
outer decoder while giving later validators a compact, stable register ABI.
-/

/-! ## End-to-end outer/nested projection -/

/-! ## Mandatory nested-presence check -/

/-! ## Canonical structural prefix -/

/-! ## Canonical nested-oracle validation -/

/-! ## Structural prefix with mandatory oracle validation -/

/-! ## Fail-closed legal-sum envelope

This stage validates the selected sum end to end: common envelope syntax,
mode-specific limits, coefficient payloads, and normalized circuit families.
It keeps the existing handoff as the sole success value, so every later caller
has one fail-closed production path and no decoded side channel. -/

/-! ## Coefficient numerator/denominator width validation

The coefficient mapper above is the sole parser for legal terms and canonical
rationals.  This stage consumes its mapped summary: it never re-decodes
untrusted term syntax, and it treats the mapper's zero sentinel as failure. -/

/-! ## Circuit-to-coefficient-width handoff

This lowering reads only the circuit stage's retained mapped coefficient
summary and trusted limit handoff.  Its right component is the complete
circuit-stage value, so a successful width check restores the existing
finalization input exactly. -/

/-! ## Exact coefficient-mass validation

The coefficient pass already produced one canonical rational summary per term.
The production path projects those summaries once, folds them with the shared
exact accumulator, and compares cross-products against the selected rational
cap.  No raw coefficient is decoded again. -/

/-! ### One linked context chain per resource coordinate -/

/-! ### The two lowered resource requests -/

/-! ### Discharging the validated-summary hypothesis of both resource passes

The tree consumed by the two passes is the circuit stage's own retained
`encodeBalancedList` of validator outputs.  If that stage rejected, the tree is
the zero sentinel and decodes to the empty list, so no projection ever reaches
a rejected term. -/

/-! ### The two gated resource stages -/

/-! ### The two resource gates inside the legal-sum envelope

Both gates run on the mass stage's own output, so the retained context reaching
the existing finalization chain is unchanged.  A rejected wire pass replaces
that context with the zero sentinel, and the description pass then sees an
empty summary tree, so no projection of a sentinel ever occurs. -/

/-! ## Fail-closed regressions for the staged validator

Every entry below is a kernel-checked minimal counterexample class for the
staged validator: each names one hostile coordinate and shows that the single
public output collapses to zero.  Rejection always happens at the owning gate,
so no later stage ever unpairs or projects a sentinel. -/

/-! ## Typed limits recovered from the accepted staged handoff

Every acceptance conjunct of the staged validator is stated against a
positional projection of one packed configuration word.  The lemmas below prove
that on the accepting path each projection is exactly the corresponding typed
field of the caller's `RecoveryWitnessLimits`, so no conjunct can ever be
discharged against a cap other than the configured one. -/

/-! ### Positional projections of the packed configuration -/

/-! ### Mode selection on the accepting path -/

/-! ## Acceptance criterion for the structural and Boolean-DAG prefix

The staged prefix composes the outer three-field envelope parser, the
nested-presence guard, and the complete Boolean-DAG validator.  The theorem
below records its exact acceptance condition against the pure canonical
decoders, leaving no intermediate register ABI in the statement. -/

/-! ## Canonical round-trip from structural field checks

`decodeRecoveryWitness` and `decodeLegalCircuitSum` both end with an exact
re-encode guard.  The lemmas below show that guard is *implied* by the
component-level canonical decodes the executable stages already perform:
`decodeTaggedList`, `decodeNat`, `decodeBalancedList`, `decodeBooleanCircuit`
and `decodeLegalCircuitTerm` are each canonical, so re-encoding the decoded
fields reproduces the original code bit for bit.  Consequently no additional
executable canonicality check is required beyond the structural ones, and no
raw code can pass the structural checks while failing the round-trip. -/

/-! ## Coefficient magnitude ABI of one validated term

The coefficient mapper stores the accepted rational as
`pair 1 (pair sign (pair magnitude denominator))`.  The two lemmas below prove
that the magnitude and denominator projections consumed by the coefficient
bit-cap stage are exactly the reduced numerator magnitude and denominator of
the typed rational, so the bit-cap conjunct is the typed `coefficient_bits_le`
condition and not a check on some other integer. -/

/-! ## The public recovery-witness validator endpoint

The staged legal-sum prefix returns the complete accepted handoff, whose first
two components are the accepted mode tag and the original untrusted code.  The
final stage repackages exactly those two components.  On rejection the handoff
is zero and both projections are zero, so the same instructions preserve the
fail-closed sentinel; no second reject block is introduced. -/

-- The exact five-step trace peels the mode tag and the retained raw code.

/-! ### Exact shape of the endpoint output -/

/-! ### Typed resource charges of one accepted per-term summary

The two refinements below turn the wire and description charges the executable
gates compare against their caps into the exact typed metrics of the decoded
normalized circuit, in whichever family the request selects. -/

/-! ### Reconstructing typed legal terms from accepted term codes

The executable per-term stages certify canonical field decodes for every term
code.  The two lemmas below turn those field decodes into a typed term whose
canonical code is the original one, and then assemble the whole accepted code
list into a typed term list with the exact same serialization.  Together with
`decodeLegalCircuitSum_of_canonical_fields` this is everything the pure
decoder needs beyond the field-level facts. -/

/-! ### Field-level consequences of the accepted legal-sum flags

The four structural legal-sum conjuncts are executable flags on register
projections.  The lemmas below translate each of them onto the pure codecs the
canonical decoder itself runs, so `decodeLegalCircuitSum_of_canonical_fields`
can be applied without re-reading any register ABI.  The terms slot the later
per-term stages consume is the tuple's second field *only* on the accepting
side of the term-count gate, so that bound travels with the bundle. -/

/-! ### Canonical outer fields on the accepting path

`recoveryValidatorOraclePrefixOutput_ne_zero_iff` already states acceptance
against the pure decoders, but leaves the accepted mode tag and the nested
legal-sum code as anonymous existentials.  The lemmas below pin them to the
handoff projections the legal-sum stages actually read, which is what the
mode-specific round-trip lemmas require. -/

/-! ### Canonical legal-sum fields on the accepting path

Instantiating the flag-level bundle at the staged handoff and rewriting the
schedule-selected arity through the limits-recovery statement turns the four
structural legal-sum conjuncts into exactly the three field decodes
`decodeLegalCircuitSum` performs. -/

/-! ### Per-term canonical reconstruction

The coefficient pass certifies the two-field term syntax and the canonical
rational; the circuit pass certifies the normalized circuit in the selected
family.  Together they rebuild a typed `LegalCircuitTerm` whose canonical code
is bit-for-bit the accepted term code, which is what
`decodeLegalCircuitSum_of_canonical_fields` consumes. -/

/-! ### Whole-list typed reconstruction

Both per-term passes accept over the same accepted code list, so every term
code carries both certificates at once.  Feeding that through
`exists_legalCircuitTerms_of_codes` produces a typed term list whose
serialization is bit-for-bit the accepted balanced list. -/

/-! ### Typed resource charges of one typed term

The metric refinements are stated against an anonymous validated payload.  The
lemmas below instantiate them at the payload the coefficient pass produces from
a typed term's own canonical code, which removes the last register projection
from the resource conjuncts. -/

/-! ### Per-code resource certificates of the accepting legal sum

The three resource passes accept over payloads derived from the same accepted
code list, so each accepted term code carries its own bit-width, wire and
description certificate.  Each lemma below is stated at one code, which keeps
the later whole-list assembly free of nested balanced-tree reasoning. -/

/-! ### Whole-list typed reconstruction with resource bounds

Combining the per-code certificates with the typed reconstruction produces the
term list `decodeLegalCircuitSum` would build, already carrying its bit-width,
wire and description proof fields.  Only the exact coefficient-mass field of
`CheckedLegalCircuitSum` is not produced here. -/

/-! ### The mass pass reads the coefficient pass's own summaries

`recoveryLegalTermCoefficientMass_eq_legalCircuitSum` is stated against the
named correspondence premise `recoveryLegalTermMassSummariesRepresent`.  The
lemmas below discharge that premise from the executable acceptance facts: the
mass pass maps over exactly the coefficient pass's mapped payload, and the
rational summary it projects from one accepted term code is precisely the
canonical summary of that term's typed coefficient. -/

/-! ### The cross-multiplied mass gate is the exact rational comparison

The executable gate compares integer cross-products of the folded accumulator
with the validated cap summary.  With a canonical, nonnegative cap and a
nonzero accumulator denominator that is exactly the rational inequality
`coefficientMass ≤ coefficientMassCap` of `CheckedLegalCircuitSum`. -/

/-! ### The accepting legal-sum stage builds the typed checked sum

Every proof field of `CheckedLegalCircuitSum` is now discharged: arity and term
count from the structural gates, coefficient widths from the bit-cap gate, the
exact rational mass from the cross-multiplied mass gate, and the two physical
resource bounds from the wire and description gates. -/

/-! ## Soundness half of the decode equivalence

Assembling the outer-field bundle, the legal-sum field bundle and the typed
checked sum discharges every field of `decodeRecoveryWitness`: an accepting
staged validator run certifies a genuine typed recovery witness for the very
code it was handed.  No conjunct of the executable acceptance criterion is
unused, and no additional canonicality check is required. -/

/-! ## Completeness of the structural and Boolean-DAG prefix

The converse of the soundness statement above starts here: a code the pure
decoder accepts already satisfies the exact acceptance criterion of the staged
structural and Boolean-DAG prefix, and the executable mode tag it produces is
the typed witness's own mode tag. -/

/-! ## Completeness of the staged legal-sum envelope

The converse of the soundness chain.  Decode success pins `raw = witness.code`,
so every projection the staged validator reads is a canonical encoding, and each
of the twelve conjuncts of `recoveryValidatorLegalSumPrefixOutput_ne_zero_iff`
is discharged from a proof field the typed checked witness already carries.  No
conjunct needs a hypothesis beyond `CheckedLegalCircuitSum`. -/

/-! ### Per-term certificates of one canonically encoded typed term

The circuit pass accepts the payload the coefficient pass builds from a typed
term's own canonical code, and the two resource metrics it reports are the
typed wire count and description length of that term's circuit. -/

/-! ## The decode equivalence

Soundness and completeness together: the staged validator accepts exactly the
codes the pure canonical decoder accepts. -/

/-! ## The unconditional endpoint identification

The executable endpoint agrees with the pure validator at every input, not just
on the accepting path: rejection is now known to be exactly decode failure. -/

/-! ## Endpoint-level fail-closed regressions

Every hostile class of the staged validator is now a statement about the single
public endpoint output, obtained through the unconditional identification. -/

/-! ## Gap 1 closed

The executable recovery-witness validator and the pure canonical decoder are
now identified unconditionally.  The chain is:

* `recoveryValidatorOraclePrefixOutput_ne_zero_iff` — the staged structural and
  Boolean-DAG prefix accepts exactly the canonical three-field envelopes with a
  decodable in-cap oracle;
* `recoveryValidatorLegalSumPrefixOutput_ne_zero_iff` — the twelve executable
  conjuncts of the legal-sum envelope;
* `exists_decodeRecoveryWitness_of_legalSumAccept` (soundness) and
  `recoveryValidatorLegalSumPrefixOutput_ne_zero_of_decode` (completeness),
  combined in `recoveryValidatorLegalSumPrefixOutput_ne_zero_iff_decode`;
* `recoveryWitnessValidatorProgramOutput_eq` — the endpoint output equals
  `recoveryWitnessValidatorOutput` at every input, so
  `run_recoveryWitnessValidatorProgram_eq_validatorOutput` states the register
  program's run in the pure validator's own vocabulary, and
  `recoveryWitnessValidatorProgram_accepts_with_resources_iff` transfers the
  full typed resource ledger `RecoveryWitnessResourceChecks` verbatim.

Completeness consumes no conjunct-specific side condition: the term count, the
coefficient widths, the exact rational mass, the wire charge and the description
charge are all read off the proof fields of `CheckedLegalCircuitSum`, and the
fold denominator is nonzero by `rationalMassFold_canonical_valid`. -/

end NearCubicWires.CanonicalRecoveryValidatorProgram
