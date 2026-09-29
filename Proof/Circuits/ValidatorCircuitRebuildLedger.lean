import Batteries.Tactic.OpenPrivate
import Proof.MachineModel.CanonicalBooleanNodeListRebuildProgram
import Proof.Circuits.ValidatorCanonicalizerRebuildLedger

/-!
# The Boolean circuit validator, rebuilt — and `hcall` re-landed on it

`ValidatorCircuitWidthLedger` §6 states `hcall` at exactly two callee widths,
`booleanNodeListValidationBits` and `canonicalNatValidationBits`.  Both of those
are **refuted**: `ValidatorTraversalWidthLedger.not_polyBounded_canonicalNat-
ValidationBits` shows no coefficient and no degree dominates the second on the
canonical atom family, and `two_pow_le_booleanNodeListValidationBits` floors the
first at `2 ^ (5 · atoms.length)`.  So the premise list of
`hcall_at_computableLimits_of_two_widths` cannot be met by *any* proof: `hcall`
is not open at those names, it is false at them.

Two modules repaired the programs behind those names at unchanged output
contracts:

* `ValidatorCanonicalizerRebuildLedger.canonicalNatValidationRebuildProgram`
  returns `canonicalNatValidationOutput raw`;

* `CanonicalBooleanNodeListRebuildProgram.booleanNodeListValidationRebuild-
  Program` returns `booleanNodeListValidationOutput inputLength raw`.

This module spends both.  It rebuilds the Boolean circuit validator's two
callee stages on them, re-walks `ValidatorCircuitWidthLedger` §3 verbatim, and
carries the result through the native contextual call to `hcall` — whose
premise list is now the two *rebuilt* widths, neither of which carries a
geometric floor.

* §1 the two rebuilt stages.

* §2 the rebuilt Boolean circuit validator, executed.

* §3 the rebuilt circuit width, reduced to two callee widths.

* §4 the reduced charge, in the domination judgement.

* §5 the rebuilt oracle call.

* §6 `hcall`, at the two rebuilt widths.
-/

namespace NearCubicWires.ValidatorCircuitRebuildLedger

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeListRebuildProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.ValidatorCanonicalizerRebuildLedger
open NearCubicWires.ValidatorCircuitLeafClosure
open NearCubicWires.ValidatorCircuitStageWidths
open NearCubicWires.ValidatorCircuitWidthLedger
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafPremiseSweep
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorOracleCallWidth
open NearCubicWires.ValidatorOracleResultWidth
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.ValidatorWidthCombinatorLedger
open NearCubicWires.VerifiedLinker

/-! ## §1 The two rebuilt stages -/

/-! ## §2 The rebuilt Boolean circuit validator -/

/-! ## §3 The rebuilt circuit width, reduced to two callee widths -/

/-! ## §4 The reduced charge, in the domination judgement -/

/-! ## §5 The rebuilt oracle call -/

/-! ## §6 `hcall`, at the two rebuilt widths -/

end NearCubicWires.ValidatorCircuitRebuildLedger
