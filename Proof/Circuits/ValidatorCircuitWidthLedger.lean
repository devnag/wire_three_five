import Proof.Circuits.ValidatorWidthCombinatorLedger

namespace NearCubicWires.ValidatorCircuitWidthLedger

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorLeafPremiseSweep
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.ValidatorCircuitLeafClosure
open NearCubicWires.ValidatorCircuitStageWidths
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorWidthCombinatorLedger

/-! ## §1 The circuit's atom cone -/

/-! ## §3 The ten-way maximum -/

/-! ## §4 The reduced charge, in the domination judgement

The cone is linear in the two width anchors, so the reduction is
degree-preserving: the Boolean circuit validator's width sits at exactly the
larger of its two callees' degrees. -/

/-! ## §5 `hcall`'s residual, at the machine's request family

`ValidatorOracleCallWidth` §3 consumes `hcircuitBits` — the Boolean circuit
validator's width at the oracle handoff's two projections.  §4 replaces it by
the two callee widths at the same projections, with no other premise: the two
width anchors are the published witness anchor and the published prefix
anchor. -/

end NearCubicWires.ValidatorCircuitWidthLedger
