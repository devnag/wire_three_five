import Proof.MachineModel.CanonicalGateAtomHeadListProgram
import Proof.MachineModel.CanonicalSymmetricRowTableProgram

namespace NearCubicWires.CanonicalOccurrenceRequestProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalGateAtomHeadListProgram
open NearCubicWires.CanonicalSignedAtomRequestProgram
open NearCubicWires.CanonicalSignedGateEvaluationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## §1 The two gate fields a residual request reads

`encodeSupportedNormalizedGate` is a canonical tagged list whose first two
fields are the gate's encoded weight list and its encoded threshold.  Both are
read by fixed `unpair` chains, so no decoder appears below. -/

/-! ## §2 The framing adapter

One straight-line program.  It reads the index, the gate code and the two
masks off its request, extracts the gate's two encoded fields, generates the
four range lengths from the public arity, and assembles §14's input beside the
index it must return. -/

end NearCubicWires.CanonicalOccurrenceRequestProgram
