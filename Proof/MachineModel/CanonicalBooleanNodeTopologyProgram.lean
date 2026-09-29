import Proof.MachineModel.CanonicalBooleanNodeValidationProgram
import Proof.MachineModel.CanonicalBooleanRangeAggregationProgram
import Proof.MachineModel.CanonicalFourfoldRowProgram
import Proof.MachineModel.CanonicalNativeCallProgram

/-!
# Indexed Boolean-node topology validation

Structural node validation produces a compact descriptor.  This module turns
one descriptor and its machine-generated index into two explicit native
less-than requests, executes both through the sole native-call/paired-call
path, and conjoins the results.  Unary cases use a fixed true comparison;
malformed descriptors use a fixed false comparison.
-/

namespace NearCubicWires.CanonicalBooleanNodeTopologyProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanNodeValidationProgram
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RegisterBounds
open NearCubicWires.VerifiedLinker

/-! ## Descriptor-to-comparison lowering -/

/-! ## Fixed native less-than calls -/

/-! ## Boolean conjunction tail -/

/-! ## Closed descriptor-topology program -/

/-! ## Indexed lookup wrapper for the generated range -/

/-! ## All-node topology aggregation -/

end NearCubicWires.CanonicalBooleanNodeTopologyProgram
