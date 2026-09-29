import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.CanonicalNatValidationProgram
import Proof.MachineModel.CanonicalTaggedListValidationProgram

/-!
# Canonical natural validation over one tagged field list

Fixed witness records repeatedly contain canonical naturals.  This module
provides their single list-level execution path: validate the tagged spine,
convert it to the sole balanced ABI, attach register-one to every call, run the
total canonical-natural validator, and flatten the results back to a tagged
stream.  Invalid spines become the empty stream; malformed fields remain zero
atoms, so the record-specific continuation can reject them without reparsing
the public bytes.
-/

namespace NearCubicWires.CanonicalTaggedNatListValidationProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalTaggedListValidationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Retain exactly one validated tagged spine -/

/-! ## One shared field-validation pipeline -/

end NearCubicWires.CanonicalTaggedNatListValidationProgram
