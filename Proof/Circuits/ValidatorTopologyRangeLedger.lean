import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorOracleResultWidth

namespace NearCubicWires.ValidatorTopologyRangeLedger

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafFuelBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorResidualLeafBudget
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

/-! ## §1 One comparison request -/

/-! ## §2 The per-descriptor topology charge -/

/-! ### The budgets, dominated -/

/-! ## §3 The range aggregation

`booleanNodeTopologyRangeFuel` is one `fixedBooleanRangeAggregationFuel`: a
generated range, a counted call at the descriptor count, and one Boolean count.
The counted call is the only degree-raising node. -/

end NearCubicWires.ValidatorTopologyRangeLedger
