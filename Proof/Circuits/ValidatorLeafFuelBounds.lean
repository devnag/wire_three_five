import Proof.Circuits.ValidatorLeafWidthCore

namespace NearCubicWires.ValidatorLeafFuelBounds

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.VerifiedLinker

/-! ## §1 The counting ledgers -/

/-! ## §2 The balanced canonicalization pipeline

Every node of the pipeline is a linker or a context-preserving wrapper, so the
whole of it stays at the degree of the *node count* certificate it is handed. -/

end NearCubicWires.ValidatorLeafFuelBounds
