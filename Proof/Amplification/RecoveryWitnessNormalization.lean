import Proof.Amplification.RecoveryWitnessPolicy

/-!
# Canonical normalization of XOR-authorized recovery sums

The XOR theorem speaks about semantic rational sums over the two physical
wire families, while the fixed weak machine decodes normalized canonical
syntax.  This module is the sole bridge between those representations.  Every
finite cap is derived from the XOR witness and the source wire bound; callers
provide no alternate encoding, normalization, or resource envelope.
-/

namespace NearCubicWires.RecoveryWitnessNormalization

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CircuitRestriction
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

end NearCubicWires.RecoveryWitnessNormalization
