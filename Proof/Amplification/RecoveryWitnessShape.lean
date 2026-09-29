import Proof.Amplification.RecoveryWitnessPolicy

/-!
# Canonical globally admissible weak-witness shape

The refuter contract requires a fixed executable witness width bounded by one
tenth of every input length, including small lengths.  A four-bit right shift
computes `n / 16` exactly, avoiding the capacity troughs of pairing-coordinate
projections while leaving linear room for the eventual polylogarithmic
recovery certificate.
-/

namespace NearCubicWires.RecoveryWitnessShape

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.VerifiedLinker

/-! ## Canonical zero extension -/

end NearCubicWires.RecoveryWitnessShape
