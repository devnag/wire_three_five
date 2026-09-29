import Proof.Circuits.CanonicalBalancedTraversal

/-!
# Canonical total Booleanization

This is the sole executable boundary from an arbitrary natural-valued stage to
a Boolean code.  Zero maps to zero and every nonzero value maps to one.  In
particular, narrow integer interpolation may be used on a certified good seed
without allowing an uncertified seed to contribute an unbounded value to a
later majority.
-/

namespace NearCubicWires.CanonicalBooleanizeProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.VerifiedLinker

end NearCubicWires.CanonicalBooleanizeProgram
