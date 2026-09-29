import Proof.Foundations.PolynomialClock
import Proof.Foundations.RecoveryPipeline

/-!
# Closing the fixed-machine/refuter clock quantifiers

The executable refuter contract chooses its timed hierarchy *after* the clock.
Accordingly, the local compiler first proves one structural verifier-degree
bound, then freezes a pairing clock above that bound, and only then constructs
the hierarchy-dependent weak machine.  This is the CLW quantifier order.
-/

namespace NearCubicWires.RefuterClockClosure

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces

end NearCubicWires.RefuterClockClosure
