import Proof.Circuits.HeadlineClosure
import Proof.Foundations.PhysicalHardness

/-!
# Adapters from physical recovery facts to the exact headline closures

These definitions merely expose the already-paid factor-27 coefficients under
the names expected by `HeadlineClosure`.  They add no recovery premise and do
not alter the language, onset, advantage, or per-mode circuit statements.
-/

namespace NearCubicWires.PhysicalHeadlineAdapters

open NearCubicWires
open NearCubicWires.HeadlineClosure
open NearCubicWires.PhysicalHardness
open NearCubicWires.RecoveryPipeline

end NearCubicWires.PhysicalHeadlineAdapters
