import Proof.Foundations.RecoveryPipeline

/-!
# First-crossing arithmetic for executable recovery schedules

The recovery program searches a fixed increasing sequence of source instances
for the first core whose double exceeds the requested target.  This module
owns the semantic arithmetic of that search.  It is deliberately independent
of PCP and refuter objects: the downstream executable selector must prove that
its decoded output is exactly `firstCrossingSelection`.
-/

namespace NearCubicWires.ScheduleArithmetic

open NearCubicWires.RecoveryPipeline

end NearCubicWires.ScheduleArithmetic
