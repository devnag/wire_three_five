import Proof.Foundations.OuterPCPRecovery

/-!
# Restricting exact-width outer oracles to the native PCP face

Exact-width padding presents the outer proof as a circuit on the common width,
while the imported executable substitution consumes a circuit on its native
width.  The padded verifier queries only the zero-suffix face.  This module
proves that restricting a padded circuit to that face preserves every verifier
row, so both views use one oracle rather than parallel semantic witnesses.
-/

namespace NearCubicWires.PaddedOracleRestriction

open NearCubicWires
open NearCubicWires.CaseOnePadding
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces

end NearCubicWires.PaddedOracleRestriction
