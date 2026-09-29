import Proof.Foundations.ScheduledRecovery

/-!
# Determinacy of the Case-2 seed

`caseTwoTable` selects a `SourceHonestPCPPTable` with choice, but every such
table pins its executable component to the one factory chosen before any
oracle, and its support bound is propositional.  The semantic table, the
padded occurrence function, and the scheduled Case-2 seed are therefore
independent of the selection.  An executable layer may construct any concrete
table and identify its output with the scheduled seed through these lemmas;
no second seed definition and no new choice is introduced.
-/

namespace NearCubicWires.CaseTwoSeedDeterminacy

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery

end NearCubicWires.CaseTwoSeedDeterminacy
