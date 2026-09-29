import Batteries.Tactic.OpenPrivate
import Proof.Circuits.AmbientLinkEntry
import Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-!
# The clauses guard request certificate

This module freezes the exact input tuple parsed by the arity guard and the
four component-width facts needed by its bounded writes.  It introduces no new
wire format: `totalSelectiveClausesRequest_eq_private` identifies the tuple
definitionally with the existing private clauses ABI.
-/

namespace NearCubicWires.TotalSelectiveClausesGuardedProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.PolynomialClock

end NearCubicWires.TotalSelectiveClausesGuardedProgram
