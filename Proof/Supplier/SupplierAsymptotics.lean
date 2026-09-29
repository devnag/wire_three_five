import Proof.Foundations.AsymptoticAdapters
import Proof.MachineModel.SupplierRuntime

/-!
# Supplier asymptotic closure

The supplier implementation proves concrete error and integer step bounds.
This module performs the only quantifier and asymptotic packaging needed by
the published A.1/A.2 interfaces: it combines finite onsets, weakens caps in
the safe direction, and converts a master integer saving inequality into the
real-valued runtime envelope.  It introduces no alternate supplier or runner.
-/

namespace NearCubicWires.SupplierAsymptotics

open NearCubicWires
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierRuntime

end NearCubicWires.SupplierAsymptotics
