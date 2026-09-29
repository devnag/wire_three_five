import Proof.CaseAnalysis.RowsCircuitTermSupplier
import Proof.CaseAnalysis.CloseoutWitnessFamilyRun

/-! The two actual circuit workers instantiate the whole family ABI.
The predicate is the same public circuit decoder and original wire and
description guards; no worker certificate is an external premise. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyMode
open LocalBitMultitape CloseoutRowsCircuitTermSupplier
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def flag (sym : Bool) (core W L : ℕ):=
  if sym then symmetricFlag core W L else thresholdFlag core W L

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyMode
