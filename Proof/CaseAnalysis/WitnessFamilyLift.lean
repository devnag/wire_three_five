import Proof.CaseAnalysis.WitnessFamilyMeaning

/-! Generic retained-tape lifting keeps the enclosing source state count
opaque while proving the three exact unused-bank projections. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilyLift
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (E : ℕ) {t : ℕ} (i : Fin t):=
  FamilyCold.Call.old (FamilyCapacity.Call.old E (i.castAdd 1))



end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilyLift
