import Proof.CaseAnalysis.WitnessFamilyLoad

/-! The one loaded raw sum and the one verdict write are exactly the
already-checked sum entry. This is a tape identity, not another parser
or serializer; the family source remains outside the sum bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoad
open LocalBitMultitape RecoveryRootRound
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def prepare:=Composition.machine loader prime

end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoad
