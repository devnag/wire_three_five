import Proof.CaseAnalysis.RowsSupportFamily
import Proof.CaseAnalysis.WitnessFamilyMeaning

/-! The actual strengthened cold family consumes the original Fits ledger.
Its old streams retain their existing semantic predicate, and the one new
support tape carries the actual ordered family/term/gate accumulation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySupport
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev Actual:=CloseoutRowsSupportStream.FamilyCold.machine

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySupport
