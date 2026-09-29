import Proof.CaseAnalysis.WitnessSumCountStream

/-! The all-raw sum header uses one reusable allocated bank. Its exact
term fields and actual count feed the existing loop directly. The source
arity and cap ports are retained without imposing a workspace bound on them. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumHeader
open LocalBitMultitape RecoveryRootRound PCPPNativeCanonicalWalk RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def flag (bits arityBits : List Bool) (T : ℕ) : Bool := by
  classical
  exact decide (SumGuard.Passes bits arityBits T)
def words (bits : List Bool) := Reencode.fields (SumFields.listCode bits)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumHeader
