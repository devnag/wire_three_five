import Proof.CaseAnalysis.WitnessFamilyLoopData

/-! The same canonical outer list produces the actual V driver and the
ordered original sum fields. The already-produced source V is retained
without charging its magnitude as raw parsing scratch. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyFields
open LocalBitMultitape RecoveryRootRound PCPPNativeCanonicalWalk PCPPNativeCanonicalTree
open RepairSource.VerifierDecoding RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def words (bits : List Bool):=Reencode.fields bits

end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyFields
