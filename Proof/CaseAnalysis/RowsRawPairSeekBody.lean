import Proof.CaseAnalysis.RowsRawAtomSeek

/-! The A.2 source cache is ordered X,C at each occurrence. One original
occurrence index advances over these two existing cache entries together;
no doubled index word or second cache is manufactured. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawPairSeek
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open CloseoutRowsRawAtomSeek (heads data advance advance_run skip skip_run)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Pair:=List (List ℕ)×List (List ℕ)
def word (p : Pair):=ExtIncidence.stream p.1++ExtIncidence.stream p.2
def cacheWord (ps : List Pair):=ps.flatMap word
noncomputable def skipPair:=Composition.machine skip skip
noncomputable def body:=Composition.machine skipPair advance

end NearCubicWires.RepairOrdinary.CloseoutRowsRawPairSeek
