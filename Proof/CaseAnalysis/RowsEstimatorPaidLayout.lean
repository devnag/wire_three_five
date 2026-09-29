import Proof.CaseAnalysis.RowsEstimatorPrepareWords
import Proof.CaseAnalysis.RowsEstimatorScannedCleanJoin

/-! The actual driver aliases its preserved70 words and D output into the
consumer bank. Every other driver word has a disjoint private port. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tapes (a : WilliamsAlgorithm) (p : Program):=WarmPrepare.tapes p+ScannedClean.tapes a
noncomputable def old (a : WilliamsAlgorithm) (p : Program) (i : Fin (WarmPrepare.tapes p)) : Fin (tapes a p):=
  i.castAdd (ScannedClean.tapes a)
noncomputable def slots (a : WilliamsAlgorithm) (p : Program) (i : Fin (ScannedClean.tapes a)) : Fin (tapes a p):=
  if h:i.val<70 then ⟨i.val,by dsimp [tapes,WarmPrepare.tapes,Reuse.tapes,WholePrefix.tapes];omega⟩
  else if i=ScannedClean.driver a then old a p (WarmPrepare.driver p)
  else i.natAdd (WarmPrepare.tapes p)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
