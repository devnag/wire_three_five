import Proof.CaseAnalysis.RowsEstimatorPreparedPorts

/-! Symbolic consumer projections avoid unfolding the Williams controller. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem embedded_heads (p : Program) (out : List Bool) :
    Fin.addCases (fun i : Fin (Reuse.tapes p)=>if i=Reuse.output p then out.length else 0)
      (fun _ : Fin 7=>0)=WarmPrepare.heads p out := by
  funext i
  refine Fin.addCases (m:=Reuse.tapes p) (n:=7) (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left,WarmPrepare.heads,WarmPrepare.spare]
    by_cases hj : j=Reuse.output p
    · subst j
      simp only [ite_true]
    · simp only [hj,ite_false]
      split_ifs with hit
      · exact False.elim (hj (Fin.ext (congrArg (fun z : Fin (WarmPrepare.tapes p)=>z.val) hit)))
      · rfl
  · simp only [Fin.addCases_right]
    change 0=WarmPrepare.heads p out (WarmPrepare.source p j)
    simp only [WarmPrepare.heads,source_ne p j,ite_false]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared
