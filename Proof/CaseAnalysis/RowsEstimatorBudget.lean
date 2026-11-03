import Proof.CaseAnalysis.CloseoutRowsEstimatorCold

/-! A coarse additive preprocessing envelope in the actual retained row
scalars and literal cut-byte length. It has no external-row cardinality or
columnwise size assumption, and introduces no Williams table factor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Cold
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem header_scalar (n : ℕ) : EquationHeaderAppend.budget n≤200*(n+1)^2:=by
  have hn:natBitLength n≤n+1:=by
    unfold natBitLength
    exact Nat.succ_le_succ (Nat.log_le_self 2 n)
  unfold EquationHeaderAppend.budget
  nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Cold
