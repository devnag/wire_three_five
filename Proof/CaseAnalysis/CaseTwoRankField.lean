import Proof.CaseAnalysis.CaseTwoDirect
import Proof.CaseAnalysis.RowsCountBinary

/-! The original canonical description uses unary-rank fields.  Their
literal trailing false bits are allocation, so the existing total unary
converter consumes them without a new decoder or a numeric-value loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RankField
open LocalBitMultitape RepairSource.VerifierDecoding OuterPCPRecovery
open RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ordered_eq_pad (limit value : Nat) (hvalue : value ≤ limit) :
    orderedNatBits limit value = ZeroPadding.pad limit (List.replicate value true) := by
  apply List.ext_getElem
  · simp [orderedNatBits,ZeroPadding.pad_length,Nat.max_eq_left hvalue]
  · intro i hi hj
    have hil : i < limit := by simpa [orderedNatBits] using hi
    simp only [orderedNatBits,List.getElem_map,List.getElem_range]
    by_cases hiv : i < value
    · simp [ZeroPadding.pad,List.getElem_append_left,hiv]
    · simp only [decide_eq_false hiv,ZeroPadding.pad,List.length_replicate]
      rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hiv)]
      simp


end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RankField
