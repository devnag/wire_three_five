import Proof.CaseAnalysis.FinalBandRecycle

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundCursor

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.CloseoutFinal.C10EnvelopeCounter
open NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The cursor word -/

/-- A fixed-width binary word determines its value below the width's capacity. -/
theorem fixedWidthNatBits_inj {width a b : ℕ} (ha : a < 2 ^ width) (hb : b < 2 ^ width)
    (h : WilliamsPublishedForm.fixedWidthNatBits width a
      = WilliamsPublishedForm.fixedWidthNatBits width b) : a = b := by
  unfold WilliamsPublishedForm.fixedWidthNatBits at h
  have hfun : (fun bit : Fin width => a.testBit bit.val)
      = fun bit : Fin width => b.testBit bit.val := List.ofFn_inj.mp h
  refine Nat.eq_of_testBit_eq (fun i => ?_)
  by_cases hi : i < width
  · simpa using congrFun hfun ⟨i, hi⟩
  · have hp : (2 : ℕ) ^ width ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb hp)]

/-! ## §2 The envelope the paper names, and the width it needs -/

/-! ## §3 The cost of the unary alternative, measured -/

/-! ## §4 The invariant -/

/-! ## §5 The two things the record ports cannot do, and the bank past the
envelope -/

/-! ## §6 THE DELIVERABLE: the all-`k` form of `Rounds`, without
`AddressDeterminacy` -/


end NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundCursor
