import Proof.CaseAnalysis.FinalRequestAtCursor
import Proof.CaseAnalysis.FinalExactRecordLoop
import Proof.CaseAnalysis.FinalRoundBudget
import Proof.CaseAnalysis.RowsOriginalCount
import Proof.CaseAnalysis.RowsGateArityCheck

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10UnaryAddressProbe
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation SourceInterfaces
open RepairSource.VerifierDecoding RecoveryRootRound
open CloseoutFinalC10ExactRecordLoop CloseoutFinalC10RoundCursor
open CloseoutRowsEstimatorCoefficients.Stream (Entry)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def testInput (j M C : ℕ) : Fin 4 → List Bool :=
  ![ZeroPadding.pad C (UnaryTemplate.tape j), List.replicate M true,
    List.replicate C false, List.replicate C false]
def testOutput (j M C : ℕ) : Fin 4 → List Bool :=
  ![ZeroPadding.pad C (UnaryTemplate.tape j), List.replicate M true,
    ZeroPadding.pad C [decide (j = M)], List.replicate C false]

/-- Real comparison, including its reusable flag and reset log. The index
operand is precisely the padded template on physical cache tape 14. -/
theorem terminal_test (j M C : ℕ) (hC : j + 2 ≤ C) :
    Step CloseoutRowsGateArityCheck.machine (2 * min j M + 6) (fun _ => 0)
      (testInput j M C) (fun _ => 0) (testOutput j M C) := by
  let caps : Fin 4 → ℕ := ![C, 0, C, C]
  obtain ⟨r, hr, ht, hh, _⟩ := CloseoutRowsGateArityCheck.arity_run j M
  have h := (Step.of_run hr (funext hh) ht).pad caps
  have hin : (fun i => ZeroPadding.pad (caps i) (CloseoutRowsGateArityCheck.input j M i))
      = testInput j M C := by
    funext i
    fin_cases i
    · exact pad_template C j hC
    all_goals simp [caps, CloseoutRowsGateArityCheck.input, testInput, ZeroPadding.pad]
  have hout : (fun i => ZeroPadding.pad (caps i) (CloseoutRowsGateArityCheck.output j M i))
      = testOutput j M C := by
    funext i
    fin_cases i
    · exact pad_template C j hC
    · simp [caps, CloseoutRowsGateArityCheck.output, testOutput, ZeroPadding.pad]
    · rfl
    · change ZeroPadding.pad C (List.replicate (min j M + 2) false) = List.replicate C false
      have hmin : min j M + 2 ≤ C :=
        (Nat.add_le_add_right (Nat.min_le_left j M) 2).trans hC
      simp [ZeroPadding.pad, Nat.add_sub_of_le hmin]
  rw [hin, hout] at h
  exact h

end NearCubicWires.RepairOrdinary.CloseoutFinalC10UnaryAddressProbe
