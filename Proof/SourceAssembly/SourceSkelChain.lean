import Proof.SourceAssembly.SourceSkelTrace

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton
noncomputable section

section chain
variable {U t : Nat} (N : Nat) (reserve : Fin U → Nat) (slots : Fin t → Fin U)
  (inT : Nat → Fin t → List Bool)
  (Inv : Nat → (Fin U → Nat) → (Fin U → List Bool) → Prop)
  (Good : Nat → (Fin U → Nat) → (Fin U → List Bool) → (Fin U → Nat) → (Fin U → List Bool) → Prop)

/-- **S's per-call seam, abstractly** (`Rest.refill_seam` + `view_padded` + `Inv.view`). -/
def SeamSpec : Prop :=
  ∀ j, j < N → ∀ (H : Fin U → Nat) (A : Fin U → List Bool), Inv j H A →
    ∃ (H' : Fin U → Nat) (A' : Fin U → List Bool), Good j H A H' A' ∧
      (fun x => ZeroPadding.pad (reserve x) (install slots A' (inT (j+1)) x)) = A' ∧
      Inv (j+1) H' (install slots A' (inT (j+1)))

open Classical in
/-- The chain of per-call UNPADDED banks from the first call's bank `(H0, A0)`. -/
def callChain (seam : SeamSpec N reserve slots inT Inv Good) (H0 : Fin U → Nat) (A0 : Fin U → List Bool) :
    Nat → (Fin U → Nat) × (Fin U → List Bool)
  | 0 => (H0, A0)
  | j+1 =>
    if h : j < N ∧ Inv j (callChain seam H0 A0 j).1 (callChain seam H0 A0 j).2 then
      (Classical.choose (seam j h.1 _ _ h.2),
        install slots (Classical.choose (Classical.choose_spec (seam j h.1 _ _ h.2))) (inT (j+1)))
    else callChain seam H0 A0 j

end chain

end
end NearCubicWires.SourceSkeleton
end
