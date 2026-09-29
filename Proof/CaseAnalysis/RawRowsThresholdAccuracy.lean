import Proof.CaseAnalysis.RawRowsThresholdSize
import Proof.CaseAnalysis.RawRowsModeBounds

/-! The actual threshold family uses coarse source-fixed metadata. Its
selection SUM, prime normalization and two error reserves remain unchanged. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open SupplierPipeline SupplierEstimator SupplierPrime SourceInterfaces RepairRepresentation
open PolynomialSchedule RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def thresholdFamilyBound (a : DecompositionAlgorithm) (desc : ℕ) :=
  (sourceChildBound a desc+1)^4
def thresholdPrimeDen (a : DecompositionAlgorithm) (desc target : ℕ) :=
  reciprocalUnionDenominator (thresholdFamilyBound a desc) target
def thresholdCutoff (a : DecompositionAlgorithm) (desc target : ℕ) :=
  canonicalPrimeCutoff (thresholdMagnitudeExponent a desc) (thresholdPrimeDen a desc target)
def thresholdListDen (a : DecompositionAlgorithm) (desc target : ℕ) :=
  modulusDigitCount (thresholdCutoff a desc target)*(thresholdPrimeDen a desc target+1)

theorem threshold_parameters_polynomial (a : DecompositionAlgorithm) (degree : ℕ)
    (target : ℕ → ℕ) (ht : PolynomiallyBounded target) :
    PolynomiallyBounded (fun q=>thresholdPrimeDen a (descriptionEnvelope degree q) (target q)) ∧
    PolynomiallyBounded (fun q=>thresholdCutoff a (descriptionEnvelope degree q) (target q)) ∧
    PolynomiallyBounded (fun q=>thresholdListDen a (descriptionEnvelope degree q) (target q)) := by
  have h1 := polynomiallyBounded_constant 1
  have hF := polynomiallyBounded_pow (polynomiallyBounded_add
    (sourceChildBound_polynomial a (descriptionEnvelope_polynomial degree)) h1) 4
  have hden := polynomiallyBounded_mul (polynomiallyBounded_mul (polynomiallyBounded_constant 2) hF)
    (polynomiallyBounded_add ht h1)
  have hcut := primeCutoff_polynomial (thresholdMagnitudeExponent_polynomial a degree) hden
  refine ⟨hden,hcut,?_⟩
  exact polynomiallyBounded_mul (CloseoutWitnessResources.bits_polynomial hcut)
    (polynomiallyBounded_add hden h1)

end
end NearCubicWires.RepairSource.CloseoutRawRows
