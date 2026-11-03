import Proof.CaseAnalysis.FinalThresholdNaturalSum

/-!
C10's natural THR/mixed numerator reuses the existing denominator envelope.
A.13.10 excludes the child population from the denominator. Accuracy bounds
the actual numerator by twice that denominator, so its already-reserved
extra bit suffices; no separate log-|G| width is required.
-/

open NearCubicWires NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.SupplierWalk
open NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdNaturalFit

open C10ThresholdNaturalSum C10UnionSupplier CloseoutFinalC10ThresholdRows

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- The exact existing left sample population at the two-way reserve. -/
def leftRows (sources : EightSources) (liveScale target : ℕ) :=
  symmetricFourfoldRows (expanderOf sources) liveScale
    (fun _ => reciprocalUnionDenominator 1 target)

def numerator (sources : EightSources) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) : ℕ :=
  mixedNativeNumeratorOf (decompositionOf sources) (leftRows sources liveScale target)
    liveScale (reciprocalUnionDenominator 1 target) request

def denominator (sources : EightSources) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) : ℕ :=
  mixedNativeDenominatorOf (decompositionOf sources) (leftRows sources liveScale target)
    liveScale (reciprocalUnionDenominator 1 target) request

/-- Native mixed denominator equals the current union row denominator exactly. -/
theorem denominator_eq_rowDenominator (sources : EightSources) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) :
    denominator sources liveScale target request =
      rowDenominator (unionAtomRows sources liveScale (fun _ => target))
        request.q request.circuits := by
  unfold denominator mixedNativeDenominatorOf nativeDenominator rowDenominator
  rw [unionAtomRows_rowCount]
  rw [C10ThresholdRowIdentity.thresholdRows_rowCount]
  simp only [Fintype.card_prod, Nat.mul_assoc]
  rfl

theorem denominator_pos (sources : EightSources) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) :
    0 < denominator sources liveScale target request := by
  rw [denominator_eq_rowDenominator]
  exact rowDenominator_pos _ _ _

/-- The selected fraction matches the mixed rational estimator. -/
theorem ratio_eq (sources : EightSources) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) :
    (numerator sources liveScale target request : ℚ) /
      denominator sources liveScale target request =
        mixedRatio (decompositionOf sources) (expanderOf sources) liveScale target request := rfl

/-- The stage's existing constant accuracy target is positive whenever its
coefficient-mass cap is nonnegative. This introduces no new accuracy choice. -/
theorem accuracyTargetAll_pos {source : PointwisePCPPAlgorithm}
    (constants : CompetitorRationalGap.Constants source)
    (limits : CanonicalWitnessCodec.LegalSumLimits) (hmass : 0 ≤ limits.coefficientMassCap) :
    0 < C10SupplierAccuracyChain.accuracyTargetAll constants limits := by
  have hm : (0 : ℚ) < C10FamilyMass.siteMassBound limits.coefficientMassCap .penalty := by
    dsimp [C10FamilyMass.siteMassBound]
    positivity
  have h := C10SupplierAccuracyChain.accuracyTarget_spec constants limits .penalty
    (C10SupplierAccuracyChain.accuracyTargetAll constants limits)
    (C10SupplierAccuracyChain.accuracyTarget_le_all constants limits .penalty)
  by_contra hn
  have hz : C10SupplierAccuracyChain.accuracyTargetAll constants limits = 0 :=
    Nat.eq_zero_of_not_pos hn
  rw [hz, Nat.cast_zero, zero_mul] at h
  have hp : (0 : ℝ) < 2 * (C10FamilyMass.siteMassBound limits.coefficientMassCap .penalty : ℚ) := by
    exact_mod_cast (mul_pos (by norm_num : (0 : ℚ) < 2) hm)
  exact (not_le_of_gt hp) h


end
end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdNaturalFit
