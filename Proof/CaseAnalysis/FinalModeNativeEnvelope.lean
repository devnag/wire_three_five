import Proof.CaseAnalysis.FinalModeNativeStageFields
import Proof.CaseAnalysis.FinalPrimeWindow

/-!
Native-mode denominator bounds, from admitted wire and description envelopes.
The THR denominator counts primes and walk seeds, never child labels. One
native request has one occurrence pool. All stage bounds retain membership.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeEnvelope

open NearCubicWires NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeStageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10PrimeWindow
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WireEnvelope
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10NaturalModeAtoms
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10SiteWireEnvelope
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open NearCubicWires.RepairSource.SelectedRecoveryIntegration

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def parityDescCap (q : ℕ) : ℕ := thresholdDescriptionCap q q

/-- Reuse the existing normalized-circuit bound on the actual native parity.
This is the short F2 proof at the C10 circuit, without importing the F2 graph. -/
theorem nativeThresholdParity_description {q : ℕ} (support : Finset (Fin q)) :
    (CloseoutRowsEstimatorParity.normalizedThresholdParityCircuit support).descriptionBits ≤
      parityDescCap q := by
  have hcard : support.card ≤ q := by simpa using Finset.card_le_univ support
  apply normalizedThreshold_descriptionBits_le
  · exact hcard
  · intro index
    have hi : index.val < support.card := index.isLt
    have hq : 0 < q := by omega
    have hpow : q ≤ q ^ q := by
      calc q = q ^ 1 := by simp
        _ ≤ q ^ q := Nat.pow_le_pow_right hq (by omega)
    constructor
    · intro coordinate
      change (if coordinate ∈ support then (1 : ℤ) else 0).natAbs ≤ q ^ q
      split <;> norm_num
      exact (by omega)
    · change index.val + 1 ≤ q ^ q
      exact ((Nat.succ_le_iff.mpr index.isLt).trans hcard).trans hpow
  · have hone : 1 ≤ support.card ^ support.card := by
      by_cases hz : support.card = 0
      · simp [hz]
      · have hp := Nat.pow_pos (Nat.pos_of_ne_zero hz) (n := support.card)
        omega
    constructor
    · intro index
      change (if Even index.val then (1 : ℤ) else -1).natAbs ≤ support.card ^ support.card
      split <;> norm_num
      all_goals exact hone
    · change (1 : ℤ).natAbs ≤ support.card ^ support.card
      norm_num
      exact hone

def symSeedBits (wireCap target : ℕ) : ℕ :=
  seedEnvelope (4 * wireCap) (4 * wireCap) (4 * (target + 1))

def thrSeedBits (a : DecompositionAlgorithm) (wireCap descCap target : ℕ) : ℕ :=
  Nat.clog 2 (tupleCutoffBound a descCap target + 1) +
    seedEnvelope (4 * wireCap) (4 * wireCap) (tupleListDenominatorBound a descCap target)

variable (sources : EightSources) (liveScale target : ℕ)

theorem familyCoordinate_description {Circuit : CanonicalWitnessCodec.CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ} {limits : LegalSumLimits}
    {variableCount arity : ℕ} (harity : limits.expectedArity = arity)
    (family : SumFamily Circuit wires description limits variableCount) (i : Fin variableCount) :
    (familyCoordinate harity family i).FactorsSatisfy
      (fun circuit => description circuit ≤ limits.descriptionCap) := by
  unfold familyCoordinate
  refine linearPolynomial_factorsSatisfy _ _ ?_
  intro term hterm
  exact wires_le_of_mem_transportTerms description _ (family.getSum i).value.terms
    limits.descriptionCap (family.getSum i).description_le term hterm


end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeEnvelope
