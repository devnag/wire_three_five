import Proof.CaseAnalysis.FinalModeNativeWidth
import Proof.CaseAnalysis.FinalStageJoin

/-!
Paper C10's record widths and call counts are polynomial in native q. Combine
their already proved caps before choosing ONE exponent for PartsSchedule.
The finite onset includes that schedule's ledger onset and the soundness cutoff.
Only actual site members receive numeric fits; physical runs and their costs
remain separate obligations. A q-polynomial exponent need not be bounded by k;
the cold source-preprocessing exponent must still satisfy the runtime ledger.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeSchedule

open NearCubicWires NearCubicWires.PolynomialSchedule NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeWidth
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeEnvelope
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeStageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10NaturalStageFields (stageTarget_pos)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageJoin
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10LedgerAssembly
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutWitnessResources
open NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairSource.SelectedRecoveryIntegration
open NearCubicWires.RepairSource.CompetitorRationalGap (zeta)
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierEstimator
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) {gamma : ℝ} (p : Parameters sources gamma)

def clauseAt (q : ℕ) : ℕ :=
  CloseoutSourceCounts.shortBound (selectedPCPP sources)
    (fixedProjection sources).coefficient (fixedProjection sources).degrees.queries p.degree q

def sampleAt (q : ℕ) : ℕ := arityAt sources q + clauseWidth p.clauseDegree q + 1

def coefficientAt (q : ℕ) : ℕ :=
  Nat.log 2 (clauseAt sources p q) + 4 * natBitLength
    (CloseoutXor.cap (zeta (constantsOf sources)) (sampleAt sources p q) p.copies
      * max 1 (2 * clauseAt sources p q)) + 3

def termAt (q : ℕ) : ℕ :=
  2 * clauseAt sources p q * xorTermBound (zeta (constantsOf sources)) (sampleAt sources p q) p.copies

def callAt (q : ℕ) : ℕ :=
  clauseAt sources p q * CloseoutFinalC10CallCountCap.siteCap (termAt sources p q)

def scalarAt (q : ℕ) : ℕ := arityAt sources q + stageScale sources p 0 + 1

def jointCap (q : ℕ) : ℕ :=
  max (denominatorBitsAt sources p q + 1)
    (max (coefficientAt sources p q) (max (callAt sources p q) (scalarAt sources p q)))

theorem jointCap_polynomial : PolynomiallyBounded (jointCap sources p) := by
  have h1 := polynomiallyBounded_constant 1
  have h2 := polynomiallyBounded_constant 2
  have ha : PolynomiallyBounded (arityAt sources) :=
    polynomiallyBounded_max polynomiallyBounded_id
      (polynomiallyBounded_constant (selectedPCPP sources).minimumArity)
  have hclause : PolynomiallyBounded (clauseAt sources p) :=
    CloseoutSourceCounts.shortBound_polynomial _ _ _ _
  have hr : PolynomiallyBounded (clauseWidth p.clauseDegree) :=
    polynomiallyBounded_mono (clause_linear p.clauseDegree)
      (polynomiallyBounded_mul (polynomiallyBounded_constant p.clauseDegree)
        (polynomiallyBounded_add polynomiallyBounded_id h1))
  have hs : PolynomiallyBounded (sampleAt sources p) :=
    polynomiallyBounded_add (polynomiallyBounded_add ha hr) h1
  have hcap : PolynomiallyBounded (fun q =>
      CloseoutXor.cap (zeta (constantsOf sources)) (sampleAt sources p q) p.copies) :=
    polynomiallyBounded_mul
      (polynomiallyBounded_mul (polynomiallyBounded_constant 32) (polynomiallyBounded_add hs h1))
      (polynomiallyBounded_constant ((zeta (constantsOf sources)).den ^ (3 * p.copies + 2)))
  have hc : PolynomiallyBounded (coefficientAt sources p) :=
    polynomiallyBounded_add (polynomiallyBounded_add
      (polynomiallyBounded_mono (fun q => Nat.log_le_self 2 (clauseAt sources p q)) hclause)
      (polynomiallyBounded_mul (polynomiallyBounded_constant 4)
        (bits_polynomial (polynomiallyBounded_mul hcap
          (polynomiallyBounded_max h1 (polynomiallyBounded_mul h2 hclause))))))
      (polynomiallyBounded_constant 3)
  have ht : PolynomiallyBounded (termAt sources p) :=
    polynomiallyBounded_mul (polynomiallyBounded_mul h2 hclause)
      (polynomiallyBounded_comp (xor_terms_polynomial (zeta (constantsOf sources)) p.copies) hs)
  have hcalls : PolynomiallyBounded (callAt sources p) :=
    polynomiallyBounded_mul hclause (polynomiallyBounded_mul (polynomiallyBounded_constant 16)
      (polynomiallyBounded_pow (polynomiallyBounded_add ht h1) 4))
  exact polynomiallyBounded_max
    (polynomiallyBounded_add (denominatorBitsAt_polynomial sources p) h1)
    (polynomiallyBounded_max hc (polynomiallyBounded_max hcalls
      (polynomiallyBounded_add (polynomiallyBounded_add ha
        (polynomiallyBounded_constant (stageScale sources p 0))) h1)))

/-- One exponent, chosen after all numeric caps, and one extensible finite onset. -/
structure Selection (k : ℕ) where
  exponent : ℕ
  onset : ℕ
  parts_le : partsOnset sources k exponent p.clauseDegree ≤ onset
  cutoff_le : Soundness.cutoff (constantsOf sources) ≤ onset
  cap_le : ∀ N, onset ≤ N → jointCap sources p (widthAt sources k N) ≤
    widthPower sources k exponent N

/-- The polynomial witness is selected before k; only its finite onset depends on k. -/
def selected (k : ℕ) : Selection sources p k := by
  let C := Classical.choose (jointCap_polynomial sources p)
  let d := Classical.choose (Classical.choose_spec (jointCap_polynomial sources p))
  have hcap : ∀ q, jointCap sources p q ≤ C * (q + 1) ^ d :=
    (Classical.choose_spec (Classical.choose_spec (jointCap_polynomial sources p))).2
  let onset := max (2 ^ C) (max (partsOnset sources k (d + 1) p.clauseDegree)
    (Soundness.cutoff (constantsOf sources)))
  refine ⟨d + 1, onset, ?_, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · intro N hN
    have hC : C ≤ widthAt sources k N :=
      nativeWidth_ge sources k (PolynomialClock.ordinaryClock k) C N
        ((le_max_left _ _).trans hN)
    calc
      jointCap sources p (widthAt sources k N) ≤ C * (widthAt sources k N + 1) ^ d := hcap _
      _ ≤ (widthAt sources k N + 1) * (widthAt sources k N + 1) ^ d :=
        Nat.mul_le_mul_right _ (hC.trans (Nat.le_succ _))
      _ = widthPower sources k (d + 1) N := by
        unfold widthPower
        rw [pow_succ, Nat.mul_comm]


end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeSchedule
