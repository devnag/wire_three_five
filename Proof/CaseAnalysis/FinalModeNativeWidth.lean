import Proof.CaseAnalysis.FinalModeNativeEnvelope
import Proof.CaseAnalysis.FinalPartsSchedule
import Proof.CaseAnalysis.FinalEncoder

/-!
The native denominator width is polynomial in native q, before choosing the
schedule exponent. One polynomial witness then fixes an exponent and finite
onset for the existing entryWidthSchedule. No restriction to the old soundness
cutoff, no physical runtime assertion, and no enlarged resource budget.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeWidth

open NearCubicWires NearCubicWires.PolynomialSchedule
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeEnvelope
open NearCubicWires.RepairOrdinary.CloseoutFinalC10PrimeWindow
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WireEnvelope
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10LedgerAssembly
open NearCubicWires.RepairSource.CloseoutRawRows
open NearCubicWires.RepairSource.CloseoutWitnessResources
open NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem clog_polynomial {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun q => Nat.clog 2 (f q)) :=
  polynomiallyBounded_mono (fun _ => Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le) hf

private theorem seed_polynomial {population denominator : ℕ → ℕ}
    (hp : PolynomiallyBounded population) (hd : PolynomiallyBounded denominator) :
    PolynomiallyBounded (fun q => seedEnvelope (population q) (population q) (denominator q)) :=
  polynomiallyBounded_add
    (polynomiallyBounded_add
      (polynomiallyBounded_mul (polynomiallyBounded_constant 3)
        (polynomiallyBounded_max
          (clog_polynomial (polynomiallyBounded_mul (polynomiallyBounded_constant 256) hp))
          (clog_polynomial hp))) (polynomiallyBounded_constant 1))
    (polynomiallyBounded_mul (polynomiallyBounded_constant 320)
      (clog_polynomial (polynomiallyBounded_add hd (polynomiallyBounded_constant 1))))

private theorem tuple_polynomial (a : DecompositionAlgorithm) {description : ℕ → ℕ}
    (hd : PolynomiallyBounded description) (target : ℕ) :
    PolynomiallyBounded (fun q => tupleCutoffBound a (description q) target) ∧
      PolynomiallyBounded (fun q => tupleListDenominatorBound a (description q) target) := by
  have hchild := sourceChildBound_polynomial a hd
  have h1 := polynomiallyBounded_constant 1
  have hexp : PolynomiallyBounded (fun q => tupleExponentBound a (description q)) :=
    polynomiallyBounded_add
      (polynomiallyBounded_add
        (polynomiallyBounded_mul (polynomiallyBounded_constant 4)
          (clog_polynomial (polynomiallyBounded_add hchild h1)))
        (polynomiallyBounded_mul (polynomiallyBounded_constant 4)
          (polynomiallyBounded_add hchild (polynomiallyBounded_constant 3)))) h1
  have hden : PolynomiallyBounded (fun q => thresholdPrimeDen a (description q) target) :=
    polynomiallyBounded_mul
      (polynomiallyBounded_mul (polynomiallyBounded_constant 2)
        (polynomiallyBounded_pow (polynomiallyBounded_add hchild h1) 4))
      (polynomiallyBounded_constant (target + 1))
  have hcut := primeCutoff_polynomial hexp hden
  exact ⟨hcut, polynomiallyBounded_mul (bits_polynomial hcut)
    (polynomiallyBounded_add hden h1)⟩

variable (sources : EightSources) {gamma : ℝ} (p : Parameters sources gamma)

/-- All cap functions below take native q, not source input length. -/
def arityAt (q : ℕ) : ℕ := max q (selectedPCPP sources).minimumArity

def wireAt (q : ℕ) : ℕ :=
  max (arityAt sources q * (arityAt sources q + 1))
    (max (arityAt sources q) (max ⌊wireScale 1 5 q⌋₊ ⌊wireScale 1 9 q⌋₊))

def carriedDescAt (q : ℕ) : ℕ :=
  thresholdDescription (arityAt sources q)
    (arityAt sources q + clauseWidth p.clauseDegree q + 1) ⌊wireScale 1 9 q⌋₊

def descAt (q : ℕ) : ℕ := max (parityDescCap (arityAt sources q)) (carriedDescAt sources p q)

def denominatorBitsAt (q : ℕ) : ℕ :=
  arityAt sources q +
    max (symSeedBits (wireAt sources q) (stageTarget sources p 0))
      (thrSeedBits (decompositionOf sources) (wireAt sources q) (descAt sources p q)
        (stageTarget sources p 0))

private theorem arity_polynomial : PolynomiallyBounded (arityAt sources) :=
  polynomiallyBounded_max polynomiallyBounded_id
    (polynomiallyBounded_constant (selectedPCPP sources).minimumArity)

private theorem wire_polynomial : PolynomiallyBounded (wireAt sources) :=
  polynomiallyBounded_max
    (polynomiallyBounded_mul (arity_polynomial sources)
      (polynomiallyBounded_add (arity_polynomial sources) (polynomiallyBounded_constant 1)))
    (polynomiallyBounded_max (arity_polynomial sources)
      (polynomiallyBounded_max (wireScaleFloor_polynomial 1 5) (wireScaleFloor_polynomial 1 9)))

private theorem description_polynomial : PolynomiallyBounded (descAt sources p) := by
  have ha := arity_polynomial sources
  have hr : PolynomiallyBounded (clauseWidth p.clauseDegree) :=
    clog_polynomial (polynomiallyBounded_pow
      (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 2)) p.clauseDegree)
  have haug := polynomiallyBounded_add (polynomiallyBounded_add ha hr) (polynomiallyBounded_constant 1)
  exact polynomiallyBounded_max (threshold_description_polynomial ha ha)
    (restricted_threshold_polynomial ha haug (wireScaleFloor_polynomial 1 9))

/-- The cap is fixed before the eventual schedule exponent is chosen. -/
theorem denominatorBitsAt_polynomial : PolynomiallyBounded (denominatorBitsAt sources p) := by
  have hp := polynomiallyBounded_mul (polynomiallyBounded_constant 4) (wire_polynomial sources)
  have htuple := tuple_polynomial (decompositionOf sources) (description_polynomial sources p)
    (stageTarget sources p 0)
  exact polynomiallyBounded_add (arity_polynomial sources)
    (polynomiallyBounded_max
      (seed_polynomial hp (polynomiallyBounded_constant (4 * (stageTarget sources p 0 + 1))))
      (polynomiallyBounded_add
        (clog_polynomial (polynomiallyBounded_add htuple.1 (polynomiallyBounded_constant 1)))
        (seed_polynomial hp htuple.2)))


end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeWidth
