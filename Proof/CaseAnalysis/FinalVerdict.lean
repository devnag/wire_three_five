import Proof.CaseAnalysis.FinalRealizes
import Proof.CaseAnalysis.FinalLengthGate

namespace NearCubicWires.RepairSource.CloseoutFinal.C10Verdict

open LocalBitMultitape RepairOrdinary RepairOrdinary.CloseoutWitness
open RepairRepresentation CompetitorRationalGap ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open CloseoutRowsOriginalSchedule
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- The paper's admissible range for each phase. C.10 validity plus C.10.1. -/
def bound {source : PointwisePCPPAlgorithm} (constants : Constants source) :
    Phase → ℝ
  | .penalty => 2*((zeta constants : ℚ) : ℝ)
  | .moment => 1+((zeta constants : ℚ) : ℝ)
  | .clause => ((midpoint constants : ℚ) : ℝ)

/-- Paper C.10 + C.10.1, fused with the length gate over ONE execution. -/
structure Verdict {t s : ℕ} {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    {source : PointwisePCPPAlgorithm}
    (constants : Constants source) (pcpp : PointwisePCPP circuit)
    (proofValue : BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (evaluate : Atom → BitInput n → Bool)
    (p : Machine t s) (ht : 2 ≤ t) (budget : ℕ → ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool)
    (result : Fin t) (ports : Phase → Fin t) (width : Phase → ℕ) where
  /-- Paper: reject every length below the soundness cutoff. -/
  gate : LengthGate constants p ht result budget
  heads : Fin t → ℕ
  exit : Fin t → List Bool
  /-- **The machine halts at EVERY length.** Above the cutoff this is the
  estimator's run; below it, the gate's rejection (`gated_reject`). `StepAtInputs`
  needs both, so the run is unconditional while the three `Realizes` are not. -/
  run : Step p (budget len) (fun _ => 0)
    ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) bits) heads exit
  /-- One `Realizes` per phase, at the SAME run, above the cutoff. -/
  realizes : Soundness.cutoff constants ≤ len → ∀ ph : Phase,
    Realizes ph constants pcpp proofValue evaluate p (budget len) (fun _ => 0)
      ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) bits)
      (ports ph) (width ph)
  /-- Determinism of `runFrom` makes this true; it is a field so the sharing is
  syntactic rather than re-derived at every use. -/
  hshared : ∀ (h : Soundness.cutoff constants ≤ len) (ph : Phase),
    (realizes h ph).exit = exit
  /-- The three estimated reals of C.10. -/
  estimate : Phase → ℝ
  hestimate : ∀ (h : Soundness.cutoff constants ≤ len) (ph : Phase),
    estimate ph = (((realizes h ph).result.value : ℚ) : ℝ)
  /-- C.10 validity and C.10.1 acceptance, exactly. -/
  accepts_iff : readTapeBit (exit result) (heads result) = true ↔
    (Soundness.cutoff constants ≤ len ∧
      estimate .penalty ≤ bound constants .penalty ∧
      estimate .moment ≤ bound constants .moment ∧
      bound constants .clause ≤ estimate .clause)

variable {t s : ℕ} {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
variable {source : PointwisePCPPAlgorithm} {constants : Constants source}
variable {pcpp : PointwisePCPP circuit}
variable {proofValue : BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ}
variable {evaluate : Atom → BitInput n → Bool}
variable {p : Machine t s} {ht : 2 ≤ t} {budget : ℕ → ℕ}
variable {len : ℕ} {x : BitInput len} {bits : List Bool}
variable {result : Fin t} {ports : Phase → Fin t} {width : Phase → ℕ}

/-- **Paper C.10.2 at the verdict.** Every estimated real the verdict compares is
within `eps_est` of the paper's mean for its phase. -/
theorem accurate_of_verdict
    (V : Verdict constants pcpp proofValue evaluate p ht budget len x bits result ports width)
    (h : Soundness.cutoff constants ≤ len) (ph : Phase) :
    |V.estimate ph - CloseoutRowsOriginalSchedule.mean ph pcpp proofValue| ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
  rw [V.hestimate h ph]
  exact accurate_of_realizes (V.realizes h ph)

end
end NearCubicWires.RepairSource.CloseoutFinal.C10Verdict
