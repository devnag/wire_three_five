import Proof.CaseAnalysis.FinalExactStagePackage
import Proof.CaseAnalysis.FinalThresholdNaturalFit

/-!
An exact C10 stage adapter at A.13.10's natural child sum. Only the numerator
and rational supplier change; the native denominator, fixed accuracy target,
record width, coordinate expansion and machine budget remain the selected ones.
All numeric envelopes below are guarded by actual site membership. The final
constructor retains the physical stage run and its actual fuel as premises.
This mixed-row adapter does not select a physical printer: the left and right
row producers have separate live-set choices. The paper's mode-native parity
route may replace these values; no shared-live-set identity is assumed here.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10NaturalStageFields

open NearCubicWires NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)

/-- The actual natural count on mixed atoms, including systematic parity atoms. -/
def naturalNum (liveScale : ℕ) :
    (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
      Fin (2 ^ (pcppOf sources k p x bits).clauseBits) →
      CircuitMonomial (Atoms sources k p x bits) 4 → ℕ :=
  fun n _ _ _ monomial => C10ThresholdNaturalFit.numerator sources liveScale
    (stageTarget sources p (stageArity sources k n))
    ⟨stageArity sources k n, monomial.factors.map atomToUnion⟩

/-- The mixed rational estimate uses the same fixed accuracy reserve. -/
def naturalSupplier (liveScale : ℕ) :
    (n : ℕ) → (x : BitInput n) → (bits : List Bool) → List (Atoms sources k p x bits) → ℚ :=
  fun n _ _ atoms => C10ThresholdNaturalSum.mixedRatio (decompositionOf sources)
    (expanderOf sources) liveScale (stageTarget sources p (stageArity sources k n))
    ⟨stageArity sources k n, atoms.map atomToUnion⟩

theorem stageTarget_pos (q : ℕ) : 0 < stageTarget sources p q :=
  C10ThresholdNaturalFit.accuracyTargetAll_pos (constantsOf sources) (stageLimits sources p)
    (CloseoutSampledWitness.mass_nonneg _ p.hd p.hh p.copies)

/-- Reuse the exact stage data and replace only the two A.13.10 value fields. -/
def naturalStageData (liveScale : ℕ) (coefficientFloor : ℕ → ℕ) (extra : ℕ)
    (st : Phase → ℕ)
    (stage : (ph : Phase) → LocalBitMultitape.Machine (218 + (60 + extra)) (st ph))
    (stageFuel : Phase → ℕ → ℕ) (L budget : ℕ → ℕ) : StageData' sources k p :=
  { exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget with
    num := naturalNum sources k p liveScale
    supplier := naturalSupplier sources k p liveScale }

section Assembly

variable (liveScale : ℕ) (coefficientFloor seedBits : ℕ → ℕ) (extra : ℕ)
  (st : Phase → ℕ)
  (stage : (ph : Phase) → LocalBitMultitape.Machine (218 + (60 + extra)) (st ph))
  (stageFuel : Phase → ℕ → ℕ) (L budget : ℕ → ℕ)

local notation "S" => naturalStageData sources k p liveScale coefficientFloor extra st
  stage stageFuel L budget

end Assembly


end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10NaturalStageFields
