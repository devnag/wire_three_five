import Proof.CaseAnalysis.RawRowsModeDegree
import Proof.CaseAnalysis.RawRowsLoad
import Proof.CaseAnalysis.RowsUniversalResources
import Proof.CaseAnalysis.FinalThresholdRows

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open scoped BigOperators
open NearCubicWires
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.CloseoutRawRows
open NearCubicWires.RepairSource.CloseoutRowsUniversal

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdRowIdentity

noncomputable section

variable (a : DecompositionAlgorithm)
  (r : FourfoldRequest NormalizedThresholdThresholdCircuit)

/-! ## 1. The printed row IS the estimator's row (A.13.6/A.13.7) -/

/-! ## 2. A.13.8 — the per-row preprocessing budget, with NO `|G|` factor -/

/-! ## 3. Where the paper's label `g` lives: OUTSIDE the printed row -/

/-- **THE TASK-ZERO RECEIPT.**  The external row count of `thresholdRows` enumerates the prime `p`
and the amplified-list seed `e` and NOTHING else: it carries no
`Fintype.card (ThresholdRows.Selection a r)` factor.  Together with
`fourfoldRow_eq_printedDisjunction` (the paper's `g` is aggregated OUTSIDE the printed polynomial)
and `thresholdRow_degree_le` (each printed polynomial's budget has exponent
`modulusDigitCount prime.val`, never `|G|`), this is the Lean statement of
`paper.tex:3216–3219`: the external labels `(g,p,e,f)` are paid by `T_prep`, not by `s_gen`.  The
normalisation matches A.13.10's `1/(|\mathcal P_q||\mathcal E|2^q)`, which likewise has no
`|\mathcal G|`. -/
theorem thresholdRows_rowCount (spectrum : SourceInterfaces.ExpanderSpectrumContract)
    (theta : SourceInterfaces.PrimeThetaBoundContract)
    (liveScale : ℕ) (targetDenominator : ℕ → ℕ) :
    (CloseoutFinalC10ThresholdRows.thresholdRows spectrum theta a liveScale
        targetDenominator).rowCount r =
      Fintype.card
        (PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r (targetDenominator r.q)) ×
          NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
            (CloseoutFinalC10ThresholdRows.listDenominator a r (targetDenominator r.q))) := by
  simp only [CloseoutFinalC10ThresholdRows.thresholdRows]


end

end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdRowIdentity
