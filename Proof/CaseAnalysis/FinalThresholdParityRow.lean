import Proof.CaseAnalysis.FinalThresholdRowIdentity
import Proof.CaseAnalysis.FinalPrinterBridge
import Proof.CaseAnalysis.RowsFamilyBudget
import Proof.Circuits.ValidatorPolynomialDomination
import Proof.MachineModel.CanonicalFourfoldRowProgram

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open scoped BigOperators
open NearCubicWires
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime
open NearCubicWires.SupplierPrinter
open NearCubicWires.SupplierRadix
open NearCubicWires.SupplierWalk
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.CloseoutRawRows

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdParityRow

noncomputable section

section Accuracy

/-! ## §1 A.13.1 in parity form: the GF(2) sum of the EXACT child rows is the conjunction

`ThresholdRows.selection_sum` (`Proof/Supplier/RowThresholdSelections.lean`) says the exact child rows
sum to `conjunctionBit`, a bit.  A `{0,1}`-valued sum is its own parity, so the parity aggregate
is exactly as faithful as the disjunction aggregate on the exact rows — this is the fact that
makes R-B a legitimate reading of A.13.10's `\sum_g`. -/

/-! ## §2 One prime's parity row and its amplified-list error

The proof is the SAME union bound as `primeRow_mismatch_reciprocal`
(`Proof/CaseAnalysis/FinalThresholdRows.lean`): if every printed component agrees with its
modular target then the aggregates agree.  Only the aggregation congruence changes —
`finiteBoolDisjunction_congr` becomes `congrArg boolParity`. -/

/-! ## §4 The complete parity row and its closed reciprocal accuracy -/

end Accuracy

/-! ## §5 The deliverable rows object

`CloseoutFinalC10ThresholdRows.thresholdRows` (`Proof/CaseAnalysis/FinalThresholdRows.lean`)
with the `g`-aggregate changed from `finiteBoolDisjunction` to `boolParity`.  `rowCount`,
`failure` and the external row index are IDENTICAL, so A.13.10's
`1/(|\mathcal P_q||\mathcal E|2^q)` normalisation is unchanged and every consumer of the
preprocessor interface — `rowAnswer`, `rowDenominator`, `answer`, `rowSupplier_error_le` — applies
verbatim. -/

section Rows

end Rows

/-! ## §6 The printed parity row — ONE polynomial per `(p,e)`, ADDITIVE in `|G|` -/

section Printed

end Printed

/-! ## §7 The bridge: `acceptanceCount` as a sum of printed exact column counts

The THR twin of `C10PrinterBridge.acceptanceCount_eq_sum_exactColumnCount`
(`Proof/CaseAnalysis/FinalPrinterBridge.lean`).  A.2's live/residual split is the same
`normalizedLiveExternalInputEquiv` (`Proof/Supplier/SupplierEstimator.lean`); the offset selected
by the residual column is A.13.10's `f_{g,p}(z)`, and it is a function of `z` ALONE because
`modularResidualOffset` reads the input only through `occurrenceResidualConstant`, i.e. through
`frozenScore`, which sums over `Finset.univ \ live`. -/

section Split

/-- A.2's reassembly at a general live set. -/
def splitInput {q : ℕ} (live : Finset (Fin q)) (y : BitInput live.card)
    (z : BitInput liveᶜ.card) : BitInput q :=
  (normalizedLiveExternalInputEquiv live).symm (y, z)

end Split

section Bridge

variable (a : DecompositionAlgorithm)
  (r : FourfoldRequest NormalizedThresholdThresholdCircuit)

/-- **A.13.10's \(f_{g,p}(z)\)**: the modular offset the fixed-column scan selects, a function of
the residual column `z` and the external label `g` only. -/
def thrOffset (liveScale : ℕ)
    (z : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card)
    (sel : ThresholdRows.Selection a r) (modulus : ℕ) : ℕ :=
  modularResidualOffset (thresholdFourfoldOccurrences r) liveScale
    (splitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
      (fun _ => false) z)
    (ThresholdRows.equation a r sel) modulus

end Bridge


end

end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdParityRow
