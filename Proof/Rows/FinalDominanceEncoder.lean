import Proof.CaseAnalysis.FinalSupplierSelect

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.SourceInterfaces
open NearCubicWires.ThresholdCompiler
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter
open NearCubicWires.RepairOrdinary

namespace NearCubicWires.RepairSource.CloseoutFinal.C10DominanceEncoder

noncomputable section

/-! ## §1 The two frozen half-weight vectors

`B_i(z)=\sum_{j\notin I}w_{ij}z_j` (`paper.tex:1901`) splits over the two external halves of
`normalizedLiveSet`: the physical ROW address carries the larger external RIGHT half and the
physical COLUMN address the smaller external LEFT half
(`RowExternalSelection.input`, `Proof/Supplier/RowExternalSelection.lean`).  `Request.lengths`
(`Proof/MachineModel/OrdinaryMatrixScoreBatchCodec.lean`) demands ONE common width, so the smaller
half is zero-padded to `normalizedExternalRightCount`. -/

variable {q : ℕ}

/-- Gate weights at the external RIGHT coordinates — the half the physical row carries. -/
def rowWeights (gate : NormalizedThresholdGate q) (live : Finset (Fin q)) : List ℤ :=
  List.ofFn fun index : Fin (normalizedExternalRightCount live) =>
    gate.weight (normalizedExternalRightCoordinate live index)

/-- Gate weights at the external LEFT coordinates — the half the physical column carries —
zero-padded to the common width `normalizedExternalRightCount`
(`normalizedExternalLeftCount_le_right`, `Proof/Supplier/SupplierEstimator.lean`). -/
def columnWeights (gate : NormalizedThresholdGate q) (live : Finset (Fin q)) : List ℤ :=
  List.ofFn fun index : Fin (normalizedExternalRightCount live) =>
    if hindex : index.val < normalizedExternalLeftCount live then
      gate.weight (normalizedExternalLeftCoordinate live ⟨index.val, hindex⟩)
    else 0

@[simp] theorem rowWeights_length (gate : NormalizedThresholdGate q) (live : Finset (Fin q)) :
    (rowWeights gate live).length = normalizedExternalRightCount live := by
  simp [rowWeights]

@[simp] theorem columnWeights_length (gate : NormalizedThresholdGate q) (live : Finset (Fin q)) :
    (columnWeights gate live).length = normalizedExternalRightCount live := by
  simp [columnWeights]

/-! ## §2 `B_i(z)` as the two linear forms

`frozenScore` (`Proof/Foundations/SupplierPipeline.lean`) is the paper's \(B_i(z)\).  The live
half of `normalizedSplitInput` contributes nothing to it, so the frozen score of a split input is
exactly the sum of the two external half-scores. -/

/-! ## §3 The encoder, one gate at a time

`C_i(z)=\mathbf1[B_i(z)\ge\theta_i-m_i^-]` (`paper.tex:1913`) is exactly one
`MatrixScoreBatch.Cut` (`Proof/MachineModel/OrdinaryMatrixScoreBatchCodec.lean`) at unit
coefficient: threshold \(\theta_i-m_i^-\), left weights the row half, right weights the padded
column half. -/

/-- **The encoder, per gate.** -/
def cutOfGate (gate : NormalizedThresholdGate q) (live : Finset (Fin q)) : MatrixScoreBatch.Cut where
  leftWeights := rowWeights gate live
  rightWeights := columnWeights gate live
  threshold := gate.threshold - minimumLiveScore gate live
  coefficient := 1

/-! ## §4 The encoder, one circuit at a time

`F(z)=\sum_iC_i(z)` (`paper.tex:1973`) sums the `C_i` of ONE circuit's occurrence mask
`symmetricCircuitMask` (`Proof/Supplier/SupplierEstimator.lean`). -/

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- **The encoder, per occurrence.** -/
def occurrenceCut (index : Fin (symmetricFourfoldOccurrences request).length) :
    MatrixScoreBatch.Cut :=
  cutOfGate ((symmetricFourfoldOccurrences request).get index).gate
    (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)

/-- **The encoder.**  Circuit `circuitIndex`'s `C_i` family as a `MatrixScoreBatch.Cut` list. -/
def circuitCuts (circuitIndex : Fin request.circuits.length) : List MatrixScoreBatch.Cut :=
  (symmetricCircuitMask request circuitIndex).toList.map (occurrenceCut request liveScale)

theorem circuitCuts_length (circuitIndex : Fin request.circuits.length) :
    (circuitCuts request liveScale circuitIndex).length =
      (symmetricCircuitMask request circuitIndex).card := by
  simp [circuitCuts]

/-- The `Request.lengths` obligation (`Proof/MachineModel/OrdinaryMatrixScoreBatchCodec.lean`):
every encoded cut has both halves at the common width. -/
theorem circuitCuts_lengths (circuitIndex : Fin request.circuits.length)
    (c : MatrixScoreBatch.Cut) (hc : c ∈ circuitCuts request liveScale circuitIndex) :
    c.leftWeights.length = normalizedExternalRightCount
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale) ∧
      c.rightWeights.length = normalizedExternalRightCount
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale) := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp hc
  exact ⟨rowWeights_length _ _, columnWeights_length _ _⟩

/-! ## §6 The encoder's `Request`

`fits` and `gateSquare` are the paper's "polynomial-bit parameters" and \(s\le2^{r/100}\)
(`paper.tex:3317`, `paper.tex:3320`).  They are HYPOTHESES here, not facts proved here; only
`lengths` is encoder work. -/

def circuitRequest (circuitIndex : Fin request.circuits.length) (p : ℕ)
    (hfits : ∀ c ∈ circuitCuts request liveScale circuitIndex,
      (∀ w ∈ c.leftWeights ++ c.rightWeights, w.natAbs < 2 ^ p) ∧
        c.threshold.natAbs < 2 ^ p ∧ c.coefficient.natAbs < 2 ^ p)
    (hgateSquare : (circuitCuts request liveScale circuitIndex).length *
        (circuitCuts request liveScale circuitIndex).length ≤
      rectangularInnerDimension (2 ^ normalizedExternalRightCount
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale))) :
    MatrixScoreBatch.Request where
  d := normalizedExternalRightCount
    (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
  p := p
  cuts := circuitCuts request liveScale circuitIndex
  lengths := circuitCuts_lengths request liveScale circuitIndex
  fits := hfits
  gateSquare := hgateSquare

end

end NearCubicWires.RepairSource.CloseoutFinal.C10DominanceEncoder
