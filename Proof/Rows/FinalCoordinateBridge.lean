import Proof.CaseAnalysis.FinalExternalRowLoop
import Proof.Rows.FinalCircuitRequest

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SourceInterfaces
open NearCubicWires.RepairRepresentation
open NearCubicWires.ThresholdCompiler
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CompetitorCountMask (selected)
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)
open NearCubicWires.RepairSource.CloseoutFinal
open Finset
open scoped BigOperators

namespace NearCubicWires.RepairSource.CloseoutFinal.C10CoordinateBridge

noncomputable section

/-! ## §1  The two conventions, read coordinate by coordinate

Both index maps are a `Fin.addCases` over a two-block split of the residual cube.  They differ in
BOTH the split point and which half the physical row feeds. -/

section Conventions

end Conventions

section SelectConvention

end SelectConvention

section Mismatch

end Mismatch

/-! ## §2  \(B_i(z)\) at a residual column

`frozenScore` (`Proof/Foundations/SupplierPipeline.lean`) is A.2 :1901's
\(B_i(z)=\sum_{j\notin I}w_{ij}z_j\).  Stated over the residual coordinates directly — not over
either half-split — it can afterwards be split along ANY two-block partition. -/

section Residual

variable {n : ℕ} (live : Finset (Fin n))

/-- The ambient coordinate of residual coordinate `j`. -/
def residualCoordinate (j : Fin liveᶜ.card) : Fin n :=
  normalizedLiveExternalCoordinateEquiv live (Sum.inr j)

end Residual

/-! ## §3  The printer's split of the residual cube, and \(B_i\) across it -/

section PrinterSplit

variable {n : ℕ} (live : Finset (Fin n)) (s : ℕ)
  (harity : (s + 1) / 2 + s / 2 = liveᶜ.card)

/-- The ambient coordinate of the printer's ROW half, index `i`. -/
def printerRowCoordinate (i : Fin ((s + 1) / 2)) : Fin n :=
  residualCoordinate live (C10ExternalRowLoop.printerCoordinates live s harity (Sum.inl i))

/-- The ambient coordinate of the printer's COLUMN half, index `i`. -/
def printerColumnCoordinate (i : Fin (s / 2)) : Fin n :=
  residualCoordinate live (C10ExternalRowLoop.printerCoordinates live s harity (Sum.inr i))

/-! ## §4  The encoder at the printer's split

`cutOfGate` (`Proof/Rows/FinalDominanceEncoder.lean`) with the two weight lists taken
at the PRINTER's coordinates.  `Request.lengths`
(`Proof/MachineModel/OrdinaryMatrixScoreBatchCodec.lean`) demands one common width, and here the ROW half
`(s+1)/2` is the larger one, so the COLUMN half is the zero-padded one. -/

/-- Gate weights at the printer's ROW coordinates — the half the physical row carries. -/
def printerRowWeights (gate : NormalizedThresholdGate n) : List ℤ :=
  List.ofFn fun i : Fin ((s + 1) / 2) => gate.weight (printerRowCoordinate live s harity i)

/-- Gate weights at the printer's COLUMN coordinates, zero-padded to `(s+1)/2`. -/
def printerColumnWeights (gate : NormalizedThresholdGate n) : List ℤ :=
  List.ofFn fun i : Fin ((s + 1) / 2) =>
    if hi : i.val < s / 2 then
      gate.weight (printerColumnCoordinate live s harity ⟨i.val, hi⟩)
    else 0

@[simp] theorem printerRowWeights_length (gate : NormalizedThresholdGate n) :
    (printerRowWeights live s harity gate).length = (s + 1) / 2 := by
  simp [printerRowWeights]

@[simp] theorem printerColumnWeights_length (gate : NormalizedThresholdGate n) :
    (printerColumnWeights live s harity gate).length = (s + 1) / 2 := by
  simp [printerColumnWeights]

/-- **The encoder, per gate, at the printer's split.**  A.2 :1913's
\(C_i(z)=\mathbf1[B_i(z)\ge\theta_i-m_i^-]\) as one `MatrixScoreBatch.Cut` at unit coefficient. -/
def printerCutOfGate (gate : NormalizedThresholdGate n) : MatrixScoreBatch.Cut where
  leftWeights := printerRowWeights live s harity gate
  rightWeights := printerColumnWeights live s harity gate
  threshold := gate.threshold - minimumLiveScore gate live
  coefficient := 1

end PrinterSplit

/-! ## §5  The cut list of one circuit, and the identity at the printer's convention -/

section Circuit

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale s : ℕ)
  (harity : (s + 1) / 2 + s / 2 =
    (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card)

/-- The encoder, per occurrence. -/
def printerOccurrenceCut (index : Fin (symmetricFourfoldOccurrences request).length) :
    MatrixScoreBatch.Cut :=
  printerCutOfGate (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale) s harity
    ((symmetricFourfoldOccurrences request).get index).gate

/-- **THE ENCODER at the printer's convention** — `C10DominanceEncoder.circuitCuts`
(`Proof/Rows/FinalDominanceEncoder.lean`) re-stated with the residual cube split at
`(s+1)/2` and the ROW half read by the physical row. -/
def printerCuts (circuitIndex : Fin request.circuits.length) : List MatrixScoreBatch.Cut :=
  (symmetricCircuitMask request circuitIndex).toList.map
    (printerOccurrenceCut request liveScale s harity)

theorem printerCuts_length (circuitIndex : Fin request.circuits.length) :
    (printerCuts request liveScale s harity circuitIndex).length =
      (symmetricCircuitMask request circuitIndex).card := by
  simp [printerCuts]

/-- The `Request.lengths` obligation at the common width `(s+1)/2`. -/
theorem printerCuts_lengths (circuitIndex : Fin request.circuits.length)
    (c : MatrixScoreBatch.Cut) (hc : c ∈ printerCuts request liveScale s harity circuitIndex) :
    c.leftWeights.length = (s + 1) / 2 ∧ c.rightWeights.length = (s + 1) / 2 := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp hc
  exact ⟨printerRowWeights_length _ s harity _, printerColumnWeights_length _ s harity _⟩

/-! ## §6  The printed \(\mathbf F\)-table and its dock -/

/-- The printer-convention `Request`.  `fits` and `gateSquare` are the paper's "polynomial-bit
parameters" and \(s\le2^{r/100}\) (`paper.tex:3317`, `paper.tex:3320`); they are HYPOTHESES here,
exactly as in `C10DominanceEncoder.circuitRequest`
(`Proof/Rows/FinalDominanceEncoder.lean`).  Its width is the PRINTER's `(s+1)/2`, so
`U` is the count table's own `2 ^ ((s+1)/2)`. -/
def printerRequest (circuitIndex : Fin request.circuits.length) (p : ℕ)
    (hfits : ∀ c ∈ printerCuts request liveScale s harity circuitIndex,
      (∀ w ∈ c.leftWeights ++ c.rightWeights, w.natAbs < 2 ^ p) ∧
        c.threshold.natAbs < 2 ^ p ∧ c.coefficient.natAbs < 2 ^ p)
    (hgateSquare : (printerCuts request liveScale s harity circuitIndex).length *
        (printerCuts request liveScale s harity circuitIndex).length ≤
      rectangularInnerDimension (2 ^ ((s + 1) / 2))) : MatrixScoreBatch.Request where
  d := (s + 1) / 2
  p := p
  cuts := printerCuts request liveScale s harity circuitIndex
  lengths := printerCuts_lengths request liveScale s harity circuitIndex
  fits := hfits
  gateSquare := hgateSquare

/-- The printer-convention cut list's own field width — `C10CircuitRequest.circuitWidth`
(`Proof/Rows/FinalCircuitRequest.lean`) at `printerCuts`. -/
def printerWidth (circuitIndex : Fin request.circuits.length) : ℕ :=
  RowBinLift.fieldWidth (printerCuts request liveScale s harity circuitIndex)

theorem printerCuts_fits (circuitIndex : Fin request.circuits.length) :
    ∀ c ∈ printerCuts request liveScale s harity circuitIndex,
      (∀ v ∈ c.leftWeights ++ c.rightWeights,
          v.natAbs < 2 ^ printerWidth request liveScale s harity circuitIndex) ∧
        c.threshold.natAbs < 2 ^ printerWidth request liveScale s harity circuitIndex ∧
        c.coefficient.natAbs < 2 ^ printerWidth request liveScale s harity circuitIndex :=
  RowBinLift.fields_fit (printerCuts request liveScale s harity circuitIndex)

theorem printerCuts_gateSquare (circuitIndex : Fin request.circuits.length)
    (hgates : (symmetricCircuitMask request circuitIndex).card ^ 100 ≤
      2 ^ (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    (printerCuts request liveScale s harity circuitIndex).length *
        (printerCuts request liveScale s harity circuitIndex).length ≤
      rectangularInnerDimension (2 ^ ((s + 1) / 2)) := by
  rw [printerCuts_length]
  refine C10CircuitRequest.gateSquare_of_residual_pow100 ?_ hgates
  omega

/-- **THE PRINTER-CONVENTION `Request`, built.**  The counterpart of
`C10CircuitRequest.printRequest` (`Proof/Rows/FinalCircuitRequest.lean`): one circuit's
\(C_i\) family as an actual `MatrixScoreBatch.Request` at the PRINTER's split, under
`thm:signed-printer`'s gate bound alone. -/
def printerPrintRequest (circuitIndex : Fin request.circuits.length)
    (hgates : (symmetricCircuitMask request circuitIndex).card ^ 100 ≤
      2 ^ (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    MatrixScoreBatch.Request :=
  printerRequest request liveScale s harity circuitIndex
    (printerWidth request liveScale s harity circuitIndex)
    (printerCuts_fits request liveScale s harity circuitIndex)
    (printerCuts_gateSquare request liveScale s harity circuitIndex hgates)

@[simp] theorem printerPrintRequest_cuts (circuitIndex : Fin request.circuits.length)
    (hgates : (symmetricCircuitMask request circuitIndex).card ^ 100 ≤
      2 ^ (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    (printerPrintRequest request liveScale s harity circuitIndex hgates).cuts =
      printerCuts request liveScale s harity circuitIndex :=
  rfl

end Circuit

/-! ## §7  The pairing, and A.13.9 over both concrete tables -/

section Pairing

end Pairing

end


end NearCubicWires.RepairSource.CloseoutFinal.C10CoordinateBridge
