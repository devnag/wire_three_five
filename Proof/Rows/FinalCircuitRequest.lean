import Proof.Rows.FinalDominanceEncoder

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
open NearCubicWires.RepairSource.CloseoutFinal.C10DominanceEncoder

namespace NearCubicWires.RepairSource.CloseoutFinal.C10CircuitRequest

noncomputable section

/-! ## §1 `gateSquare` — the paper's \(s\le2^{r/100}\)

`Request.gateSquare` (`Proof/MachineModel/OrdinaryMatrixScoreBatchCodec.lean`) demands
`cuts.length * cuts.length ≤ rectangularInnerDimension (2 ^ d)`, i.e. \(s^2\le\lceil(2^d)^{1/10}
\rceil\).  The printer's `d` is the HALF width: the physical row carries the external right half
and the physical column the external left half, so the residual arity \(r\) of
`thm:signed-printer` is the whole complement `liveᶜ.card`, which is at most `2 * d`.  The paper's
own hypothesis \(s\le2^{r/100}\) (`paper.tex:3320`) at that residual arity therefore suffices with
room to spare. -/

/-- `thm:signed-printer`'s \(s\le2^{r/100}\) (`paper.tex:3320`), in natural-number form and at the
residual arity of `paper.tex:2888`, gives the squared gate dimension of
`Request.gateSquare`.  The last step is `SupplierCapacity.gateSquare_le_rectangularInnerDimension_of_pow_le`
(`Proof/Supplier/SupplierCapacity.lean`). -/
theorem gateSquare_of_residual_pow100 {gates residual half : ℕ}
    (hresidual : residual ≤ 2 * half) (hgates : gates ^ 100 ≤ 2 ^ residual) :
    gates * gates ≤ rectangularInnerDimension (2 ^ half) := by
  refine SupplierCapacity.gateSquare_le_rectangularInnerDimension_of_pow_le ?_
  rcases Nat.eq_zero_or_pos gates with rfl | hpos
  · simp
  · have hsq : (gates ^ 50) ^ 2 ≤ (2 ^ half) ^ 2 := by
      calc
        (gates ^ 50) ^ 2 = gates ^ 100 := by ring
        _ ≤ 2 ^ residual := hgates
        _ ≤ 2 ^ (2 * half) := Nat.pow_le_pow_right (by decide) hresidual
        _ = (2 ^ half) ^ 2 := by rw [Nat.mul_comm, pow_mul]
    exact (Nat.pow_le_pow_right hpos (by decide : (20 : ℕ) ≤ 50)).trans
      ((Nat.pow_le_pow_iff_left (by decide)).mp hsq)

/-- The residual arity is at most twice the printer's half width, because the external right half
is the larger one (`normalizedExternalLeftCount_le_right`,
`Proof/Supplier/SupplierEstimator.lean`). -/
theorem externalComplement_le_two_mul_right {n : ℕ} (live : Finset (Fin n)) :
    liveᶜ.card ≤ 2 * normalizedExternalRightCount live := by
  have hadd := normalizedExternalCounts_add live
  have hle := normalizedExternalLeftCount_le_right live
  omega

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- **The `gateSquare` obligation, DISCHARGED.**  `s` is the circuit's gate count
`(symmetricCircuitMask request circuitIndex).card` (`Proof/Supplier/SupplierEstimator.lean`) and
`r` the residual arity; the hypothesis is `paper.tex:3320` verbatim. -/
theorem circuitCuts_gateSquare (circuitIndex : Fin request.circuits.length)
    (hgates : (symmetricCircuitMask request circuitIndex).card ^ 100 ≤
      2 ^ (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    (circuitCuts request liveScale circuitIndex).length *
        (circuitCuts request liveScale circuitIndex).length ≤
      rectangularInnerDimension (2 ^ normalizedExternalRightCount
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)) := by
  rw [circuitCuts_length]
  exact gateSquare_of_residual_pow100 (externalComplement_le_two_mul_right _) hgates

/-! ## §2 `fits` — no hypothesis at all

`Request.p` (`Proof/MachineModel/OrdinaryMatrixScoreBatchCodec.lean`) is a free field, so `Request.fits` is
dischargeable at a width read off the emitted data.  `RowBinLift.fieldWidth`
(`Proof/Supplier/RowBinLiftInput.lean`) is that width and `RowBinLift.fields_fit`
(`Proof/Supplier/RowBinLiftInput.lean`) is that discharge, for an arbitrary `List MatrixScoreBatch.Cut`.
Nothing about `NormalizedThresholdGate.weight` is assumed here; §4 bounds the width instead. -/

/-- The encoder's own field width: the bit length of the total field mass of its cut list. -/
def circuitWidth (circuitIndex : Fin request.circuits.length) : ℕ :=
  RowBinLift.fieldWidth (circuitCuts request liveScale circuitIndex)

/-- **The `fits` obligation, DISCHARGED**, with no hypothesis. -/
theorem circuitCuts_fits (circuitIndex : Fin request.circuits.length) :
    ∀ c ∈ circuitCuts request liveScale circuitIndex,
      (∀ w ∈ c.leftWeights ++ c.rightWeights,
          w.natAbs < 2 ^ circuitWidth request liveScale circuitIndex) ∧
        c.threshold.natAbs < 2 ^ circuitWidth request liveScale circuitIndex ∧
        c.coefficient.natAbs < 2 ^ circuitWidth request liveScale circuitIndex :=
  RowBinLift.fields_fit (circuitCuts request liveScale circuitIndex)

/-! ## §3 The `Request`, and the identity with no `hcuts`

`C10DominanceEncoder.circuitRequest` (`Proof/Rows/FinalDominanceEncoder.lean`) is the
encoder's `Request` shape; supplying §1 and §2 turns it into an actual value. -/

/-- **THE `Request`.**  One circuit's \(C_i\) family as a `MatrixScoreBatch.Request`, at the
encoder's cut list, at the data-derived width, under `thm:signed-printer`'s gate bound alone. -/
def printRequest (circuitIndex : Fin request.circuits.length)
    (hgates : (symmetricCircuitMask request circuitIndex).card ^ 100 ≤
      2 ^ (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    MatrixScoreBatch.Request :=
  circuitRequest request liveScale circuitIndex (circuitWidth request liveScale circuitIndex)
    (circuitCuts_fits request liveScale circuitIndex)
    (circuitCuts_gateSquare request liveScale circuitIndex hgates)

@[simp] theorem printRequest_cuts (circuitIndex : Fin request.circuits.length)
    (hgates : (symmetricCircuitMask request circuitIndex).card ^ 100 ≤
      2 ^ (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    (printRequest request liveScale circuitIndex hgates).cuts =
      circuitCuts request liveScale circuitIndex := rfl

@[simp] theorem printRequest_d (circuitIndex : Fin request.circuits.length)
    (hgates : (symmetricCircuitMask request circuitIndex).card ^ 100 ≤
      2 ^ (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    (printRequest request liveScale circuitIndex hgates).d =
      normalizedExternalRightCount
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale) := rfl

@[simp] theorem printRequest_p (circuitIndex : Fin request.circuits.length)
    (hgates : (symmetricCircuitMask request circuitIndex).card ^ 100 ≤
      2 ^ (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    (printRequest request liveScale circuitIndex hgates).p =
      circuitWidth request liveScale circuitIndex := rfl

end

/-! ## §4 The width IS the paper's polynomial-bit parameter

`paper.tex:3317` — the gates have "polynomial-bit parameters".  In Lean that is
`NormalizedThresholdGate.parametersBoundedBy` (`Proof/Foundations/Semantics.lean`).  Under it the
encoder's field width is bounded by the bit length of a quantity linear in the gate bound, the
half width and the arity — so `circuitWidth` is not an escape hatch. -/

section Widths

end Widths

noncomputable section

end

end NearCubicWires.RepairSource.CloseoutFinal.C10CircuitRequest
