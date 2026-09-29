import Proof.CaseAnalysis.FinalPrinterBridge
import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.CaseAnalysis.RowsEstimatorRecord

set_option autoImplicit false

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch (Step)
open NearCubicWires.RepairOrdinary.CompetitorCountMask (mask selected)
open NearCubicWires.RepairOrdinary.CompetitorFinalTable (lowerColumn)
open NearCubicWires.RepairSource.CloseoutFinal

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierSelect

section Offsets

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- \(\mathbf F(z)=\bigl(C_i(z)\bigr)_i\) (A.3 :1970-1974), a function of the residual
column `z` ALONE (`C10PrinterBridge.residualOffset_spec`). -/
noncomputable def offsetOf
    (z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card)
    (circuitIndex : Fin request.circuits.length) : ℕ :=
  C10PrinterBridge.residualOffset request liveScale z circuitIndex

end Offsets

section Selector

end Selector

section MaskWord

end MaskWord

section Reindex

end Reindex

section SelectedSum

end SelectedSum

section Corollary

end Corollary

section Writer

end Writer

section Run

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- The loop driver's added counter tape is the last one: the body's slots are unchanged. -/
theorem cfg_tapes_castAdd {t s : ℕ} (phase : Fin 5) (data : Configuration t s)
    (total head : ℕ) (i : Fin t) :
    (RepairSource.VerifierDecoding.RepeatMachine.cfg phase data total head).tapes
        (i.castAdd 1) = data.tapes i := by
  simp [RepairSource.VerifierDecoding.RepeatMachine.cfg, controlConfig, TapeEmbedding.config]

end Run

section Consumer

end Consumer

section ExternalRows

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- A.3 :1976 "every possible \(f\in\{0,\ldots,M\}\)": the finite set of offset tuples one
external row is printed for.  It is the corpus's own offset family
(`RowOffsets.SymmetricOffsets`, `Proof/Supplier/RowOffsetFamilies.lean`) read as ℕ. -/
noncomputable def offsetRange : Finset (Fin request.circuits.length → ℕ) :=
  Finset.image (fun w : RowOffsets.SymmetricOffsets request => fun c => (w c).val) Finset.univ

theorem offsetOf_mem_offsetRange
    (z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    offsetOf request liveScale z ∈ offsetRange request := by
  refine Finset.mem_image.mpr ⟨RowOffsets.symmetricOffsets request liveScale
    (C10PrinterBridge.inputOf request liveScale (fun _ => false) z), Finset.mem_univ _, rfl⟩

/-- **A.13.9 :3155-3164, the whole column sum.**  Summing the per-offset external rows over
the offset range restores \(\sum_zT_{e,\mathbf F(z)}(z)\): each residual column is charged
to exactly the one printed row whose offset is its own \(\mathbf F(z)\). -/
theorem offsets_partition
    (T : (Fin request.circuits.length → ℕ) →
      BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card → ℕ) :
    (∑ f ∈ offsetRange request, ∑ z, if offsetOf request liveScale z = f then T f z else 0) =
      ∑ z, T (offsetOf request liveScale z) z := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [Finset.sum_ite_eq (offsetRange request) (offsetOf request liveScale z)
    (fun f => T f z)]
  exact if_pos (offsetOf_mem_offsetRange request liveScale z)

end ExternalRows


end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierSelect