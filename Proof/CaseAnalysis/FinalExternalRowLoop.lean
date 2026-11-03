import Proof.CaseAnalysis.FinalSources
import Proof.CaseAnalysis.FinalSupplierRowInput
import Proof.CaseAnalysis.FinalSupplierSelect
import Proof.CaseAnalysis.FinalSupplierTable
import Proof.CaseAnalysis.FinalSupplierWidth
import Proof.CaseAnalysis.RowsEstimatorDriverBounds
import Proof.CaseAnalysis.RowsEstimatorLinearBudget
import Proof.CaseAnalysis.RowsEstimatorWhole
import Proof.CaseAnalysis.RowsEstimatorWholePrefix
import Proof.CaseAnalysis.RowsRawRecord
import Proof.MachineModel.NativeFamily

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
open NearCubicWires.RepairOrdinary.CompetitorSelectedCount
open NearCubicWires.RepairOrdinary.CompetitorCountMask (selected)
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)
open NearCubicWires.ExtDecompositionBatch (Step)
open NearCubicWires.RepairSource.CloseoutFinal
open Finset
open scoped BigOperators

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ExternalRowLoop

/-! ## 1. The printer's own cell-addressing convention -/

section PrinterPoint

variable {n : ℕ} (live : Finset (Fin n)) (s : ℕ) (harity : (s + 1) / 2 + s / 2 = liveᶜ.card)

/-- **The printer's coordinate split of the residual cube**: the ROW half first
(`C10SupplierRowInput.halfPoint`, `Proof/CaseAnalysis/FinalSupplierRowInput.lean`), then the
COLUMN half. -/
def printerCoordinates : Fin ((s + 1) / 2) ⊕ Fin (s / 2) ≃ Fin liveᶜ.card :=
  finSumFinEquiv.trans (finCongr harity)

/-- **The residual column addressed by the printed table's cell `(rowN, colN)`** — literally the
point `C10SupplierTable.table_eq_exactColumnCount`
(`Proof/CaseAnalysis/FinalSupplierTable.lean`) reads. -/
def printerPoint (rowN colN : ℕ) : BitInput liveᶜ.card :=
  C10SupplierRowInput.residualPoint live s harity
    (C10SupplierRowInput.halfPoint ((s + 1) / 2) (s / 2) rowN colN)

end PrinterPoint

/-! ## 2. The column scan in the printer's convention, and A.13.9's per-offset sum -/

section Selector

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale s : ℕ)
  (harity : (s + 1) / 2 + s / 2 =
    (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card)

/-- **A.3 :1978-1979 in the printer's coordinates**: the physical cell `(i,j)` is selected exactly
when the residual column the PRINTED TABLE put there has offset tuple \(\mathbf f\). -/
noncomputable def printerSelect (f : Fin request.circuits.length → ℕ) {u : ℕ} :
    Fin u → Fin u → Bool :=
  fun i j => decide (C10SupplierSelect.offsetOf request liveScale
    (printerPoint (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale) s harity
      i.val j.val) = f)

end Selector

/-! ## 3. The external-row family, and the count its record words total -/

/-- A.13.9's list denominator for this request. -/
def familyDenominator (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  symmetricListDenominator request (targetDenominator request.q)

/-- **One printed external row** (A.3 :1976-1978): seed `sample`, offset tuple `f`. -/
noncomputable def familyPolynomial (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (sample : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
      (familyDenominator targetDenominator request))
    (f : Fin request.circuits.length → ℕ) : StructuralGF2Polynomial :=
  structuralCanonicalSymmetricFourfoldRow request liveScale
    (familyDenominator targetDenominator request) sample f

/-- **The payload of one external row's record word** — A.13.9's
\(\sum_{z:\mathbf F(z)=\mathbf f}T_{e,\mathbf f}(z)\). -/
noncomputable def pairValue (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (sample : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
      (familyDenominator targetDenominator request))
    (f : Fin request.circuits.length → ℕ) : ℕ :=
  ∑ z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card,
    if C10SupplierSelect.offsetOf request liveScale z = f then
      exactColumnCount (C10PrinterBridge.residualHolds request liveScale)
        (familyPolynomial liveScale targetDenominator request sample f) z
    else 0

/-- The `|\mathcal E|` seeds of A.13.9, enumerated. -/
noncomputable def seedList (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List (NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
      (familyDenominator targetDenominator request)) :=
  (Finset.univ : Finset (NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request)
    liveScale (familyDenominator targetDenominator request))).toList

/-- The offset tuples of A.3 :1976, enumerated. -/
noncomputable def offsetList (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List (Fin request.circuits.length → ℕ) :=
  (C10SupplierSelect.offsetRange request).toList

/-- **The rounds of the loop**: the seeds crossed with the offset range. -/
noncomputable def pairList (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List ((NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
      (familyDenominator targetDenominator request)) ×
      (Fin request.circuits.length → ℕ)) :=
  (seedList liveScale targetDenominator request).flatMap
    (fun e => (offsetList request).map (fun f => (e, f)))

theorem length_flatMap_const {A B : Type} (l : List A) (h : A → List B) (m : ℕ)
    (hm : ∀ a, (h a).length = m) : (l.flatMap h).length = l.length * m := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, ih, hm x, List.length_cons]
    ring

theorem sum_map_flatMap {A B : Type} (l : List A) (h : A → List B) (g : B → ℕ) :
    ((l.flatMap h).map g).sum = (l.map (fun a => ((h a).map g).sum)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem offsetList_length (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (offsetList request).length = (C10SupplierSelect.offsetRange request).card := by
  unfold offsetList
  exact Finset.length_toList _

theorem seedList_length (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (seedList liveScale targetDenominator request).length =
      Fintype.card (NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
        (familyDenominator targetDenominator request)) := by
  unfold seedList
  rw [Finset.length_toList, Finset.card_univ]

/-- **`|\mathcal E|` times the offset range** rounds: `2 ^ seedExponent` seeds
(`C10SupplierWidth.rowCount_eq_two_pow`, `Proof/CaseAnalysis/FinalSupplierWidth.lean`) crossed
with A.3 :1976's offsets. -/
theorem pairList_length (spectrum : SourceInterfaces.ExpanderSpectrumContract) (liveScale : ℕ)
    (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (pairList liveScale targetDenominator request).length =
      2 ^ C10SupplierWidth.seedExponent request liveScale (targetDenominator request.q) *
        (C10SupplierSelect.offsetRange request).card := by
  unfold pairList
  rw [length_flatMap_const _ _ ((C10SupplierSelect.offsetRange request).card)
      (fun _ => by rw [List.length_map]; exact offsetList_length request),
    seedList_length]
  exact congrArg (fun x => x * (C10SupplierSelect.offsetRange request).card)
    (C10SupplierWidth.rowCount_eq_two_pow spectrum liveScale targetDenominator request)

/-- **THE COUNT.**  The record-word payloads of the whole external-row family total exactly
`FiniteRowAggregation.acceptanceCount` of the symmetric supplier's rows — A.13.9 :3155-3164's
\(\sum_e\sum_zT_{e,\mathbf F(z)}(z)\). -/
theorem familyTotal_eq_acceptanceCount (spectrum : SourceInterfaces.ExpanderSpectrumContract)
    (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (((pairList liveScale targetDenominator request).map
        (fun p => pairValue liveScale targetDenominator request p.1 p.2)).sum) =
      ((symmetricFourfoldRows spectrum liveScale targetDenominator).aggregation
        request).acceptanceCount := by
  unfold pairList
  rw [sum_map_flatMap]
  have hrow : ∀ e : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
        (familyDenominator targetDenominator request),
      (((offsetList request).map (fun f => (e, f))).map
          (fun p => pairValue liveScale targetDenominator request p.1 p.2)).sum =
        ∑ z : BitInput
            (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card,
          exactColumnCount (C10PrinterBridge.residualHolds request liveScale)
            (familyPolynomial liveScale targetDenominator request e
              (C10SupplierSelect.offsetOf request liveScale z)) z := by
    intro e
    rw [List.map_map]
    have hlist : ((offsetList request).map
        ((fun p => pairValue liveScale targetDenominator request p.1 p.2) ∘
          fun f => (e, f))).sum =
        ∑ f ∈ C10SupplierSelect.offsetRange request,
          pairValue liveScale targetDenominator request e f :=
      Finset.sum_map_toList (C10SupplierSelect.offsetRange request)
        (fun f => pairValue liveScale targetDenominator request e f)
    rw [hlist]
    exact C10SupplierSelect.offsets_partition request liveScale
      (fun f z => exactColumnCount (C10PrinterBridge.residualHolds request liveScale)
        (familyPolynomial liveScale targetDenominator request e f) z)
  rw [List.map_congr_left (fun e _ => hrow e)]
  unfold seedList
  rw [Finset.sum_map_toList (Finset.univ : Finset
      (NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
        (familyDenominator targetDenominator request)))
      (fun e => ∑ z : BitInput
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card,
        exactColumnCount (C10PrinterBridge.residualHolds request liveScale)
          (familyPolynomial liveScale targetDenominator request e
            (C10SupplierSelect.offsetOf request liveScale z)) z)]
  exact (C10PrinterBridge.acceptanceCount_eq_sum_exactColumnCount spectrum liveScale
    targetDenominator request).symm

/-! ## 4. One round: the external row, and the record word it prints -/

section Round

end Round

/-! ## 5. The family loop: one machine, one accumulated stream, one count -/

/-- The family scan's driver: the corpus's own literal loop driver
(`CloseoutRowsDegreeLoop.machine`, `Proof/CaseAnalysis/RowsDegreeLoop.lean`), one round per printed
external row. -/
noncomputable def familyWriter {tp st : ℕ} (body : Machine tp st) :=
  CloseoutRowsDegreeLoop.machine body

/-- **The whole family's fuel** — one external row per round at `rowCost`, plus the driver's three
paid steps per round and its final rewind. -/
def familyFuel (pairCount rowCost : ℕ) : ℕ := pairCount * (rowCost + 3) + 3

/-- The record word of one round. -/
noncomputable def pairWord (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (b : ℕ) (est : CompetitorValidity.Estimate) (denominator : ℕ)
    (sample : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
      (familyDenominator targetDenominator request))
    (f : Fin request.circuits.length → ℕ) : List Bool :=
  Stream.recordWord b est (pairValue liveScale targetDenominator request sample f) denominator

/-- The family's record words, in scan order. -/
noncomputable def wordList (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (b : ℕ) (est : CompetitorValidity.Estimate) (denominator : ℕ) : List (List Bool) :=
  (pairList liveScale targetDenominator request).map
    (fun p => pairWord liveScale targetDenominator request b est denominator p.1 p.2)

/-- **The accumulated stream**: the record words of the whole external-row family. -/
noncomputable def familyStream (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (b : ℕ) (est : CompetitorValidity.Estimate) (denominator : ℕ) : List Bool :=
  (wordList liveScale targetDenominator request b est denominator).flatten

theorem flatten_getD {B : Type} (xs : List (List B)) :
    (List.range xs.length).flatMap (fun j => xs.getD j []) = xs.flatten := by
  have he : (List.range xs.length).map (fun j => xs.getD j []) = xs := by
    apply List.ext_getElem
    · simp
    · intro i _ hi
      simp only [List.getElem_map, List.getElem_range]
      exact List.getD_eq_getElem xs [] hi
  rw [List.flatMap_def, he]

/-- **SITE item 3.2 — the external-row family loop.**  Given a round body that runs one printed
external row and appends its record word (`row_step` is that run, at each pair), the corpus's
literal loop driver lays the WHOLE family's record stream on the body's output slot inside
`familyFuel`, and the payloads of those words total `FiniteRowAggregation.acceptanceCount` —
A.13.9's \(\sum_e\sum_zT_{e,\mathbf F(z)}(z)\). -/
theorem family_run (spectrum : SourceInterfaces.ExpanderSpectrumContract) (liveScale : ℕ)
    (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    {tp st : ℕ} (body : Machine tp st)
    (source : ℕ → List Bool → Configuration tp st) (slot : Fin tp) (rowCost : ℕ)
    (b : ℕ) (est : CompetitorValidity.Estimate) (denominator : ℕ) (out : List Bool)
    (hslot : ∀ k pre, (source k pre).tapes slot = pre)
    (hstart : ∀ k < (wordList liveScale targetDenominator request b est denominator).length,
      ∀ pre, (source k pre).control = body.start)
    (hrow : ∀ k < (wordList liveScale targetDenominator request b est denominator).length,
      ∀ pre, ∃ rc : ExecutionReceipt tp st,
        runFrom body rowCost (source k pre) = some rc ∧
        rc.final.heads = (source (k + 1) (pre ++
          (wordList liveScale targetDenominator request b est denominator).getD k [])).heads ∧
        rc.final.tapes = (source (k + 1) (pre ++
          (wordList liveScale targetDenominator request b est denominator).getD k [])).tapes ∧
        rc.steps ≤ rowCost) :
    ∃ T, Step (familyWriter body)
        (familyFuel (wordList liveScale targetDenominator request b est denominator).length rowCost)
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (source 0 out)
          (wordList liveScale targetDenominator request b est denominator).length 1).heads
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (source 0 out)
          (wordList liveScale targetDenominator request b est denominator).length 1).tapes
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 3
          (source (wordList liveScale targetDenominator request b est denominator).length
            (out ++ familyStream liveScale targetDenominator request b est denominator))
          (wordList liveScale targetDenominator request b est denominator).length 1).heads T ∧
      T (slot.castAdd 1) =
        out ++ familyStream liveScale targetDenominator request b est denominator ∧
      (((pairList liveScale targetDenominator request).map
          (fun p => pairValue liveScale targetDenominator request p.1 p.2)).sum) =
        ((symmetricFourfoldRows spectrum liveScale targetDenominator).aggregation
          request).acceptanceCount := by
  obtain ⟨r, hr, hf, hst⟩ := CloseoutRowsDegreeLoop.loop_run body source
    (fun k => (wordList liveScale targetDenominator request b est denominator).getD k []) rowCost
    (wordList liveScale targetDenominator request b est denominator).length hstart hrow out
  rw [flatten_getD (wordList liveScale targetDenominator request b est denominator)] at hf
  refine ⟨_, ⟨r, hr, congrArg Configuration.heads hf, congrArg Configuration.tapes hf, hst⟩, ?_,
    familyTotal_eq_acceptanceCount spectrum liveScale targetDenominator request⟩
  rw [C10SupplierSelect.cfg_tapes_castAdd]
  exact hslot _ _


end NearCubicWires.RepairSource.CloseoutFinal.C10ExternalRowLoop
