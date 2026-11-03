import Proof.MachineModel.ClosureRadix
import Proof.Supplier.RowTupleCommonEquation
import Proof.Supplier.RowTupleFixedCapacity
import Proof.Supplier.RowTupleCursorEquation
import Proof.Supplier.RowTupleCursorLayout
import Proof.Supplier.RowTupleCursorBody
import Proof.Supplier.RowTupleFramedBody
import Proof.Supplier.RowTupleEnumeratedEquations
import Proof.Supplier.RowTupleCutBody
import Proof.Supplier.RowTupleCutList
import Proof.CaseAnalysis.RowsEnumeratedCuts
import Proof.CaseAnalysis.RowsComputedCuts
import Proof.CaseAnalysis.RowsDegreeReset
import Proof.CaseAnalysis.RowsCacheInput
import Proof.CaseAnalysis.RowsCutMeaning
import Proof.CaseAnalysis.RowsReusableCuts
import Proof.CaseAnalysis.RowsLoopLayout
import Proof.CaseAnalysis.RowsLoopBoundary
import Proof.CaseAnalysis.RowsLoopInterface
import Proof.CaseAnalysis.RowsDegreeBody
import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.CaseAnalysis.RowsDegreeRange
import Proof.CaseAnalysis.RowsPolynomial
import Proof.CaseAnalysis.RowsSharedDigits
import Proof.CaseAnalysis.RowsSharedInput
import Proof.CaseAnalysis.RowsPreparationBounds
import Proof.CaseAnalysis.RowsPreparationFits
import Proof.CaseAnalysis.RowsPreparationInput
import Proof.CaseAnalysis.RowsBankFields
import Proof.CaseAnalysis.RowsBankPolynomial
import Proof.CaseAnalysis.RowsSourceLoad
import Proof.CaseAnalysis.RowsPacketPolynomial
import Proof.CaseAnalysis.RowsPacketOptional
import Proof.CaseAnalysis.RowsFamilyLoop
import Proof.MachineModel.ClosureRadixCoordinate
import Proof.MachineModel.ClosureMaskDegree

/-! A whole selected tuple now reaches the complete common-width equation
emitter through shared physical occurrence/count tapes. The ordered native
positions come from executed cache lookups, including all repetitions. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleCommonEquation
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def one (N : ℕ) (bits : List Bool) : List (Fin N) :=
  if h : bits.length≤N then RowMaskMeaning.typed N 0 bits (by omega) else []

def tupleSlots : Fin 14→Fin 48 := ![36,37,23,24,38,39,40,41,42,43,44,45,46,47]
def rowSlots (i : Fin 36) : Fin 48 := i.castAdd 12
noncomputable def first := RecoveryFocus.machine tupleSlots RowTupleMaskReady.machine
noncomputable def last := RecoveryFocus.machine rowSlots P1CompactRowCommonCoordinateLoop.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.P1CompactRowTupleCommonEquation

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! The tuple equation caller accepts the binary frame emitted by the
actual enumerator. Its time is bounded using source dimensions and tuple
degree, without a separate supplied selected-occurrence count. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleEquationBounds
open LocalBitMultitape RepairRepresentation SignedSortKey P1CompactRowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactRowTupleEquationBounds

/-! The complete equation emitter accepts any sufficiently large fixed
allocation. One source-size allocation can therefore serve every selected
tuple; its size need not depend on the runtime selected-occurrence count. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonFixedCapacity
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactRowCommonFixedCapacity

/-! The actual tuple-to-equation caller uses one common width and one
source-sized allocation for every tuple up to degree Q. Per-tuple width and
allocation conditions are discharged by the computed occurrence-count bound. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleFixedCapacity
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q : ℕ) :=
  P1Radix.bits gs*(P1Radix.effectiveDegree gs*Q)

end NearCubicWires.RepairOrdinary.P1CompactRowTupleFixedCapacity

/-! The complete equation body consumes one tuple at its retained stream
cursor. Its exact final configuration exposes the ports needed to clear
only the per-tuple data before the next selected tuple. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleCursorEquation
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := RecoveryFocus.machine tupleSlots RowTupleCursorReady.machine
noncomputable def last := RecoveryFocus.machine rowSlots P1CompactRowCommonCoordinateLoop.machine
noncomputable def machine := Composition.machine first last


end NearCubicWires.RepairOrdinary.P1CompactRowTupleCursorEquation

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! The whole tuple-to-equation machine starts with blank scratch and
recording tapes. Zero-padding transport removes the earlier supplied false
allocations without changing the machine, actual data, or execution time. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleBlank
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactRowTupleBlank

/-! The exact reusable tuple-store layout: only the coordinate counter,
occurrence stream and count need erasure between adjacent tuples. The
cached last lookup bound remains available and is overwritten by the next
digit read. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleCursorLayout
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation RowMaskPositionParts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactRowTupleCursorLayout

/-! The three changing tuple fields fit the same actual source-derived
allocation already used by the equation consumer. This pays their physical
erasure without another runtime capacity. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleResetBounds
open RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactRowTupleResetBounds

/-! A reusable whole-tuple body: the actual selected digits produce the
common-width equation, then paid erasure restores all per-tuple fields.
The stream cursor advances and the equation append cursor stays live. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleCursorBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine P1CompactRowTupleCursorEquation.machine RowTupleCursorErase.machine

end NearCubicWires.RepairOrdinary.P1CompactRowTupleCursorBody

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! One actual enumerated frame executes through the complete reusable
equation body and its paid three-cell trailer. The next cursor is exactly
the end of that frame, including the zero-degree case. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleFramedBody
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine P1CompactRowTupleCursorBody.machine RowTupleFrame.skip

end NearCubicWires.RepairOrdinary.P1CompactRowTupleFramedBody

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! Execute every actual selected tuple frame, without a supplied unary
frame count. The physical stream marker controls entry and termination;
all equations append in the enumerator's exact occurrence order. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleList
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactRowTupleList

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! The complete equation list consumes the actual checked enumeration
order. Width and validity of every tuple are discharged from the filter;
no selected tuple list or occurrence multiplicity is changed. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleSelectedList
open LocalBitMultitape RepairRepresentation
open RowTupleSubsets RowTupleDigits P1CompactRowTupleList
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactRowTupleSelectedList

/-! The actual binary producer, paid output rewind, and complete selected
list consumer share one tuple tape. No tuple bytes or unary tuple count
are supplied at input. Native cache and common metadata remain retained. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleEnumeratedEquations
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true




end NearCubicWires.RepairOrdinary.P1CompactRowTupleEnumeratedEquations

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! The actual tuple consumer emits the complete signed cut: all equation
coordinates, its threshold, then the cached binLift coefficient. The cache
is retained at head zero while the row append cursor stays live. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleCutBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 1 P1CompactRowTupleFramedBody.machine
noncomputable def machine := Composition.machine first RowTupleCutAppend.machine


end NearCubicWires.RepairOrdinary.P1CompactRowTupleCutBody

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! The actual selected tuple stream emits every complete signed cut,
reusing one cached coefficient and retaining the whole-row append cursor. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleCutList
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := StreamController.machine P1CompactRowTupleCutBody.machine 44

end NearCubicWires.RepairOrdinary.P1CompactRowTupleCutList

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! The actual binary subset producer hands its rewound tuple stream to the
complete signed-cut consumer. One coefficient is retained for the whole
degree; coordinates and threshold are followed by that coefficient. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsEnumeratedCuts
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def enumSlots : Fin 41 → Fin 89 :=
  ![49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,44,66,67,68,
    69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88]
def rowSlots (i : Fin 49) : Fin 89 := i.castAdd 40
noncomputable def first := RecoveryFocus.machine enumSlots RowTupleEnumerationReady.machine
noncomputable def last := RecoveryFocus.machine rowSlots P1CompactRowTupleCutList.machine
noncomputable def machine := Composition.machine first last


end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsEnumeratedCuts

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! A complete fixed-degree row call starts with a blank coefficient cache.
Unary j and p produce (-2)^j once, then the actual positional enumeration
and signed-cut writer run at their retained native cache and output cursors. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsComputedCuts
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficientSlots (i : Fin 14) : Fin 103 :=
  if i.val=12 then 48 else i.natAdd 89

noncomputable def first := RecoveryFocus.machine coefficientSlots CloseoutRowsDegreeCoefficient.machine
noncomputable def last := TapeEmbedding.machine 14 P1CompactCloseoutRowsEnumeratedCuts.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsComputedCuts

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! The fixed-degree call executes one recorded rewind of its reusable
work tapes. Its append cursor is excluded. The coarse capacity concerns
only those work tapes, so accumulated row output never enters this charge. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeReset
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open CloseoutRowsDegreeReset

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeReset

/-! The native cache fixes the actual common coordinate width. Incidence
lists retain every monomial occurrence, including empty monomials. Native
coordinate order is exactly the signed cut order consumed by the row printer. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsCacheInput
open RepairRepresentation SupplierPipeline SupplierPrime SupplierEstimator ThresholdCompiler
open MatrixScoreBatch RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coordinates {l r : ℕ} (e : LabelledEquation (Fin (l+r))) : Equation l r :=
  ⟨Sum.elim (fun i => e.weights (i.castAdd r)) (fun i => e.weights (i.natAdd l)),e.target⟩

theorem coordinates_magnitude {l r : ℕ} (e : LabelledEquation (Fin (l+r))) :
    equationMagnitudeBound (coordinates e)=equationMagnitudeBound e := by
  simp [coordinates,equationMagnitudeBound,Fintype.sum_sum_type,Fin.sum_univ_add]

def monomial {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (bits : List Bool) :=
  (P1CompactRowCachedEquation.equations gs (P1CompactRowTupleCommonEquation.one gs.length bits)).map coordinates
def polynomial {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (rows : List (List Bool)) :=
  rows.map (monomial gs)
def family {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (bank : List (List (List Bool))) :=
  bank.map (polynomial gs)

theorem one_length (N : ℕ) (bits : List Bool) :
    (P1CompactRowTupleCommonEquation.one N bits).length≤N := by
  unfold P1CompactRowTupleCommonEquation.one
  split_ifs with h
  · exact (RowMaskMeaning.typed_le N 0 bits (by omega)).trans h
  · simp

theorem monomial_length {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (bits : List Bool) :
    (monomial gs bits).length≤gs.length := by
  simpa only [monomial,P1CompactRowCachedEquation.equations,List.length_map] using one_length gs.length bits

theorem monomial_fit {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (bits : List Bool)
    (e : Equation l r) (he : e∈monomial gs bits) :
    equationMagnitudeBound e<2^(P1Radix.bits gs) := by
  obtain ⟨native,hn,rfl⟩ := List.mem_map.mp he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hn
  rw [coordinates_magnitude]
  exact P1CompactRowCachedEquation.cache_radix_safe gs i

theorem family_lengths {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (bank : List (List (List Bool))) (ms : List (List (Equation l r)))
    (hm : ms∈family gs bank) (m : List (Equation l r)) (hmem : m∈ms) : m.length≤gs.length := by
  obtain ⟨rows,_,rfl⟩ := List.mem_map.mp hm
  obtain ⟨bits,_,rfl⟩ := List.mem_map.mp hmem
  exact monomial_length gs bits

theorem family_fit {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (bank : List (List (List Bool))) (ms : List (List (Equation l r)))
    (hm : ms∈family gs bank) (e : Equation l r) (he : e∈ms.flatten) :
    equationMagnitudeBound e<2^(P1Radix.bits gs) := by
  obtain ⟨rows,_,rfl⟩ := List.mem_map.mp hm
  obtain ⟨m,hm,he⟩ := List.mem_flatten.mp he
  obtain ⟨bits,_,rfl⟩ := List.mem_map.mp hm
  exact monomial_fit gs bits e he

def input (s Q : ℕ) (gs : List (ExactThresholdGate ((s+1)/2+s/2))) [_radix : P1Radix gs]
    (bank : List (List (List Bool))) (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (family gs bank)).length^100≤2^s) : EquationRow.Input :=
  CloseoutRows.commonInput s (P1Radix.bits gs) gs.length Q (family gs bank)
    hs hg (family_lengths gs bank) (family_fit gs bank)

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsCacheInput

/-! The actual tuple-cut bytes are precisely the common-width row's cuts.
All degree and monomial occurrences remain in their enumerated order. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsCutMeaning
open RepairRepresentation SupplierPipeline MatrixScoreBatch RowBinLift
open P1CompactCloseoutRowsCacheInput
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def degreeCuts {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (w j : ℕ) (rows : List (List Bool)) : List Cut :=
  (RowTupleSubsets.selected w rows.length (j+1)).map fun ds =>
    split ((-2 : ℤ)^j) (RowPowerBinLift.stack (P1Radix.bits gs)
      (RowTupleTerms.selectedMonomials (polynomial gs rows) ds).flatten)

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsCutMeaning

/-! Actual fixed-degree cut production followed by paid scratch reuse.
The native cache and the row append cursor survive; the next call reloads
only degree metadata into the erased work bank. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsReusableCuts
open LocalBitMultitape RecoveryExecution CloseoutRowsDegreeReset P1CompactCloseoutRowsDegreeReset
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := CloseoutRowsDegreeClean.machine P1CompactCloseoutRowsComputedCuts.machine

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsReusableCuts

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! One exact boundary for the degree loop: native row context, 57 work
tapes, the retained C driver/logs, and six short templates. The worker
receipt describes every physical head and tape needed by its next call. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsLoopLayout
open LocalBitMultitape RecoveryExecution CloseoutRowsDegreeReset P1CompactCloseoutRowsDegreeReset
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def worker := TapeEmbedding.machine 6 P1CompactCloseoutRowsReusableCuts.machine

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsLoopLayout

/-! The accepted degree pass, four small updates and six metadata copies
return exactly the next pass's boundary, including the append cursor. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsLoopBoundary
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout CloseoutRowsDegreeReset P1CompactCloseoutRowsDegreeReset
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsLoopBoundary

/-! The full next-call identity and actual metadata inputs at the shared
degree boundary. Every source and cursor is inherited from one receipt. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsLoopInterface
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsLoopBoundary CloseoutRowsDegreeReset P1CompactCloseoutRowsDegreeReset
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsLoopInterface

/-! One executed degree transition: print and clean the positional cuts,
advance the retained counters, and reload six short templates. The joined
receipt has exactly the next degree's entry configuration. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeBody
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsLoopBoundary P1CompactCloseoutRowsLoopInterface
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first {s : ℕ} (callee : Machine 112 s) :=
  Composition.machine callee CloseoutRowsDegreeNext.machine
noncomputable def machine {s : ℕ} (callee : Machine 112 s) :=
  Composition.machine (first callee) CloseoutRowsMetadataReload.machine

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeBody

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! The literal Q driver executes only the required degree transitions.
Exhaustion includes its physical rewind; no body call at degree Q is
assumed. The growing cut pre is retained throughout the loop. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeLoop
open LocalBitMultitape RecoveryExecution P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsLoopBoundary
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine {t s : ℕ} (body : Machine t s) := RepeatMachine.machine body (fun _ _=>true)

def budget (Q C : ℕ) := Q*(40*C+103)+3

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeLoop

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! The physical degree loop may use its existing Q driver. Degrees above
the actual monomial count emit no positional subset, so no extra physical
min(Q,M) controller is needed and the exact cut list is unchanged. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeRange
open MatrixScoreBatch P1CompactCloseoutRowsCutMeaning P1CompactCloseoutRowsCacheInput
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem selected_nil (w M j : ℕ) (hw : M≤2^w) (hj : M≤j) :
    RowTupleSubsets.selected w M (j+1)=[] := by
  have h := RowTupleSubsets.selected_perm w M (j+1) hw
  have hb : (List.range M).length<j+1 := by simp; omega
  rw [List.sublistsLen_of_length_lt hb] at h
  exact List.perm_nil.mp h

theorem degree_nil {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (w j : ℕ) (rows : List (List Bool)) (hw : rows.length≤2^w) (hj : rows.length≤j) :
    degreeCuts gs w j rows=[] := by
  simp only [degreeCuts,selected_nil w rows.length j hw hj,List.map_nil]

theorem all_degrees {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (Q w : ℕ) (rows : List (List Bool)) (hw : rows.length≤2^w) :
    (List.range Q).flatMap (fun j=>degreeCuts gs w j rows)=
      (List.range (min Q rows.length)).flatMap (fun j=>degreeCuts gs w j rows) := by
  by_cases hQ : Q≤rows.length
  · rw [Nat.min_eq_left hQ]
  · have hM : rows.length≤Q := by omega
    rw [Nat.min_eq_right hM]
    clear hQ
    induction Q,hM using Nat.le_induction with
    | base => rfl
    | succ Q hQ ih =>
      simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,degree_nil gs w Q rows hw hQ,ih]

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeRange

/-! The executed degree loop prints exactly one polynomial's complete
signed-cut word, in the permitted positional order and with every duplicate
monomial occurrence retained. Its output cursor remains at the append end. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPolynomial
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsLoopBoundary
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body := P1CompactCloseoutRowsDegreeBody.machine worker
noncomputable def machine := P1CompactCloseoutRowsDegreeLoop.machine body

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPolynomial

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! One shared digit width may serve an entire live-family bank. Changing
the binary enumeration width only permutes positional subsets; no repeated
monomial or cut is removed and the matrix coordinate width is unchanged. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSharedDigits
open P1CompactCloseoutRowsCutMeaning P1CompactCloseoutRowsCacheInput MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cuts {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (Q w : ℕ) (rows : List (List Bool)) :=
  (List.range Q).flatMap (fun j=>degreeCuts gs w j rows)

theorem degree_perm {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (w j : ℕ) (rows : List (List Bool)) (hw : rows.length≤2^w) :
    (degreeCuts gs w j rows).Perm
      (degreeCuts gs (RowTupleSubsets.digitWidth rows.length) j rows) := by
  exact ((RowTupleSubsets.selected_perm w rows.length (j+1) hw).trans
    (RowTupleSubsets.chosen_perm rows.length (j+1)).symm).map _

theorem canonical_cuts {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (Q : ℕ) (rows : List (List Bool)) :
    cuts gs Q (RowTupleSubsets.digitWidth rows.length) rows=
      CloseoutRows.orderedCuts (P1Radix.bits gs) Q (polynomial gs rows) := by
  rw [cuts,P1CompactCloseoutRowsDegreeRange.all_degrees gs Q _ rows (RowTupleSubsets.digit_fit rows.length).le]
  simp only [CloseoutRows.orderedCuts,RowTupleTerms.terms,polynomial,List.length_map,
    List.map_flatMap,List.map_map,Function.comp_def,degreeCuts]

theorem cuts_perm {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (Q w : ℕ) (rows : List (List Bool)) (hw : rows.length≤2^w) :
    (cuts gs Q w rows).Perm
      (CloseoutRows.orderedCuts (P1Radix.bits gs) Q (polynomial gs rows)) := by
  rw [←canonical_cuts gs Q rows]
  apply List.Perm.flatMap_left
  intro j _
  exact degree_perm gs w j rows hw

theorem batch_perm {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (Q w : ℕ) (bank : List (List (List Bool))) (hw : ∀ rows∈bank,rows.length≤2^w) :
    (bank.flatMap (cuts gs Q w)).Perm
      (RowPowerBinLift.batch (P1Radix.bits gs) Q (family gs bank)) := by
  have hp : (bank.flatMap (cuts gs Q w)).Perm
      (bank.flatMap (fun rows=>CloseoutRows.orderedCuts (P1Radix.bits gs) Q (polynomial gs rows))) := by
    apply List.Perm.flatMap_left
    intro rows hr
    exact cuts_perm gs Q w rows (hw rows hr)
  exact hp.trans (by simpa only [CloseoutRows.orderedBatch,family,List.flatMap_map] using
    CloseoutRows.ordered_batch_perm (P1Radix.bits gs) Q (family gs bank))

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSharedDigits

/-! The shared digit-width family inhabits the literal row input and
count-table premises. The cache width, single successor widening, scalar
width and complete matrix dimensions are inherited without alteration. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSharedInput
open MatrixScoreBatch P1CompactCloseoutRowsCacheInput P1CompactCloseoutRowsSharedDigits
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSharedInput

/-! Coarse preparation bounds for the actual positional enumerator and
cut consumer. Only the digit exponent contains the monomial population;
native cache and matrix widths occur polynomially outside that exponent. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scale (n p F w N Q : ℕ) := n+p+F+w+N+Q+1
def capacity (n p F w N Q : ℕ) :=
  4096*(scale n p F w N Q)^4*2^(w*(Q+1))

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparationBounds

/-! One concrete preparation capacity covers every degree of every
polynomial whose monomial count fits the shared digit width. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparationFits
open P1CompactCloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparationFits

/-! The concrete shared preparation capacity discharges the actual native
metadata and every selected initial work-tape extent. The growing output
prefix is absent from all of these bounds. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparationInput
open P1CompactCloseoutRowsPreparationBounds P1CompactCloseoutRowsPreparationFits
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparationInput

/-! The complete polynomial program starts its added scratch suffixes
blank. Reverse zero-padding simulation preserves every transition and the
actual output bytes. Only the true C driver remains a required native field. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsColdScratch
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsColdScratch

/-! One whole polynomial executes at the actual common preparation capacity.
All degree, scratch, cursor and metadata inequalities are discharged here.
The enclosing bank still supplies the native source data and true C driver. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparedPolynomial
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsLoopBoundary
open P1CompactCloseoutRowsPreparationBounds P1CompactCloseoutRowsPreparationFits P1CompactCloseoutRowsPreparationInput
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparedPolynomial

/-! The enclosing family controller has one fixed head pattern and one
common native-port extent. Neither contains the accumulated cut prefix. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsBankFields
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsPreparationBounds
open P1CompactCloseoutRowsPreparationFits P1CompactCloseoutRowsPreparationInput
open RepairSource.VerifierDecoding RepairRepresentation RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsBankFields

/-! One common C bounds every native port at both ends of a polynomial.
The global append output is excluded, and the erase log has exactly C+1 cells. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsBankCapacity
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsPreparationBounds
open P1CompactCloseoutRowsPreparationFits P1CompactCloseoutRowsPreparationInput P1CompactCloseoutRowsBankFields
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsBankCapacity

/-! A complete polynomial call returns to the enclosing bank's erased
native ports. Every transition and sweep is paid; the growing output stays live. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsBankPolynomial
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsLoopBoundary
open P1CompactCloseoutRowsPreparationBounds P1CompactCloseoutRowsPreparationFits P1CompactCloseoutRowsPreparationInput
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine P1CompactCloseoutRowsPolynomial.machine CloseoutRowsBankClear.machine
def budget (Q C : ℕ) := P1CompactCloseoutRowsDegreeLoop.budget Q C+1+CloseoutRowsBankClear.budget C

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsBankPolynomial

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! The same paper load pays the generated cut family and all executed
BinLift driver/degree/clear costs plus the fixed110-port loading allowance.
This cost is added to table work; it is not internal-syntax Tprep. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSourceLoad
open CloseoutRowsSourceDigits P1CompactCloseoutRowsCacheInput
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSourceLoad

/-! One actual packet load, head positioning, complete polynomial call and
native clear compose into the reusable enclosing bank body. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPacketPolynomial
open LocalBitMultitape P1CompactCloseoutRowsPreparationBounds CloseoutRowsBankPacket
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true



end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPacketPolynomial

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! Native packets depend only on their source polynomial and fixed row
metadata. The accumulated cut output is absent from every packet field. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPacketIndependent
open P1CompactCloseoutRowsPacketPolynomial CloseoutRowsBankPacket CloseoutRowsBankPorts
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPacketIndependent

/-! One enclosing polynomial packet, including the physical zero-monomial
skip, has a uniform receipt for the outer live-family loop. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPacketOptional
open LocalBitMultitape CloseoutRowsBankPacket P1CompactCloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPacketOptional

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! The actual outer family loop consumes every polynomial packet once,
including empty polynomials, and rewinds its literal family driver. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsFamilyLoop
open LocalBitMultitape CloseoutRowsBankPacket P1CompactCloseoutRowsPreparationBounds
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsFamilyLoop

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

