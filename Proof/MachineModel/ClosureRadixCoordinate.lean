import Proof.MachineModel.ClosureRadix

/-! The fixed ordinary loop consumes an ordered list of actual cached-child
occurrences and assembles one signed coefficient. Indices are never deduplicated.
The physical counter and every call/return/rewind are included in the run. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowOccurrenceLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RepeatMachine.machine RowOccurrenceReusable.machine (fun _ _=>true)

end NearCubicWires.RepairOrdinary.P1CompactRowOccurrenceLoop

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! Physical output and uniform cost of one completed occurrence-coordinate
loop. The two produced frames denote the signed Horner coefficient. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowOccurrenceLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactRowOccurrenceLoop

/-! The executed occurrence-coordinate loop assembles the power-radix stack
of actual native child equations. The radix is safe by their native bytes;
only the conjunction is identified with the canonical equation stack. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCachedEquation
open LocalBitMultitape RepairRepresentation SupplierPipeline SupplierPrime SupplierEstimator ThresholdCompiler
open P1CompactRowOccurrenceLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def equation {n : ℕ} (g : ExactThresholdGate n) : LabelledEquation (Fin n) := ⟨g.weight,g.target⟩
def equations {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length)) :=
  indices.map (fun i=>equation gs[i.val])

theorem cache_radix_safe {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (i : Fin gs.length) :
    equationMagnitudeBound (equation gs[i.val])<2^(P1Radix.bits gs) := P1Radix.safe i

end NearCubicWires.RepairOrdinary.P1CompactRowCachedEquation

/-! Execute the complete occurrence loop and physically rewind just its two
coefficient heads. The cache, index-stream cursor and loop counter survive;
the paid rewind log supplies real allocated normalization workspace. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientLoopReset
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 25) : Bool := decide (i=10 ∨ i=11)
noncomputable def machine := MaskedReset.machine P1CompactRowOccurrenceLoop.machine selected

end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientLoopReset

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! The actual loop endpoint supplies the seven normalization tapes. The
same normalizer accepts the physically retained zero padding in its flag
and magnitude slots; only its two output tapes are fresh. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientDock
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 7 → Fin 28 := ![10,11,19,16,25,26,27]

end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientDock

/-! One fixed ordinary program consumes the retained cache and the actual
ordered occurrence stream, computes one stacked coefficient, physically
rewinds its P/N words, and emits its final normalized signed field. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientWhole
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding P1CompactRowCoefficientDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 2 P1CompactRowCoefficientLoopReset.machine
noncomputable def last := RecoveryFocus.machine slots RowCoefficientField.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientWhole

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! Whole retained-cache coefficient computation followed by its physical
append to the live row stream. The field and its emitter log are reused by
the cursor-restoring copier; the row-output head remains advanced. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientStream
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientStream

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! Restore the dedicated occurrence-stream cursor after a coefficient
append, with paid recording and retained scratch padding for the next call.
The global row-output cursor is deliberately preserved by this machine. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientStreamReset
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientStreamReset

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! Whole coefficient append with a physical erase of all coefficient work.
The native cache, width/arity drivers, occurrence list and row output survive.
The same retained allocation can be used by subsequent coordinate calls. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientStreamClear
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientStreamClear

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! Exact same-bank endpoint for one coefficient. Rewinding and erasure
restore the original allocated entry, with only the row stream extended. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientReusable
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientReusable

/-! One uniform local coefficient workspace and budget, derived from actual
cache bytes, native arity, cached child count and ordered occurrence count.
This removes the local capacity premise; cold driver production is separate. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientBounds
open LocalBitMultitape RepairRepresentation Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientBounds

/-! One actual coordinate-loop body computes and appends the stacked field,
restores its coefficient bank, then advances its own coordinate template.
All values used by the next call are physically present in the same bank. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoordinateBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactRowCoordinateBody

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! A literal native-arity driver executes all weight coordinates and the
target. Each body restores its coefficient bank and increments its actual
coordinate template. The resulting row is an ordered stream of fields. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoordinateLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactRowCoordinateLoop

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! The actual coordinate stream is the weight-and-target encoding of the
power-radix stack. The canonical radix is related only by its conjunction. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoordinateLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open SupplierPipeline SupplierPrime SupplierEstimator ThresholdCompiler
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.P1CompactRowCoordinateLoop

/-! The native occurrence coefficient is normalized once, widened directly
to the common cut width, and physically appended. No canonical-radix
coefficient equality or implicit change of the emitted width is used. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonCoefficient
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fieldSlots : Fin 5→Fin 32 := ![26,28,29,30,31]
noncomputable def first := TapeEmbedding.machine 4 P1CompactRowCoefficientWhole.machine
noncomputable def last := RecoveryFocus.machine fieldSlots RowFieldPaddingAppend.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.P1CompactRowCommonCoefficient

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! Restore the dedicated occurrence cursor after the common-width append.
All scratch lengths are bounded using the executed prefix, and the physical
reset log is retained at the same paid allocation for subsequent erasure. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonReset
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 32) := decide (i=23)
noncomputable def machine := MaskedReset.machine P1CompactRowCommonCoefficient.machine selected

end NearCubicWires.RepairOrdinary.P1CompactRowCommonReset

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! Physically erase the common-width coefficient scratch, preserving the
native cache, occurrence stream, dimensions and live cut-output cursor. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonClear
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlots : Fin 10→Fin 35 := ![10,11,16,19,25,26,27,28,30,32]
def eraseSlots : Fin 12→Fin 35 := Fin.addCases (m:=11) (n:=1) (motive:=fun _=>Fin 35)
  (Fin.addCases (m:=10) (n:=1) (motive:=fun _=>Fin 35) workSlots (fun _=>33)) (fun _=>34)
noncomputable def first := TapeEmbedding.machine 2 P1CompactRowCommonReset.machine
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 10)
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.P1CompactRowCommonClear

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! The exact common-width bank is restored after each executed coefficient.
Only the live output contains the appended common-width signed field. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonReusable
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.P1CompactRowCommonReusable

/-! A single explicit allocation pays the common-width coefficient and its
complete physical cleanup. The remaining cold caller must produce these
raw counters; no local capacity inequality survives this endpoint. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonBounds
open LocalBitMultitape RepairRepresentation RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (m p : ℕ) :=
  16384*(m+1)*RowCachedCoordinateBounds.size gs (P1Radix.bits gs)+16*p+64

end NearCubicWires.RepairOrdinary.P1CompactRowCommonBounds

/-! The actual common-width row consumer: append one coefficient at the
shared cut width, restore its bank, and advance the coordinate on tape15. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonCoordinateBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 1→Fin 35 := fun _=>15
noncomputable def increment := RecoveryFocus.machine slots RowCoordinateIncrement.machine
noncomputable def machine := Composition.machine P1CompactRowCommonClear.machine increment

end NearCubicWires.RepairOrdinary.P1CompactRowCommonCoordinateBody

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

/-! All weights and the target are emitted at the one common cut width.
The native arity driver executes the coordinate loop and restores itself. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonCoordinateLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RepeatMachine.machine P1CompactRowCommonCoordinateBody.machine (fun _ _=>true)

end NearCubicWires.RepairOrdinary.P1CompactRowCommonCoordinateLoop

namespace NearCubicWires.RepairOrdinary
end NearCubicWires.RepairOrdinary

