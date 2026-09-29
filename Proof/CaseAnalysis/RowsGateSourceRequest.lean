import Proof.CaseAnalysis.RawRowsChildLog
import Proof.CaseAnalysis.RowsGateSourceCalls

/-! The retained-top formula depends only on its supported gate. This
local abbreviation lets the all-raw source caller handle every accepted
gate; on an actual top it is definitionally the original retainedTopGate. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateSource
open LocalBitMultitape RepairRepresentation ExecutableInterfaces CanonicalBinary CanonicalWitnessCodec
open SupplierPipeline RadixSemantics CompilerSemantics CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def compressedGate {n : ℕ} (g : SupportedNormalizedGate n) : NormalizedThresholdGate g.support.card where
  weight i := g.gate.weight (g.support.orderEmbOfFin rfl i)
  threshold := g.gate.threshold
def request {n : ℕ} (compressed : Bool) (g : SupportedNormalizedGate n) : ExactDecompositionRequest :=
  if compressed then ⟨g.support.card,nonStrictAsStrict (compressedGate g)⟩ else ⟨n,nonStrictAsStrict g.gate⟩

theorem compressed_weights {n : ℕ} (g : SupportedNormalizedGate n) :
    CloseoutRowsGateNative.weights true (gateFields g.gate) (gateMembers g.support)=
      (List.ofFn (compressedGate g).weight).flatMap intWord := by
  unfold CloseoutRowsGateNative.weights
  rw [show (gateFields g.gate).length=n by simp [gateFields],gate_emission,selected_filter,sorted_members]
  rw [←Finset.listMap_orderEmbOfFin_finRange g.support rfl]
  simp only [List.flatMap_map,List.ofFn_eq_map,compressedGate]

theorem request_word {n : ℕ} (compressed : Bool) (g : SupportedNormalizedGate n) (source : List Bool)
    (hs : readTapeBit source 1=decide (g.gate.threshold<0)) :
    CloseoutRowsGateNative.word compressed (gateFields g.gate) (gateMembers g.support) source g.gate.threshold.natAbs=
      thresholdWord (request compressed g).gate := by
  cases compressed with
  | false => exact CloseoutRowsGateNative.ordinary_word g source hs
  | true =>
    change natWord (CloseoutRowsSupportCount.ones (gateMembers g.support))++
      CloseoutRowsGateNative.weights true (gateFields g.gate) (gateMembers g.support)++
      CloseoutRowsStrictNative.produced source g.gate.threshold.natAbs=_
    rw [CloseoutRowsSupportCount.support_card,compressed_weights,
      CloseoutRowsStrictNative.produced_eq source g.gate.threshold hs]
    rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsGateSource
