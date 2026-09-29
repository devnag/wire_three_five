import Proof.CaseAnalysis.RowsSupportLoop
import Proof.CaseAnalysis.RowsCircuitBottomMeaning

/-! The retained support stream has exactly the native stream's original
carrier order, including declared zero-weight incidences and THR selection. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
open LocalBitMultitape CanonicalWitnessCodec SupplierPipeline RadixSemantics
open CloseoutRowsGateSupport CloseoutRowsCircuitBottomLoop CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def supportWord {q : ℕ} (gates : List (SupportedNormalizedGate q)):=
  gates.flatMap (fun g=>frame (gateMembers g.support))

theorem support_symmetric {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core)
    (words : List (List Bool)) (membership : List Bool) (memberPos : ℕ)
    (hd : ∀ i,decodeSupportedNormalizedGate core (value (words.getD i.val []))=some (c.bottom i)) :
    (List.range c.bottomCount).flatMap (supportOutput false core memberPos membership words)=
      supportWord (List.ofFn c.bottom) := by
  rw [output_fin]
  simp only [supportWord,List.ofFn_eq_map,List.flatMap_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i _
  simp only [supportOutput,supportEmitted,hd i]
  simp [choose,kept]

theorem support_threshold {core : ℕ} (c : NormalizedThresholdThresholdCircuit core)
    (words : List (List Bool))
    (hd : ∀ i,decodeSupportedNormalizedGate core (value (words.getD i.val []))=some (c.bottom i)) :
    (List.range c.bottomCount).flatMap (supportOutput true core 1 (frame (gateMembers c.top.support)) words)=
      supportWord (List.ofFn (fun i=>c.bottom (retainedTopIndex c i))) := by
  rw [output_fin]
  have he:(List.finRange c.bottomCount).flatMap
      (fun i=>supportOutput true core 1 (frame (gateMembers c.top.support)) words i.val)=
      (List.finRange c.bottomCount).flatMap
        (fun i=>CloseoutRowsGateSupport.selected true (decide (i∈c.top.support))
          (frame (gateMembers (c.bottom i).support))):=by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i _
    simp only [supportOutput,supportEmitted,hd i,choose_members]
    cases decide (i∈c.top.support) <;> simp [CloseoutRowsGateSupport.selected,keep,PCPPQueryField.selected]
  rw [he,selected_filter,sorted_members,←Finset.listMap_orderEmbOfFin_finRange c.top.support rfl]
  simp only [supportWord,List.flatMap_map,List.ofFn_eq_map,retainedTopIndex]

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
