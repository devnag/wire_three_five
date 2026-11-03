import Proof.Packets.PacketsMetaProgram

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsMeta
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator
open NearCubicWires.PacketsMeta.CutoffMath
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJd4d1d9d7d1fa4313_Production
noncomputable section

namespace Spec
open Lev Setup Tail Prog

/-- The circuit data of a THR request. -/
def dsOf (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit) : List CD :=
  r.circuits.map (fun c => (⟨c.top.support.card, ThresholdRows.children a c⟩ : CD))

theorem tw_eq (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) :
    twOf (dsOf a r) = Request.topWord a (.thr r four L target) := by
  rw [topWord_thr]
  simp [twOf, dsOf, List.flatMap_map, pay]

theorem tab_eq (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (c : Fin 4) : tab (dOf (dsOf a r) c) = T a r c.val := by
  by_cases hc : c.val < r.circuits.length
  · have hc' : c.val < (dsOf a r).length := by simp [dsOf, hc]
    have hg : (dsOf a r)[c.val]'hc' = (⟨(r.circuits[c.val]'hc).top.support.card,
        ThresholdRows.children a (r.circuits[c.val]'hc)⟩ : CD) := by
      simp [dsOf]
    rw [dOf_lt _ c hc', hg]
    simp only [T, tables, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp [hc]), List.getElem?_map, List.getElem?_eq_getElem hc]
    rfl
  · have hc' : (dsOf a r).length ≤ c.val := by simp [dsOf]; omega
    rw [dOf_ge _ c hc', tab_pad]
    simp only [T, tables, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map]
    rw [List.getElem?_replicate]
    have : c.val - r.circuits.length < 4 - r.circuits.length := by omega
    simp [this]

theorem Fv_eq (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) : Fv (dsOf a r) = familyMagnitudeBound (ThresholdRows.equation a r) := by
  rw [family_eq a r four]
  unfold Fv
  rw [tab_eq a r four 0, tab_eq a r four 1, tab_eq a r four 2, tab_eq a r four 3]
  rfl

theorem Cv_eq (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) : Cv (dsOf a r) = Fintype.card (ThresholdRows.Selection a r) := by
  rw [card_eq a r four]
  unfold Cv
  rw [tab_eq a r four 0, tab_eq a r four 1, tab_eq a r four 2, tab_eq a r four 3]
  show (T a r 0).length * ((T a r 1).length * ((T a r 2).length * ((T a r 3).length * 1))) = _
  ring

theorem cut_eq (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (target : ℕ) :
    cutOf (Fv (dsOf a r)) (Cv (dsOf a r)) target = CloseoutFinalC10ThresholdRows.primeCutoff a r target := by
  rw [Fv_eq a r four, Cv_eq a r four]
  unfold cutOf CloseoutFinalC10ThresholdRows.primeCutoff CloseoutFinalC10ThresholdRows.primeDenominator
    reciprocalUnionDenominator familyMagnitudeExponent
  rfl

end Spec

end
end NearCubicWires.PacketsMeta

