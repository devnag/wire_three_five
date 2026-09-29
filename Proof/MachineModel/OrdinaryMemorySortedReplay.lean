import Proof.MachineModel.OrdinaryMemorySort

/-! The actual encoded sorter supplies the chronological-subsequence premise
of the computation-log memory checker. This is a bounded semantic/runtime
application, not the complete fixed universal verifier. -/
namespace NearCubicWires.RepairOrdinary.MemorySort
open LocalBitMultitape StablePartition MemoryLog
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cell_subsequence {N : ℕ} (I K W : ℕ) (events : Fin N → Event)
    (hN : N ≤ 2^I) (hcells : ∀ i, cellCode W (events i).cell < 2^K) (cell : Cell) :
    atCell cell ((sortedIndices I K W events).map events) =
      atCell cell ((List.finRange N).map events) := by
  let p : Fin N → Bool := fun i => (events i).cell == cell
  have hp := (sorted_perm I K W events hN).filter p
  have hs := (same_cell_order I K W events hN hcells).filter p
  have hsorted : ((sortedIndices I K W events).filter p).Pairwise (fun i j => i ≤ j) := by
    apply hs.imp_of_mem
    intro i j hi hj hij
    have hei : (events i).cell = cell := by simpa [p] using (List.mem_filter.mp hi).2
    have hej : (events j).cell = cell := by simpa [p] using (List.mem_filter.mp hj).2
    exact hij (hei.trans hej.symm)
  have hbase : (List.finRange N).Pairwise (fun i j => i ≤ j) := by
    rw [← List.ofFn_id, List.pairwise_ofFn]
    intro i j hij
    exact hij.le
  have he := hp.eq_of_pairwise' hsorted (hbase.filter p)
  simpa only [atCell, List.filter_map, Function.comp_def, p] using congrArg (List.map events) he

end NearCubicWires.RepairOrdinary.MemorySort
