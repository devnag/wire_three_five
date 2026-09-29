import Proof.MachineModel.OrdinaryKeyPrefix

/-! Reused prefix-copy workspace and its literal annotated occurrence-id
application. The final configuration restores all bounded local heads. -/
namespace NearCubicWires.RepairOrdinary.KeyPrefix
open LocalBitMultitape Streaming SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ready {s : ℕ} (state : Fin s) (source template out : List Bool) (capacity : ℕ) : Configuration 4 s :=
  ⟨state, ![0, 0, out.length, 0], ![source, template, out, List.replicate capacity false]⟩
def capacities (capacity : ℕ) : Fin 4 → ℕ := ![0, 0, 0, capacity]

theorem field_run (bits suffix templateBits out : List Bool) (capacity : ℕ)
    (hwidth : bits.length = templateBits.length) (hcap : 2 * bits.length ≤ capacity) :
    ∃ r : ExecutionReceipt 4 4,
      runFrom machine (4 * bits.length + 2)
        (ready 0 (marks bits ++ suffix) (frame templateBits) out capacity) = some r ∧
      r.final = ready 3 (marks bits ++ suffix) (frame templateBits) (out ++ marks bits) capacity ∧
      r.steps = 4 * bits.length + 2 ∧
      r.peakTapeCells ≤ (marks bits ++ suffix).length + (frame templateBits).length +
        out.length + 4 * bits.length + capacity := by
  obtain ⟨base, hr, hf, hs, hp⟩ := copy_run bits suffix templateBits out hwidth
  obtain ⟨r, hrun, hfinal, hsteps, hpeak⟩ := ZeroPadding.run_config machine (capacities capacity) _ _ base hr
  have hi : ZeroPadding.config (capacities capacity)
      (scan 0 (marks bits ++ suffix) (frame templateBits) 0 out) =
      ready 0 (marks bits ++ suffix) (frame templateBits) out capacity := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config, ZeroPadding.pad, capacities, scan, ready]
  refine ⟨r, by rw [hi] at hrun; exact hrun, ?_, hsteps.trans hs, ?_⟩
  · rw [hfinal, hf]
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, ZeroPadding.pad, capacities, reset, ready]
      omega
  · have hc : ZeroPadding.cells (capacities capacity) = capacity := by
      simp [ZeroPadding.cells, capacities, Fin.sum_univ_succ]
    rw [hc] at hpeak
    omega

end NearCubicWires.RepairOrdinary.KeyPrefix
