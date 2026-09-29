import Proof.Packets.PacketsGlueMetaMul
import Proof.Packets.PacketsMetaCutoffBounds

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsMeta
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.PacketsMeta.CutoffMath
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJd4d1d9d7d1fa4313_Production
noncomputable section

namespace StageRun
open Lev Setup Tail Prog Spec Bounds

/-! ## From the program's `LRuns` to PG's `Step` -/

theorem init_tr (W : ℕ) (nw tw : List Bool) :
    ∀ i : Fin (3 + 57), TR W (σ0 nw tw i) 0
      (NearCubicWires.PacketsGlue.RequestMeta.scanIn2 57 (RepairOrdinary.frame tw) (RepairOrdinary.frame nw) i) := by
  intro i
  fin_cases i <;>
    simp [TR, σ0, NearCubicWires.PacketsGlue.RequestMeta.scanIn2, rdF, readTapeBit, blank, Ruler.rb] <;> omega

theorem step_of_lruns {s : ℕ} (P : Machine 60 s) (n W : ℕ) (nw tw : List Bool) (v : ℕ)
    (h : LRuns W P n (σ0 nw tw) (outOnly v)) :
    ∃ (H1 : Fin (3 + 57) → ℕ) (A1 : Fin (3 + 57) → List Bool),
      Step P n (fun _ => 0)
        (NearCubicWires.PacketsGlue.RequestMeta.scanIn2 57 (RepairOrdinary.frame tw) (RepairOrdinary.frame nw)) H1 A1 ∧
      A1 ⟨1, by omega⟩ = List.replicate v true := by
  obtain ⟨H1, A1, hs, hA⟩ := h (fun _ => 0) _ (init_tr W nw tw)
  refine ⟨H1, A1, hs, ?_⟩
  have h1 := hA 1
  simp only [outOnly, Function.update_self, TR] at h1
  exact h1.2

/-! ## Width facts for a THR request -/

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)

theorem tab_len (four : r.circuits.length ≤ 4) (L target : ℕ) (i : Fin 4) : (tab (dOf (dsOf a r) i)).length ≤ 2 ^ (twOf (dsOf a r)).length := by
  rw [tab_eq a r four, tw_eq a r four L target]
  have h1 := T_length_le a r four L target i.val
  have h2 := Nat.lt_two_pow_self (n := (Request.topWord a (.thr r four L target)).length)
  omega

theorem rec_bound (four : r.circuits.length ≤ 4) (L target : ℕ) (i : Fin 4) (x : Rec) (hx : x ∈ tab (dOf (dsOf a r) i)) :
    recMag x < 2 ^ (twOf (dsOf a r)).length := by
  rw [tab_eq a r four] at hx
  rw [tw_eq a r four L target]
  exact rec_lt a r four L target i.val x hx

theorem Cv_le (four : r.circuits.length ≤ 4) (L target : ℕ) : Cv (dsOf a r) ≤ 2 ^ (4 * (twOf (dsOf a r)).length) := by
  have h0 := tab_len a r four L target 0
  have h1 := tab_len a r four L target 1
  have h2 := tab_len a r four L target 2
  have h3 := tab_len a r four L target 3
  unfold Cv
  have e : 2 ^ (4 * (twOf (dsOf a r)).length) = 2 ^ (twOf (dsOf a r)).length * (2 ^ (twOf (dsOf a r)).length *
      (2 ^ (twOf (dsOf a r)).length * (2 ^ (twOf (dsOf a r)).length * 1))) := by ring
  rw [e]
  exact Nat.mul_le_mul h0 (Nat.mul_le_mul h1 (Nat.mul_le_mul h2 (Nat.mul_le_mul h3 (le_refl 1))))

theorem Fv_le (four : r.circuits.length ≤ 4) (L target : ℕ) : Fv (dsOf a r) ≤ 2 ^ (8 * (twOf (dsOf a r)).length + 10) := by
  set R := (twOf (dsOf a r)).length with hR
  have hsel : ∀ x0 ∈ tab (dOf (dsOf a r) 0), ∀ x1 ∈ tab (dOf (dsOf a r) 1), ∀ x2 ∈ tab (dOf (dsOf a r) 2),
      ∀ x3 ∈ tab (dOf (dsOf a r) 3), selMag [x0, x1, x2, x3] ≤ 2 ^ (4 * R + 10) := by
    intro x0 h0 x1 h1 x2 h2 x3 h3
    exact (selMag_lt R x0 x1 x2 x3 (rec_bound a r four L target 0 x0 h0) (rec_bound a r four L target 1 x1 h1)
      (rec_bound a r four L target 2 x2 h2) (rec_bound a r four L target 3 x3 h3)).le
  have hn := nestedSum_le _ _ _ _ selMag _ hsel
  have h0 := tab_len a r four L target 0
  have h1 := tab_len a r four L target 1
  have h2 := tab_len a r four L target 2
  have h3 := tab_len a r four L target 3
  have hm : (tab (dOf (dsOf a r) 0)).length * ((tab (dOf (dsOf a r) 1)).length * ((tab (dOf (dsOf a r) 2)).length *
      ((tab (dOf (dsOf a r) 3)).length * 2 ^ (4 * R + 10)))) ≤
      2 ^ R * (2 ^ R * (2 ^ R * (2 ^ R * 2 ^ (4 * R + 10)))) :=
    Nat.mul_le_mul h0 (Nat.mul_le_mul h1 (Nat.mul_le_mul h2 (Nat.mul_le_mul h3 (le_refl _))))
  have e : 2 ^ R * (2 ^ R * (2 ^ R * (2 ^ R * 2 ^ (4 * R + 10)))) = 2 ^ (8 * R + 10) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  unfold Fv
  omega

end Thr

end StageRun

end
end NearCubicWires.PacketsMeta

