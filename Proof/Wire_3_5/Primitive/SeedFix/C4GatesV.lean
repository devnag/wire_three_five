import Proof.Wire_3_5.Primitive.SeedFix.C4GatesT
import Proof.Wire_3_5.Primitive.SeedFix.C4Geo

/-! # G1, the gate converter, part 6: the gate field's words and the tables' bounds (P3:1655-1664)

C3a's gate field of a pool `G` (`C4Geo.gateField G = frame (segment (G.map suppG) (1^n))`) is, cell by cell, the
count field `marks (natWord |G|)`, the framed arity twice framed, each gate's native word twice framed, the end
(**`gateField_eq`**: `nativeWord (suppG g) = tabGW g`). Each table's width `tabH G` bounds its numbers
(**`table_bounds`**, from TabRef's `tab_nbl_le`).

Paper quantity of the main types: C3a's gate field `gateField G` and the table width's bounds. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Gates
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.PrimT

theorem nativeWord_suppG {n : ℕ} (g : NormalizedThresholdGate n) :
    CloseoutRowsCircuitBottom.nativeWord (C4Geo.suppG g) = tabGW g := rfl

theorem marks_frame' (x : List Bool) : Streaming.marks (frame x) = quad x ++ [true, false] := by
  rw [frame_eq_frameP, Streaming.marks_append]
  show Streaming.marks (Streaming.marks x) ++ _ = _
  rw [marks_marks]
  rfl

/-- **C3a's gate field, cell by cell.** -/
theorem gateField_eq {n : ℕ} (G : List (NormalizedThresholdGate n)) :
    C4Geo.gateField G = Streaming.marks (natWord G.length) ++ (quad (List.replicate n true) ++ [true, false]) ++
      WS G ++ [false] := by
  unfold C4Geo.gateField ExtDecompositionBatch.segment
  rw [frame_eq_frameP]
  show Streaming.marks _ ++ _ = _
  rw [Streaming.marks_append, Streaming.marks_append, marks_frame', List.length_map]
  congr 2
  unfold WS
  induction G with
  | nil => rfl
  | cons g G ih =>
    simp only [List.map_cons, List.flatMap_cons, Streaming.marks_append, ih]
    rw [nativeWord_suppG, marks_frame']

/-- **The table width bounds its numbers.** -/
theorem table_bounds {n : ℕ} (G : List (NormalizedThresholdGate n)) (g : NormalizedThresholdGate n) (hg : g ∈ G) :
    1 ≤ tabH G ∧ (∀ i, (g.weight i).natAbs < 2 ^ tabH G) ∧ (g.threshold - 1).natAbs + 1 < 2 ^ tabH G ∧
      g.threshold.natAbs < 2 ^ tabH G := by
  obtain ⟨hw, ht, hn⟩ := tab_nbl_le G g hg
  have hh : 1 ≤ tabH G := by have := one_le_nbl n; omega
  have hlt : ∀ v : ℕ, natBitLength v + 1 ≤ tabH G → v + 1 < 2 ^ tabH G := by
    intro v hv
    have h1 := CompilerMachine.Pool.lt_pow_natBitLength v
    have h2 : 2 ^ natBitLength v ≤ 2 ^ (tabH G - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 * 2 ^ (tabH G - 1) = 2 ^ tabH G := by
      rw [← pow_succ']; congr 1; omega
    have h4 : 1 ≤ 2 ^ (tabH G - 1) := Nat.one_le_two_pow
    omega
  refine ⟨hh, fun i => ?_, hlt _ ht, ?_⟩
  · have := hlt _ (hw i); omega
  · have := hlt _ ht; omega

end NearCubicWires.WireExponent3_5.PrimT.C4Gates
