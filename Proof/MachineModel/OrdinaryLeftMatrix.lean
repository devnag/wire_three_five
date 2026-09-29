import Proof.MachineModel.OrdinaryGridRows

/-! Actual left-matrix production from the coordinate sorter's literal output.
The dimension templates and source/output cursor placement are explicit inputs. -/
namespace NearCubicWires.RepairOrdinary.LeftMatrix
open LocalBitMultitape SupplierPrinter LeftPlaneCell CoordinateKey GridRows
open StablePartition (Record recordsBits)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem selected_run {Rows Columns Used Capacity : ℕ} (I K : ℕ)
    (payload : Fin (Rows + Columns) → Fin Used → Bool) (left : IntMatrix Rows Used)
    (negative : Bool) (bit : ℕ) (hcap : Used ≤ Capacity)
    (hleft : ∀ row inner, payload (row.castAdd Columns) inner = coefficientBit negative (left row inner) bit)
    (out : List Bool) :
    ∃ phase, ∃ r : ExecutionReceipt 5 48,
      runFrom MatrixRows.machine
        ((MatrixRows.fields (leftRows I K payload)).length + Rows * (3 * Used + 2 * (Capacity - Used) + 11) + 1)
        (MatrixRows.config MatrixRows.machine.start (StablePartition.stream (grid I K payload)) 0 out
          Used (Capacity - Used) 1 Rows) = some r ∧
      r.final = MatrixRows.config (UnaryController.stop (s := 22) phase) (StablePartition.stream (grid I K payload))
        (MatrixRows.fields (leftRows I K payload)).length
        (out ++ WilliamsLoaderForms.rowMajorBitMatrix (fun row inner =>
          coefficientBit negative (padSignedInner (Capacity := Capacity) left row inner) bit))
        Used (Capacity - Used) (Rows + 1) Rows ∧
      r.steps = (MatrixRows.fields (leftRows I K payload)).length + Rows * (3 * Used + 2 * (Capacity - Used) + 11) + 1 ∧
      r.peakTapeCells ≤ (StablePartition.stream (grid I K payload)).length + out.length + (Rows + 2) * Capacity + Rows + 6 := by
  obtain ⟨phase, r, hr, hf, hs, hp⟩ := MatrixRows.matrix_run [] (leftRows I K payload)
    (MatrixRows.fields (rightRows I K payload) ++ [false]) out Used (Capacity - Used) (left_width I K payload)
  have hsource : [] ++ MatrixRows.fields (leftRows I K payload) ++
      (MatrixRows.fields (rightRows I K payload) ++ [false]) = StablePartition.stream (grid I K payload) := by
    rw [StablePartition.stream, grid_split]
    simp only [List.nil_append, List.append_assoc]
  rw [hsource, left_length] at hr hf hp
  rw [left_length] at hs
  rw [signed_output I K payload left negative bit hcap hleft] at hf
  have hdim : Used + (Capacity - Used) = Capacity := Nat.add_sub_of_le hcap
  rw [hdim] at hp
  exact ⟨phase, r, hr, by simpa only [List.length_nil, Nat.zero_add] using hf, hs, hp⟩

end NearCubicWires.RepairOrdinary.LeftMatrix
