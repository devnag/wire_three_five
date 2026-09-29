import Proof.Supplier.EquationRowRaw
import Proof.Supplier.EquationRowCutsForward

/-! The complete cold row producer advances its output cursor only right.
This is the exact syntactic premise for paid output-length recording. -/
namespace NearCubicWires.RepairOrdinary.EquationRowRaw
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem embedded_extra_forward {t s extra : ℕ} (p : Machine t s) (i : Fin extra) :
    CursorRestore.NoLeft (TapeEmbedding.machine extra p) (i.natAdd t) := by
  intro q bs a ha
  obtain ⟨b,_hb,he⟩ := Option.map_eq_some_iff.mp ha
  subst a
  simp only [TapeEmbedding.action,Fin.addCases_right]
  decide

theorem header_field_forward : CursorRestore.NoLeft (PCPPQueryField.machine true) 2 := by
  intro q bs a ha
  fin_cases q <;> simp [PCPPQueryField.machine] at ha
  all_goals first
    | (split at ha <;> cases ha <;> simp)
    | (cases ha; simp)

theorem header_append_forward : CursorRestore.NoLeft EquationHeaderAppend.machine 17 := by
  apply CursorRestore.composition_forward
  · exact embedded_extra_forward EquationNaturalHeader.machine (1 : Fin 2)
  · exact CursorRestore.focus_forward EquationHeaderAppend.slots (by decide)
      (PCPPQueryField.machine true) 2 header_field_forward

end NearCubicWires.RepairOrdinary.EquationRowRaw
