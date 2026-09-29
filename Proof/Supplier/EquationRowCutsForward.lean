import Proof.Supplier.EquationRowCuts

/-! The actual cut output is append-only. This syntactic rule-table fact
lets the enclosing row framer count its physical output moves directly. -/
namespace NearCubicWires.RepairOrdinary.EquationRowCuts
open LocalBitMultitape EquationCut
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem unselected_forward {t u s : ℕ} (slots : Fin t → Fin u) (p : Machine t s) (i : Fin u)
    (hi : ∀ j,slots j≠i) : CursorRestore.NoLeft (RecoveryFocus.machine slots p) i := by
  intro q bs a ha
  obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
  subst a
  have hn : RecoveryFocus.pick slots i=none := by
    unfold RecoveryFocus.pick
    apply dif_neg
    simpa using hi
  simp [RecoveryFocus.action,hn]

theorem embedded_forward {t s : ℕ} (extra : ℕ) (p : Machine t s) (i : Fin t)
    (hp : CursorRestore.NoLeft p i) : CursorRestore.NoLeft (TapeEmbedding.machine extra p) (i.castAdd extra) := by
  intro q bs a ha
  obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
  subst a
  simpa only [TapeEmbedding.action,Fin.addCases_left] using hp q (fun j => bs (j.castAdd extra)) b hb

end NearCubicWires.RepairOrdinary.EquationRowCuts
