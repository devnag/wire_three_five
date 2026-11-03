import Proof.Rows.RowsInitThrInitRun
import Proof.Rows.RowsKeyZeroThr
import Proof.Rows.RowsPartsFill
import Proof.Rows.RowsInitPrefix

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace RowsInit.ThrWork
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJd4d1d9d7d1fa4313_Production RowsConstruction RowsConstruction.BaseLayout RowsConstruction.ThrCell
open RowsInit.ThrLoop (wp wp_val rw_eq init_val loop_val c6_val)
noncomputable section

/-! ## 1. Every work port lies in one of the seven blocks -/

theorem port_cases (NI : ℕ) (p : Fin (2 + rowsWork NI)) :
    (∃ i, p = pubPort NI i) ∨ (∃ i, p = initPort NI i) ∨ (∃ i, p = rowpPort NI i) ∨ (∃ i, p = rcpPort NI i) ∨
      (∃ i, p = loopPort NI i) ∨ (∃ i, p = c6Port NI i) ∨ (∃ i, p = c5Port NI i) := by
  have hp : p.val < 2 + (NI + 610) := rw_eq NI ▸ p.isLt
  by_cases h1 : p.val < 2
  · exact Or.inl ⟨⟨p.val, h1⟩, Fin.ext rfl⟩
  by_cases h2 : p.val < 2 + NI
  · exact Or.inr (Or.inl ⟨⟨p.val - 2, by omega⟩, Fin.ext (by rw [init_val]; simp only; omega)⟩)
  by_cases h3 : p.val < 2 + NI + 8
  · exact Or.inr (Or.inr (Or.inl ⟨⟨p.val - (2 + NI), by omega⟩, Fin.ext (by rw [rowpPort_val]; simp only; omega)⟩))
  by_cases h4 : p.val < 2 + NI + 72
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨p.val - (2 + NI + 8), by omega⟩,
      Fin.ext (by rw [RowsInit.Prefix.rcp_val]; simp only; omega)⟩)))
  by_cases h5 : p.val < 2 + NI + 592
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨p.val - (2 + NI + 72), by simp [MT]; omega⟩,
      Fin.ext (by rw [loop_val]; simp only; omega)⟩))))
  by_cases h6 : p.val < 2 + NI + 594
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨p.val - (2 + NI + 592), by omega⟩,
      Fin.ext (by rw [c6_val]; simp only; omega)⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨p.val - (2 + NI + 594), by omega⟩,
      Fin.ext (by rw [RowsInit.C5.c5_val]; simp only; omega)⟩)))))

/-! ## 2. The halting machine and the switch -/

theorem stop_run {t : ℕ} (H : Fin t → ℕ) (A : Fin t → List Bool) :
    Step (CloseoutRowsOriginalSwitch.stop t) 0 H A H A :=
  ⟨_, runFrom_zero_of_halted (CloseoutRowsOriginalSwitch.stop t) _ rfl, rfl, rfl, le_refl 0⟩

theorem cell0_rep (n : ℕ) : readTapeBit (List.replicate n true) 0 = decide (0 < n) := by
  cases n <;> rfl

/-! ## 3. The shape of `thrBase … 0` (with and without a first key) -/

section Shape

end Shape

/-! ## 4. The key-0 branch: loop block + C6, C5, RC5's key-0 writer -/

section Main

end Main

section Main2

end Main2

/-! ## 5. The THR branch: switch on the nonempty flag (port 150) -/

section Branch

end Branch

end
end RowsInit.ThrWork
