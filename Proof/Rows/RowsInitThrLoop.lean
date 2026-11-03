import Proof.Rows.RowsInitVecDock

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace RowsInit.ThrLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.BlockPlatform
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction RowsConstruction.BaseLayout RowsConstruction.ThrCell
open RowsInit.VecDock RowsInit.LoopFan RowsInit.MasterFan PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
noncomputable section

/-! ## 1. Work ports by value -/

theorem rw_eq (NI : ℕ) : rowsWork NI = NI + 610 := rfl

/-- The work port of value `v` (clamped; every use has `v < 2 + rowsWork NI`). -/
def wp (NI v : ℕ) : Fin (2 + rowsWork NI) := ⟨v % (2 + rowsWork NI), Nat.mod_lt _ (by omega)⟩

theorem wp_val {NI v : ℕ} (h : v < 2 + rowsWork NI) : (wp NI v).val = v := Nat.mod_eq_of_lt h

theorem pub_val (NI : ℕ) (i : Fin 2) : (pubPort NI i).val = i.val := rfl
theorem init_val (NI : ℕ) (i : Fin NI) : (initPort NI i).val = 2 + i.val := by
  simp [initPort] <;> omega
theorem loop_val (NI : ℕ) (i : Fin (MT+1+1)) : (loopPort NI i).val = 2 + NI + 72 + i.val := by
  simp [loopPort, fixPort, MT] <;> omega
theorem c6_val (NI : ℕ) (i : Fin 2) : (c6Port NI i).val = 2 + NI + 592 + i.val := by
  simp [c6Port, fixPort, MT] <;> omega
theorem master_val (NI : ℕ) (k : Fin 254) : (masterPort NI k).val = 2 + NI + 329 + k.val := by
  simp [masterPort, loopPort, fixPort, masterP, CellReload.masterPort, MT] <;> omega

/-- A slot map given by a value function. -/
def vmap (NI n : ℕ) (f : ℕ → ℕ) : Fin n → Fin (2 + rowsWork NI) := fun i => wp NI (f i.val)

theorem vmap_val {NI n : ℕ} {f : ℕ → ℕ} (hb : ∀ v, v < n → f v < 2 + rowsWork NI) (i : Fin n) :
    (vmap NI n f i).val = f i.val := wp_val (hb i.val i.isLt)

theorem vmap_inj {NI n : ℕ} {f : ℕ → ℕ} (hb : ∀ v, v < n → f v < 2 + rowsWork NI)
    (hf : ∀ v w, v < n → w < n → f v = f w → v = w) : Function.Injective (vmap NI n f) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [vmap_val hb, vmap_val hb] at hv
  exact Fin.ext (hf _ _ i.isLt j.isLt hv)

/-- A port outside a stage's value range keeps its content. -/
theorem inst_out {t u : ℕ} (sl : Fin t → Fin u) (A : Fin u → List Bool) (B : Fin t → List Bool) (x : Fin u)
    (P : ℕ → Prop) (hP : ∀ j, P (sl j).val) (hx : ¬ P x.val) : install sl A B x = A x :=
  install_other _ _ _ _ (fun j h => hx (h ▸ hP j))

/-! ## 2. The four slot maps (init region `[o, o + need a)`) -/


section Maps



end Maps

/-! ## 3. Value ranges of the four stages -/


section Ranges


end Ranges

/-! ## 4. The machine and its cost -/


/-! ## 5. The four stages -/

section Stages

end Stages

section Stages2

end Stages2

section Stages3

end Stages3

/-! ## 6. The consumer's loop bank, port by port -/

/-! ## 7. The source words fit the capacity (`thr_hml` at witnessing ports) -/


/-! ## 8. The chained banks, port by port -/

section Banks




end Banks

/-! ## 9. The run -/

section Run

end Run

end
end RowsInit.ThrLoop
