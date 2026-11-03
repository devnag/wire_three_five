import Proof.Rows.RowsInitThrInitWords
import Proof.Rows.RowsInitThrLoop

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace RowsInit.ThrInitRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.BlockPlatform
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction RowsConstruction.BaseLayout PCJd4d1d9d7d1fa4313_Production
open RowsInit.VecDock RowsInit.ThrInitWords
open RowsInit.ThrLoop (wp wp_val vmap vmap_val vmap_inj inst_out rw_eq)
noncomputable section

section Fan
variable {k m : ℕ} (select : Fin m → Option (Fin k)) (data : Fin k → List Bool) (D : ℕ)

theorem fin_in (v : ℕ) (hv : v < k + (m + 1) + 1) :
    ExtIncidence.NativeFanout.input data D ⟨v, hv⟩ =
      if h : v < k then data ⟨v, h⟩ else if v = k + m then List.replicate D true else [] := by
  by_cases h1 : v < k + (m + 1)
  · have e : (⟨v, hv⟩ : Fin (k + (m + 1) + 1)) = Fin.castAdd 1 (⟨v, h1⟩ : Fin (k + (m + 1))) := rfl
    rw [e]; unfold ExtIncidence.NativeFanout.input; rw [Fin.addCases_left]
    by_cases h2 : v < k
    · have e2 : (⟨v, h1⟩ : Fin (k + (m + 1))) = Fin.castAdd (m + 1) (⟨v, h2⟩ : Fin k) := rfl
      rw [e2, Fin.addCases_left, dif_pos h2]
    · have e2 : (⟨v, h1⟩ : Fin (k + (m + 1))) = Fin.natAdd k (⟨v - k, by omega⟩ : Fin (m + 1)) :=
        Fin.ext (by simp; omega)
      rw [e2, Fin.addCases_right, dif_neg h2]
      by_cases h3 : v - k < m
      · have e3 : (⟨v - k, by omega⟩ : Fin (m + 1)) = Fin.castAdd 1 (⟨v - k, h3⟩ : Fin m) := rfl
        rw [e3, Fin.addCases_left, if_neg (by omega)]
      · have e3 : (⟨v - k, by omega⟩ : Fin (m + 1)) = Fin.natAdd m (0 : Fin 1) := Fin.ext (by simp; omega)
        rw [e3, Fin.addCases_right, if_pos (by omega)]
  · have e : (⟨v, hv⟩ : Fin (k + (m + 1) + 1)) = Fin.natAdd (k + (m + 1)) (0 : Fin 1) := Fin.ext (by simp; omega)
    rw [e]; unfold ExtIncidence.NativeFanout.input; rw [Fin.addCases_right, dif_neg (by omega), if_neg (by omega)]

theorem fin_out (v : ℕ) (hv : v < k + (m + 1) + 1) :
    ExtIncidence.NativeFanout.output select data D ⟨v, hv⟩ =
      if h : v < k then data ⟨v, h⟩ else if h2 : v < k + m then
        ZeroPadding.pad D ((select ⟨v - k, by omega⟩).elim [] data)
      else if v = k + m then List.replicate D true else List.replicate (D + 1) false := by
  by_cases h1 : v < k + (m + 1)
  · have e : (⟨v, hv⟩ : Fin (k + (m + 1) + 1)) = Fin.castAdd 1 (⟨v, h1⟩ : Fin (k + (m + 1))) := rfl
    rw [e]; unfold ExtIncidence.NativeFanout.output; rw [Fin.addCases_left]
    by_cases h2 : v < k
    · have e2 : (⟨v, h1⟩ : Fin (k + (m + 1))) = Fin.castAdd (m + 1) (⟨v, h2⟩ : Fin k) := rfl
      rw [e2, Fin.addCases_left, dif_pos h2]
    · have e2 : (⟨v, h1⟩ : Fin (k + (m + 1))) = Fin.natAdd k (⟨v - k, by omega⟩ : Fin (m + 1)) :=
        Fin.ext (by simp; omega)
      rw [e2, Fin.addCases_right, dif_neg h2]
      by_cases h3 : v - k < m
      · have e3 : (⟨v - k, by omega⟩ : Fin (m + 1)) = Fin.castAdd 1 (⟨v - k, h3⟩ : Fin m) := rfl
        rw [e3, Fin.addCases_left, dif_pos (by omega)]
        simp only [ExtIncidence.NativeFanout.word]
      · have e3 : (⟨v - k, by omega⟩ : Fin (m + 1)) = Fin.natAdd m (0 : Fin 1) := Fin.ext (by simp; omega)
        rw [e3, Fin.addCases_right, dif_neg (by omega), if_pos (by omega)]
  · have e : (⟨v, hv⟩ : Fin (k + (m + 1) + 1)) = Fin.natAdd (k + (m + 1)) (0 : Fin 1) := Fin.ext (by simp; omega)
    rw [e]; unfold ExtIncidence.NativeFanout.output
    rw [Fin.addCases_right, dif_neg (by omega), dif_neg (by omega), if_neg (by omega)]

theorem fan_dock {u : ℕ} (sl : Fin (k + (m + 1) + 1) → Fin u) (hi : Function.Injective sl)
    (hD : ∀ i, (data i).length ≤ D) (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (sl j) = 0)
    (hs : ∀ (v : ℕ) (hv : v < k), A (sl ⟨v, by omega⟩) = data ⟨v, hv⟩)
    (hd : A (sl ⟨k + m, by omega⟩) = List.replicate D true)
    (hb : ∀ (v : ℕ) (hv : v < k + (m + 1) + 1), k ≤ v → v ≠ k + m → A (sl ⟨v, hv⟩) = []) :
    Step (RecoveryFocus.machine sl (ExtIncidence.NativeFanout.machine select)) (2 * D + 4) H A H
      (install sl A (ExtIncidence.NativeFanout.output select data D)) := by
  refine run_dock (Step.of_ready (ExtIncidence.NativeFanout.ready select data D hD)) sl hi H A hH (fun l => ?_)
  obtain ⟨v, hv⟩ := l
  rw [fin_in]
  by_cases h1 : v < k
  · rw [dif_pos h1]; exact hs v h1
  · rw [dif_neg h1]
    by_cases h2 : v = k + m
    · subst h2; rw [if_pos rfl]; exact hd
    · rw [if_neg h2]; exact hb v hv (by omega) h2

end Fan

/-! ## 2. The fixed `init` indices and the three slot maps -/

/-! Left inverses (injectivity by `congrArg`). -/

section Maps




end Maps

/-! ## 3. Disjointness tables -/


/-! ## 4. Docked banks by value -/

theorem inst_at {NI n : ℕ} {f : ℕ → ℕ} (hb : ∀ v, v < n → f v < 2 + rowsWork NI)
    (hi : Function.Injective (vmap NI n f)) (A : Fin (2 + rowsWork NI) → List Bool) (B : Fin n → List Bool)
    (x : Fin (2 + rowsWork NI)) (v : ℕ) (hv : v < n) (hx : x.val = f v) :
    install (vmap NI n f) A B x = B ⟨v, hv⟩ := by
  rw [show x = vmap NI n f ⟨v, hv⟩ from Fin.ext (hx.trans (vmap_val hb ⟨v, hv⟩).symm)]
  exact install_slot _ hi _ _ _

theorem inst_off {NI n : ℕ} {f : ℕ → ℕ} (hb : ∀ v, v < n → f v < 2 + rowsWork NI)
    (A : Fin (2 + rowsWork NI) → List Bool) (B : Fin n → List Bool) (x : Fin (2 + rowsWork NI))
    (h : ∀ v, v < n → f v ≠ x.val) : install (vmap NI n f) A B x = A x :=
  install_other _ _ _ _ (fun j hj => h j.val j.isLt (by rw [← hj, vmap_val hb]))

/-! ## 5. The machine, its cost, the fanout data -/

section Machine


end Machine

theorem pad_nil (K : ℕ) : ZeroPadding.pad K [] = List.replicate K false := by
  simp [ZeroPadding.pad]

/-! ## 6. The three stages -/

section Stages

end Stages

/-! ## 7. The run -/

section Run

end Run

end
end RowsInit.ThrInitRun
