import Proof.CaseAnalysis.FinalCallCountCap

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10DimensionWords

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The producer's input, port by port -/

theorem input_cases (b : ℕ) (j : Fin 19) :
    CompetitorDimensions.input b j = if j.val = 0 then List.replicate b true else [] := by
  refine Fin.addCases (m := 13) (n := 6) ?_ ?_ j
  · intro k
    have h : CompetitorDimensions.input b (Fin.castAdd 6 k) =
        CompetitorDimensions.bootstrapInput b k := by
      simp only [CompetitorDimensions.input, CompetitorDimensions.extendTapes, Fin.addCases_left]
    rw [h]
    simp only [CompetitorDimensions.bootstrapInput, Fin.val_castAdd]
    rfl
  · intro k
    have h : CompetitorDimensions.input b (Fin.natAdd 13 k) = [] := by
      simp only [CompetitorDimensions.input, CompetitorDimensions.extendTapes, Fin.addCases_right]
    rw [h]
    have hv : (Fin.natAdd 13 k).val = 13 + k.val := rfl
    rw [hv, if_neg (by omega : ¬ (13 + k.val = 0))]

/-! ## §2 The engine -/

/-- **The corpus's dimension producer, docked at an arbitrary bank.**  From the
unary driver on `slots 0` and nineteen slots otherwise empty: the driver is
restored, `slots 15` carries the wide width, `slots 17` the capacity, every head
returns to zero, and every tape outside the slot map is untouched.

Sixteen of the nineteen slots are pure scratch: they must start empty and they
end dirty. -/
theorem dimensions_dock {m : ℕ} (b : ℕ) (slots : Fin 19 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (hdriver : A (slots 0) = List.replicate b true)
    (hblank : ∀ j : Fin 19, j.val ≠ 0 → A (slots j) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots CompetitorDimensions.machine)
        (CompetitorDimensions.budget b) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 0) = List.replicate b true ∧
      A' (slots 15) = List.replicate (CompetitorRationalDecision.width b) true ∧
      A' (slots 17) = List.replicate (CompetitorReusableDecision.capacity b) true ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨out, hready, h0, h15, h17⟩ := CompetitorDimensions.dimensions_run b
  have hstep : Step CompetitorDimensions.machine (CompetitorDimensions.budget b)
      (fun _ => 0) (CompetitorDimensions.input b) (fun _ => 0) out := by
    obtain ⟨r, hr, ht, hh, hs⟩ := hready
    exact ⟨r, hr, funext hh, ht, hs⟩
  have hA : ∀ j : Fin 19, A (slots j) = CompetitorDimensions.input b j := by
    intro j
    rw [input_cases]
    by_cases hj : j.val = 0
    · rw [if_pos hj]
      have hj0 : j = 0 := Fin.ext hj
      subst hj0
      exact hdriver
    · rw [if_neg hj]
      exact hblank j hj
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨dockH slots H (fun _ => 0), install slots A out, hdock, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    cases hp : RecoveryFocus.pick slots i with
    | none => simp only [dockH, hp]; exact hH i
    | some j => simp only [dockH, hp]
  · rw [install_slot slots hinj A out 0]; exact h0
  · rw [install_slot slots hinj A out 15]; exact h15
  · rw [install_slot slots hinj A out 17]; exact h17
  · intro i hi
    exact install_other slots A out i hi

/-! ## §3 The scratch contract, as a number -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10DimensionWords
