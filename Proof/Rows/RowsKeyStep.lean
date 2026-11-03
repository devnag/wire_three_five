import Proof.Rows.RowsBaseLayout
import Proof.MachineModel.OrdinaryFramedIncrement
import Proof.MachineModel.OrdinaryWitnessCounterCheck
import Proof.CaseAnalysis.RowsOriginalSwitch
import Proof.Rows.FinalPrimeModularSum
import Proof.Amplification.RecoveryScratchErase

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.KeyStep
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open SignedSortKey
noncomputable section

/-- A framed binary word. -/
abbrev fb (w x : Nat) : List Bool := frame (binary w x)

/-! ## 1. The four local stages -/

theorem pair_eq (a b : List Bool) :
    (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool) (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)) = ![a, b] := by
  funext i
  fin_cases i <;> rfl

theorem inc_local (w x cI : Nat) (hx : x+1 < 2^w) (hc : 2*w ≤ cI) :
    Step FramedIncrement.machine (4*w+2) (fun _ => 0) ![fb w x, List.replicate cI false]
      (fun _ => 0) ![fb w (x+1), List.replicate cI false] := by
  obtain ⟨r, hr, h0, h1, hh, _, _⟩ := FramedIncrement.increment_run w x cI hx hc
  rw [← pair_eq, ← pair_eq]
  apply Step.of_run hr (funext hh)
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem pad_false (R : Nat) (hR : 1 ≤ R) : ZeroPadding.pad R [false] = List.replicate R false := by
  obtain ⟨k, rfl⟩ : ∃ k, R = k+1 := ⟨R-1, by omega⟩
  simp [ZeroPadding.pad, List.replicate_succ]

theorem pad_zero (l : List Bool) : ZeroPadding.pad 0 l = l := by
  simp [ZeroPadding.pad]

/-- The flag reset, on the `R`-padded flag with the cell bank's clock `1^R` and log `0^(R+1)`. -/
theorem rst_localR (b : Bool) (R : Nat) (hR : 1 ≤ R) :
    Step (RecoveryScratchErase.resetMachine 1) (2*R+4) (fun _ => 0)
      ![ZeroPadding.pad R [b], List.replicate R true, List.replicate (R+1) false]
      (fun _ => 0) ![List.replicate R false, List.replicate R true, List.replicate (R+1) false] := by
  have h := Step.of_ready (RecoveryScratchErase.erase_ready (t := 1) R (R+1) (fun _ => ZeroPadding.pad R [b])
    (fun _ => by rw [ZeroPadding.pad_length]; simp; omega))
  have e1 : (Fin.addCases (motive := fun _ : Fin (1+1+1) => List Bool)
      (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool) (fun _ : Fin 1 => ZeroPadding.pad R [b])
        (fun _ : Fin 1 => List.replicate R true)) (fun _ : Fin 1 => List.replicate (R+1) false)) =
      ![ZeroPadding.pad R [b], List.replicate R true, List.replicate (R+1) false] := by
    funext i; fin_cases i <;> rfl
  have e2 : (Fin.addCases (motive := fun _ : Fin (1+1+1) => List Bool)
      (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool) (fun _ : Fin 1 => List.replicate R false)
        (fun _ : Fin 1 => List.replicate R true)) (fun _ : Fin 1 => List.replicate (max (R+1) (R+1)) false)) =
      ![List.replicate R false, List.replicate R true, List.replicate (R+1) false] := by
    funext i; fin_cases i <;> (simp only [max_self]; rfl)
  rw [e1, e2] at h
  exact h

/-! ## 2. The stages docked on a bank through a slot map `sl : Fin 8 → Fin t`

`sl 0` digit `x`, `sl 1` bound `b`, `sl 2` flag `[false]`, `sl 3` increment scratch `0^cI`, `sl 4` compare scratch
`0^cC`, `sl 5` clear log `0^cL`, `sl 6` eraser driver `[true]`, `sl 7` eraser log `[false,false]`. -/

section Dock
variable {t : Nat} (sl : Fin 8 → Fin t)

def incM := RecoveryFocus.machine (sl ∘ ![0, 3]) FramedIncrement.machine
def rstM := RecoveryFocus.machine (sl ∘ ![2, 6, 7]) (RecoveryScratchErase.resetMachine 1)

theorem update_same (A : Fin t → List Bool) (j : Fin t) (v : List Bool) (h : A j = v) :
    Function.update A j v = A := by
  rw [← h]; exact Function.update_eq_self j A

variable (hinj : Function.Injective sl)
include hinj

theorem inc_at (w x cI : Nat) (H : Fin t → ℕ) (A : Fin t → List Bool) (hH : ∀ i, H (sl i) = 0)
    (hX : A (sl 0) = fb w x) (hI : A (sl 3) = List.replicate cI false) (hx : x+1 < 2^w) (hc : 2*w ≤ cI) :
    Step (incM sl) (4*w+2) H A H (Function.update A (sl 0) (fb w (x+1))) := by
  have hs : Function.Injective (sl ∘ ![0, 3]) := hinj.comp (by decide)
  have h := SymVerdict.focus_at (inc_local w x cI hx hc) (sl ∘ ![0, 3]) hs H A
    (fun j => by fin_cases j <;> exact hH _) (fun j => by fin_cases j <;> simp [hX, hI])
  rw [dockH_existing _ H _ (fun j => by fin_cases j <;> exact hH _),
    SymVerdict.install_update _ hs A _ 0 (fun j hj => by fin_cases j <;> first | exact absurd rfl hj | simp [hI])] at h
  exact h

theorem rst_at (b : Bool) (R : Nat) (hR : 1 ≤ R) (H : Fin t → ℕ) (A : Fin t → List Bool) (hH : ∀ i, H (sl i) = 0)
    (hF : A (sl 2) = ZeroPadding.pad R [b]) (hD : A (sl 6) = List.replicate R true)
    (hG : A (sl 7) = List.replicate (R+1) false) :
    Step (rstM sl) (2*R+4) H A H (Function.update A (sl 2) (List.replicate R false)) := by
  have hs : Function.Injective (sl ∘ ![2, 6, 7]) := hinj.comp (by decide)
  have h := SymVerdict.focus_at (rst_localR b R hR) (sl ∘ ![2, 6, 7]) hs H A
    (fun j => by fin_cases j <;> exact hH _) (fun j => by fin_cases j <;> simp [hF, hD, hG])
  rw [dockH_existing _ H _ (fun j => by fin_cases j <;> exact hH _),
    SymVerdict.install_update _ hs A _ 0 (fun j hj => by
      fin_cases j
      · exact absurd rfl hj
      · simp [hD]
      · simp [hG])] at h
  exact h

/-! ## 3. The digit step: no carry, and carry into `K` -/

end Dock

end
end RowsConstruction.KeyStep
