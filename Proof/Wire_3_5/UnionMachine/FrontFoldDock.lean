import Proof.Wire_3_5.UnionMachine.FrontFoldCat
import Proof.Wire_3_5.UnionMachine.CWEnvCode
import Proof.Wire_3_5.UnionMachine.CWIface
import Proof.Wire_3_5.UnionMachine.FrontLoopKit

/-! # C6 front, U5, the writers' fold (b): docking the round's stages on any bank

The fold's round (P3:3409-3410, 3432-3433, 3083-3094: per variable, the parity's code, the carrier's code, the carrier's
envelope bit) docks: the cell (`cellD`), FP's crop (`cropD`) and append (`appD`), the carrier input (`catD`), the
envelope bit (`efD`), the envelope stage (`envD`) and any writer's ready run (`writerD`: input `inBank`, output
`outBankJ`). Each states the stage's inputs as tape facts on the bank and its outputs through `install`.

Paper quantity: none (the fold's docking). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldDock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords (cropBW cropBCost cropBIn cropBIn_val cropBStage appendBW
  appendBCost appendBIn appendBIn_val appendBStage)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldCat
open NearCubicWires.WireExponent3_5.UnionMachine.CWEnvCode (envCodeM envCodeIn)
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters (inBank)
open NearCubicWires.WireExponent3_5.UnionMachine.CWIface (outBankJ)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

variable {N : ℕ}

theorem zeroH {t : ℕ} (sl : Fin t → Fin N) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing sl _ _ (fun _ => rfl)

/-- **The cell**: `[false]` on a blank tape. -/
theorem cellD (c : Fin N) (B : Fin N → List Bool) (hc : B c = []) :
    Step (RecoveryFocus.machine (fun _ : Fin 1 => c) NearCubicWires.WireExponent3_5.PrimT.cellM) 1 (fun _ => 0) B
      (fun _ => 0) (install (fun _ : Fin 1 => c) B (fun _ => [false])) := by
  have d := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock (fun _ : Fin 1 => c)
    (fun a b _ => Subsingleton.elim a b) (fun _ => 0) B (fun _ => rfl) (fun _ => hc)
  rw [zeroH] at d
  exact d

/-- **FP's crop**: item `i` of a list of framed words, along the counter. -/
theorem cropD (sl : Fin 9 → Fin N) (hsl : Function.Injective sl) (W : ℕ) (ys : List (List Bool))
    (hys : ∀ y ∈ ys, y.length ≤ W) (tail : List Bool) (i : ℕ) (hi : i < ys.length) (rest : List Bool)
    (B : Fin N → List Bool) (h0 : B (sl 0) = ys.flatMap frame ++ tail) (h1 : B (sl 1) = [false])
    (h2 : B (sl 2) = List.replicate i true ++ (false :: rest)) (hF : ∀ j : Fin 9, 3 ≤ j.val → B (sl j) = []) :
    ∃ o : Fin 9 → List Bool, Step (RecoveryFocus.machine sl (Rewind.machine cropBW.toProg.compile))
      (2 * cropBCost i W + 2) (fun _ => 0) B (fun _ => 0) (install sl B o) ∧
      o 0 = ys.flatMap frame ++ tail ∧ o 1 = [false] ∧ o 2 = List.replicate (i + 1) true ++ rest ∧
      o 3 = frame ys[i] := by
  obtain ⟨o, s, e0, e1, e2, e3, -, -, -, -⟩ := cropBStage W ys hys tail i hi rest
  have d := s.dock sl hsl (fun _ => 0) B (fun _ => rfl) (by
    intro j; rw [cropBIn_val]
    by_cases j0 : j.val = 0
    · rw [if_pos j0, show j = 0 from Fin.ext j0, h0]
    · rw [if_neg j0]
      by_cases j1 : j.val = 1
      · rw [if_pos j1, show j = 1 from Fin.ext j1, h1]
      · rw [if_neg j1]
        by_cases j2 : j.val = 2
        · rw [if_pos j2, show j = 2 from Fin.ext j2, h2]
        · rw [if_neg j2, hF j (by omega)])
  rw [zeroH] at d
  exact ⟨o, d, e0, e1, e2, e3⟩

/-- **FP's append**: a framed word joins a list of framed words. -/
theorem appD (sl : Fin 4 → Fin N) (hsl : Function.Injective sl) (gs : List (List Bool)) (hgs : ∀ g ∈ gs, g ≠ [])
    (y rest : List Bool) (B : Fin N → List Bool) (h0 : B (sl 0) = frame y ++ rest) (h1 : B (sl 1) = [false])
    (h2 : B (sl 2) = gs.flatMap frame) (h3 : B (sl 3) = []) :
    ∃ o : Fin 4 → List Bool, Step (RecoveryFocus.machine sl (Rewind.machine appendBW.toProg.compile))
      (2 * appendBCost gs y + 2) (fun _ => 0) B (fun _ => 0) (install sl B o) ∧
      o 0 = frame y ++ rest ∧ o 1 = [false] ∧ o 2 = (gs ++ [y]).flatMap frame := by
  obtain ⟨o, s, e0, e1, e2⟩ := appendBStage gs hgs y rest
  have d := s.dock sl hsl (fun _ => 0) B (fun _ => rfl) (by
    intro j; rw [appendBIn_val]
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3)
  rw [zeroH] at d
  exact ⟨o, d, e0, e1, e2⟩

/-- **The carrier input.** -/
theorem catD (sl : Fin 7 → Fin N) (hsl : Function.Injective sl) (a p rA rP rc : List Bool) (X sys : ℕ)
    (hrc : rc.getD 0 false = false) (B : Fin N → List Bool) (h0 : B (sl 0) = frame a ++ rA) (h1 : B (sl 1) = [false])
    (h2 : B (sl 2) = frame p ++ rP) (h3 : B (sl 3) = List.replicate (X + 1) true ++ rc)
    (h4 : B (sl 4) = List.replicate sys true) (h5 : B (sl 5) = []) (h6 : B (sl 6) = []) :
    ∃ o : Fin 7 → List Bool, Step (RecoveryFocus.machine sl (Rewind.machine catW.toProg.compile))
      (2 * catCost a.length p.length X + 2) (fun _ => 0) B (fun _ => 0) (install sl B o) ∧
      o 0 = frame a ++ rA ∧ o 1 = [false] ∧ o 2 = frame p ++ rP ∧ o 3 = List.replicate (X + 1) true ++ rc ∧
      o 4 = List.replicate sys true ∧ o 5 = frame (a ++ if X < sys then p else []) := by
  obtain ⟨o, s, e0, e1, e2, e3, e4, e5⟩ := catStage a p rA rP rc X sys hrc
  have d := s.dock sl hsl (fun _ => 0) B (fun _ => rfl) (by
    intro j; rw [catIn_val]
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6)
  rw [zeroH] at d
  exact ⟨o, d, e0, e1, e2, e3, e4, e5⟩

/-- **The envelope bit.** -/
theorem efD (sl : Fin 5 → Fin N) (hsl : Function.Injective sl) (b : Bool) (rE rc F : List Bool) (X : ℕ)
    (hrc : rc.getD 0 false = false) (hF : F.length = X) (B : Fin N → List Bool) (h0 : B (sl 0) = frame [b] ++ rE)
    (h1 : B (sl 1) = [false]) (h2 : B (sl 2) = List.replicate (X + 1) true ++ rc) (h3 : B (sl 3) = F)
    (h4 : B (sl 4) = []) :
    ∃ o : Fin 5 → List Bool, Step (RecoveryFocus.machine sl (Rewind.machine efW.toProg.compile))
      (2 * efCost X + 2) (fun _ => 0) B (fun _ => 0) (install sl B o) ∧
      o 0 = frame [b] ++ rE ∧ o 1 = [false] ∧ o 2 = List.replicate (X + 1) true ++ rc ∧ o 3 = F ++ [b] := by
  obtain ⟨o, s, e0, e1, e2, e3⟩ := efStage b rE rc F X hrc hF
  have d := s.dock sl hsl (fun _ => 0) B (fun _ => rfl) (by
    intro j; rw [efIn_val]
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4)
  rw [zeroH] at d
  exact ⟨o, d, e0, e1, e2, e3⟩

/-- **The envelope stage**, from any run of it on its entry. -/
theorem envD (sl : Fin 1192 → Fin N) (hsl : Function.Injective sl) (x L T c : ℕ) (out : Fin 1192 → List Bool)
    (hE : Step envCodeM c (fun _ => 0) (envCodeIn x L T) (fun _ => 0) out) (B : Fin N → List Bool)
    (h0 : B (sl 0) = frame (natWord x)) (h1 : B (sl 1) = List.replicate L true)
    (h2 : B (sl 1189) = List.replicate T true)
    (hF : ∀ j : Fin 1192, j.val ≠ 0 → j.val ≠ 1 → j.val ≠ 1189 → B (sl j) = []) :
    Step (RecoveryFocus.machine sl envCodeM) c (fun _ => 0) B (fun _ => 0) (install sl B out) := by
  have d := hE.dock sl hsl (fun _ => 0) B (fun _ => rfl) (by
    intro j; unfold envCodeIn
    by_cases j0 : j.val = 0
    · rw [if_pos j0, show j = 0 from Fin.ext j0, h0]
    · rw [if_neg j0]
      by_cases j1 : j.val = 1
      · rw [if_pos j1, show j = 1 from Fin.ext j1, h1]
      · rw [if_neg j1]
        by_cases j2 : j.val = 1189
        · rw [if_pos j2, show j = 1189 from Fin.ext j2, h2]
        · rw [if_neg j2, hF j j0 j1 j2])
  rw [zeroH] at d
  exact d

/-- **Any writer's ready run**: its input word framed on its input slot, its other slots blank. -/
theorem writerD {t s : ℕ} (sl : Fin t → Fin N) (hsl : Function.Injective sl) (M : Machine t s) (inS outS : Fin t)
    (u v : List Bool) (J : Fin t → List Bool) (c : ℕ)
    (hr : ClockJoin.ReadyRun M c (inBank inS u) (outBankJ inS outS u v J)) (B : Fin N → List Bool)
    (hin : B (sl inS) = frame u) (hF : ∀ k, k ≠ inS → B (sl k) = []) :
    Step (RecoveryFocus.machine sl M) c (fun _ => 0) B (fun _ => 0) (install sl B (outBankJ inS outS u v J)) := by
  have d := (FrontLoopKit.step_of_ready hr).dock sl hsl (fun _ => 0) B (fun _ => rfl) (by
    intro k; unfold inBank
    by_cases hk : k = inS
    · rw [if_pos hk, hk, hin]
    · rw [if_neg hk, hF k hk])
  rw [zeroH] at d
  exact d

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldDock
