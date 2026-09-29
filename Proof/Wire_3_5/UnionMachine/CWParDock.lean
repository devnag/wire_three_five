import Proof.Wire_3_5.UnionMachine.CWParSuf

/-! # C6 front, U5, the code writers: docking the parity writer's stages on any bank

Generic docks for the parity writer's machines (P3:3092-3094): base's serializer (**`ser_dock`**), base's tagged cons
(**`cons_dock`**), a copy of a padded framed word (**`cp_dock`**), a fixed framed word (**`const_dock`**, the word
program `emitL`), and the cell (**`cell_dock`**). Each states the stage's inputs as tape facts on the bank and its
outputs through `install`.

Paper quantity: none (the parity writer's docking). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParDock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWParGen (emitL emitL_spec)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParStages (cpW cpIn cpIn_val cpStage)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParRound (cons)
open NearCubicWires.WireExponent3_5.UnionMachine.CWCore (serM serIn serCost serStage)
open NearCubicWires.WireExponent3_5.UnionMachine.CWMain (serIn_val)
open NearCubicWires.WireExponent3_5.UnionMachine (FrontLoopKit.step_of_ready)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

variable {N : ℕ}

theorem zeroH {t : ℕ} (sl : Fin t → Fin N) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing sl _ _ (fun _ => rfl)

/-- **The cell**: `[false]` on a blank tape. -/
theorem cell_dock (c : Fin N) (B : Fin N → List Bool) (hc : B c = []) :
    Step (RecoveryFocus.machine (fun _ : Fin 1 => c) NearCubicWires.WireExponent3_5.PrimT.cellM) 1 (fun _ => 0) B
      (fun _ => 0) (install (fun _ : Fin 1 => c) B (fun _ => [false])) := by
  have d := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock (fun _ : Fin 1 => c)
    (fun a b _ => Subsingleton.elim a b) (fun _ => 0) B (fun _ => rfl) (fun _ => hc)
  rw [zeroH] at d
  exact d

/-- **Base's serializer** on the fields `gs` (tape `0`) and their count word (tape `2`). -/
theorem ser_dock (sl : Fin 129 → Fin N) (hsl : Function.Injective sl) (gs : List (List Bool)) (B : Fin N → List Bool)
    (h0 : B (sl 0) = gs.flatMap frame) (h2 : B (sl 2) = CompareMachine.word gs.length)
    (hF : ∀ j : Fin 129, j.val ≠ 0 → j.val ≠ 2 → B (sl j) = []) :
    ∃ o : Fin 129 → List Bool, Step (RecoveryFocus.machine sl serM) (serCost gs) (fun _ => 0) B (fun _ => 0)
      (install sl B o) ∧ o 0 = gs.flatMap frame ∧ o 2 = CompareMachine.word gs.length ∧
      o 77 = frame (PCPTraversal.code gs).bits ++ List.replicate
        (PCPPairReusable.capacity (PCPSerializerMass.mass gs) - (frame (PCPTraversal.code gs).bits).length) false := by
  obtain ⟨o, s, z0, z2, z77⟩ := serStage gs
  have d := s.dock sl hsl (fun _ => 0) B (fun _ => rfl) (by
    intro j; rw [serIn_val]
    by_cases hj0 : j.val = 0
    · rw [if_pos hj0, show j = 0 from Fin.ext hj0, h0]
    · rw [if_neg hj0]
      by_cases hj2 : j.val = 2
      · rw [if_pos hj2, show j = 2 from Fin.ext hj2, h2]
      · rw [if_neg hj2, hF j hj0 hj2])
  rw [zeroH] at d
  exact ⟨o, d, z0, z2, by rw [z77]; rfl⟩

/-- **Base's tagged cons** `Nat.pair 1 (Nat.pair x y)` on `frame x.bits` (tape `2`) and `frame y.bits` (tape `3`). -/
theorem cons_dock (sl : Fin 76 → Fin N) (hsl : Function.Injective sl) (x y : ℕ) (B : Fin N → List Bool)
    (hA : B (sl 2) = frame x.bits) (hR : B (sl 3) = frame y.bits)
    (hF : ∀ j : Fin 76, j.val ≠ 2 → j.val ≠ 3 → B (sl j) = []) :
    ∃ o : Fin 76 → List Bool, Step (RecoveryFocus.machine sl PCPPRequestTaggedCons.machine)
      (PCPPRequestTaggedCons.budget x y) (fun _ => 0) B (fun _ => 0) (install sl B o) ∧
      ∃ pd, o 64 = frame (cons x y).bits ++ List.replicate pd false := by
  obtain ⟨o, r, ⟨pd, q64⟩, -⟩ := PCPPRequestTaggedCons.cons_run x y
  have d := (FrontLoopKit.step_of_ready r).dock sl hsl (fun _ => 0) B (fun _ => rfl) (by
    intro k
    show B (sl k) = PCPPRequestTaggedCons.input x y k
    unfold PCPPRequestTaggedCons.input PCPPRequestPair.input PCPPairCanonical.input
    by_cases h2 : k.val = 2
    · rw [dif_pos (by omega)]; simp only [h2, if_true]; rw [show k = 2 from Fin.ext h2, hA]
    · by_cases h3 : k.val = 3
      · rw [dif_pos (by omega)]; simp only [h3, if_true, show (3 : ℕ) ≠ 2 by decide, if_false]
        rw [show k = 3 from Fin.ext h3, hR]
      · rw [hF k h2 h3]; split_ifs <;> simp_all)
  rw [zeroH] at d
  exact ⟨o, d, pd, q64⟩

/-- **A copy** of the framed word at the head of `sl 0` onto the blank `sl 2`. -/
theorem cp_dock (sl : Fin 4 → Fin N) (hsl : Function.Injective sl) (y rest : List Bool) (B : Fin N → List Bool)
    (h0 : B (sl 0) = frame y ++ rest) (h1 : B (sl 1) = [false]) (h2 : B (sl 2) = []) (h3 : B (sl 3) = []) :
    ∃ o : Fin 4 → List Bool, Step (RecoveryFocus.machine sl (Rewind.machine cpW.toProg.compile))
      (2 * (14 * y.length + 5) + 2) (fun _ => 0) B (fun _ => 0) (install sl B o) ∧
      o 0 = frame y ++ rest ∧ o 1 = [false] ∧ o 2 = frame y := by
  obtain ⟨o, s, c0, c1, c2⟩ := cpStage y rest
  have d := s.dock sl hsl (fun _ => 0) B (fun _ => rfl) (by
    intro k; rw [cpIn_val]
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3)
  rw [zeroH] at d
  exact ⟨o, d, c0, c1, c2⟩

/-! ## A fixed framed word -/

def constW (w : List Bool) : WM 0 0 := emitL 0 (frame w)

def σK : WState 0 0 := ⟨fun _ => 0, fun _ => [], fun r => r.elim0, false⟩

def constIn : Fin 3 → List Bool :=
  Fin.addCases (m := 0 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 σK).A (fun _ => [])

theorem constIn_val (j : Fin 3) : constIn j = if j.val = 1 then [false] else [] := by
  fin_cases j <;> rfl

theorem constStage (w : List Bool) : ∃ o : Fin 3 → List Bool,
    Step (Rewind.machine (constW w).toProg.compile) (2 * (4 * (frame w).length) + 2) (fun _ => 0) constIn
      (fun _ => 0) o ∧ o 0 = frame w ∧ o 1 = [false] := by
  obtain ⟨τ, hw, e0, -, -, -, ec⟩ := emitL_spec 0 (0 : Fin 1) (frame w) σK rfl
  obtain ⟨o, st, ho⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step 0 (constW w) σK τ _ hw
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_⟩
  · rw [show (0 : Fin 3) = Fin.castAdd 1 (0 : Fin 2) from rfl, ho]; show τ.st 0 = _; rw [e0]; rfl
  · rw [show (1 : Fin 3) = Fin.castAdd 1 (1 : Fin 2) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl

/-- **A fixed framed word** on the blank `sl 0` (cell `sl 1`, log `sl 2`). -/
theorem const_dock (sl : Fin 3 → Fin N) (hsl : Function.Injective sl) (w : List Bool) (B : Fin N → List Bool)
    (h0 : B (sl 0) = []) (h1 : B (sl 1) = [false]) (h2 : B (sl 2) = []) :
    ∃ o : Fin 3 → List Bool, Step (RecoveryFocus.machine sl (Rewind.machine (constW w).toProg.compile))
      (2 * (4 * (frame w).length) + 2) (fun _ => 0) B (fun _ => 0) (install sl B o) ∧ o 0 = frame w ∧
      o 1 = [false] := by
  obtain ⟨o, s, c0, c1⟩ := constStage w
  have d := s.dock sl hsl (fun _ => 0) B (fun _ => rfl) (by
    intro k; rw [constIn_val]
    fin_cases k
    · exact h0
    · exact h1
    · exact h2)
  rw [zeroH] at d
  exact ⟨o, d, c0, c1⟩

end NearCubicWires.WireExponent3_5.UnionMachine.CWParDock
