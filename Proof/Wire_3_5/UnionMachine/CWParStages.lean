import Proof.Wire_3_5.UnionMachine.CWParTop
import Proof.Wire_3_5.UnionMachine.CWCore

/-! # C6 front, U5, the code writers: the parity writer's word passes as Steps

The parity writer (P3:3092-3094) docks its word programs as machines (each rewound): the base fields' pass
(**`genBStage`**), the two top passes (**`topSStage`**, **`topTStage`**), the counter's increment (**`incStage`**),
and a copy of a padded framed word onto a blank tape (**`cpStage`**: base's serializer and pair machines write their
outputs as `frame bits ++ 0^p`, their consumers read exact frames).

Paper quantity: none beyond the passes' (the parity code's fields, as Steps). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParStages
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWParCnt NearCubicWires.WireExponent3_5.UnionMachine.CWParGen
open NearCubicWires.WireExponent3_5.UnionMachine.CWParTop
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-! ## The base fields' pass -/

def σG (B : List Bool) : WState 4 0 := ⟨fun _ => 0, ![B, [], [], [], []], fun r => r.elim0, false⟩

/-- The base pass's entry bank: the bitmap, the cell, four blank streams, the log. -/
def genBIn (B : List Bool) : Fin 7 → List Bool :=
  Fin.addCases (m := 4 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σG B)).A (fun _ => [])

theorem genBIn_val (B : List Bool) (j : Fin 7) :
    genBIn B j = if j.val = 0 then B else if j.val = 1 then [false] else [] := by
  fin_cases j <;> rfl

theorem genBStage (l : List Bool) : ∃ o : Fin 7 → List Bool,
    Step (Rewind.machine genB.toProg.compile) (2 * (72 * l.length + 9) + 2) (fun _ => 0) (genBIn (frame l))
      (fun _ => 0) o ∧
    o 0 = frame l ∧ o 1 = [false] ∧ o 2 = wlF l ∧ o 3 = sgl l ∧ o 4 = CompareMachine.word l.length ∧
    o 5 = CompareMachine.word (l.count true) := by
  set σ := σG (frame l) with hσ
  obtain ⟨τ, hw, e0, e1, e2, e3, e4, ec⟩ := genB_spec 0 l σ (fun _ => rfl) rfl
    (by intro j hj; fin_cases j <;> simp_all <;> rfl)
  obtain ⟨o, st, ho⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step 0 genB σ τ _ hw
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 7) = Fin.castAdd 1 (0 : Fin 6) from rfl, ho]; exact e0
  · rw [show (1 : Fin 7) = Fin.castAdd 1 (1 : Fin 6) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 7) = Fin.castAdd 1 (2 : Fin 6) from rfl, ho]; exact e1
  · rw [show (3 : Fin 7) = Fin.castAdd 1 (3 : Fin 6) from rfl, ho]; exact e2
  · rw [show (4 : Fin 7) = Fin.castAdd 1 (4 : Fin 6) from rfl, ho]; exact e3
  · rw [show (5 : Fin 7) = Fin.castAdd 1 (5 : Fin 6) from rfl, ho]; exact e4

/-! ## The two top passes -/

def σT (K : List Bool) : WState 3 0 := ⟨fun _ => 0, ![K, [], [], []], fun r => r.elim0, false⟩

/-- A top pass's entry bank: the count word, the cell, three blank streams, the log. -/
def topIn (K : List Bool) : Fin 6 → List Bool :=
  Fin.addCases (m := 3 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σT K)).A (fun _ => [])

theorem topIn_val (K : List Bool) (j : Fin 6) :
    topIn K j = if j.val = 0 then K else if j.val = 1 then [false] else [] := by
  fin_cases j <;> rfl

theorem topSStage (k : ℕ) : ∃ o : Fin 6 → List Bool,
    Step (Rewind.machine topS.toProg.compile) (2 * (k * 24 + 30) + 2) (fun _ => 0) (topIn (CompareMachine.word k))
      (fun _ => 0) o ∧
    o 0 = CompareMachine.word k ∧ o 1 = [false] ∧ o 2 = sgl (oddL (k + 1)) ∧ o 3 = CompareMachine.word (k + 1) := by
  set σ := σT (CompareMachine.word k) with hσ
  obtain ⟨τ, hw, e0, e1, e2, ec⟩ := topS_spec 0 k σ (fun _ => rfl) rfl rfl rfl rfl
  obtain ⟨o, st, ho⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step 0 topS σ τ _ hw
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 6) = Fin.castAdd 1 (0 : Fin 5) from rfl, ho]; exact e0
  · rw [show (1 : Fin 6) = Fin.castAdd 1 (1 : Fin 5) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 6) = Fin.castAdd 1 (2 : Fin 5) from rfl, ho]; exact e1
  · rw [show (3 : Fin 6) = Fin.castAdd 1 (3 : Fin 5) from rfl, ho]; exact e2

theorem topTStage (k : ℕ) : ∃ o : Fin 6 → List Bool,
    Step (Rewind.machine topT.toProg.compile) (2 * (k * 60 + 10) + 2) (fun _ => 0) (topIn (CompareMachine.word k))
      (fun _ => 0) o ∧
    o 0 = CompareMachine.word k ∧ o 1 = [false] ∧ o 2 = altF k ∧ o 3 = sgl (List.replicate k true) := by
  set σ := σT (CompareMachine.word k) with hσ
  obtain ⟨τ, hw, e0, e1, e2, ec⟩ := topT_spec 0 k σ (fun _ => rfl) rfl rfl rfl rfl
  obtain ⟨o, st, ho⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step 0 topT σ τ _ hw
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 6) = Fin.castAdd 1 (0 : Fin 5) from rfl, ho]; exact e0
  · rw [show (1 : Fin 6) = Fin.castAdd 1 (1 : Fin 5) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 6) = Fin.castAdd 1 (2 : Fin 5) from rfl, ho]; exact e1
  · rw [show (3 : Fin 6) = Fin.castAdd 1 (3 : Fin 5) from rfl, ho]; exact e2

/-! ## The increment -/

def σI (C N : List Bool) : WState 2 0 := ⟨fun _ => 0, ![C, N, []], fun r => r.elim0, false⟩

/-- The increment's entry bank: the counter's fields, the cell, its count word, the flag, the log. -/
def incIn (C N : List Bool) : Fin 5 → List Bool :=
  Fin.addCases (m := 2 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σI C N)).A (fun _ => [])

theorem incIn_val (C N : List Bool) (j : Fin 5) :
    incIn C N j = if j.val = 0 then C else if j.val = 1 then [false] else if j.val = 2 then N else [] := by
  fin_cases j <;> rfl

theorem incStage (l : List Bool) : ∃ o : Fin 5 → List Bool,
    Step (Rewind.machine incW.toProg.compile) (2 * (l.length * 23 + 50) + 2) (fun _ => 0)
      (incIn (sgl l) (CompareMachine.word l.length)) (fun _ => 0) o ∧
    o 0 = sgl (incBits l) ∧ o 1 = [false] ∧ o 2 = CompareMachine.word (incBits l).length := by
  set σ := σI (sgl l) (CompareMachine.word l.length) with hσ
  obtain ⟨τ, hw, e0, e1, ec⟩ := incW_spec 0 l σ (fun _ => rfl) rfl rfl rfl
  obtain ⟨o, st, ho⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step 0 incW σ τ _ hw
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 5) = Fin.castAdd 1 (0 : Fin 4) from rfl, ho]; exact e0
  · rw [show (1 : Fin 5) = Fin.castAdd 1 (1 : Fin 4) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 5) = Fin.castAdd 1 (2 : Fin 4) from rfl, ho]; exact e1

/-! ## The copy of a padded framed word -/

/-- Copy the framed word at the head of stream `0` to stream `1`. -/
def cpW : WM 1 0 := NearCubicWires.WireExponent3_5.PrimT.CarWM.copyFrameW 0 1

def σC (S : List Bool) : WState 1 0 := ⟨fun _ => 0, ![S, []], fun r => r.elim0, false⟩

/-- The copy's entry bank: the source, the cell, the blank target, the log. -/
def cpIn (S : List Bool) : Fin 4 → List Bool :=
  Fin.addCases (m := 1 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σC S)).A (fun _ => [])

theorem cpIn_val (S : List Bool) (j : Fin 4) :
    cpIn S j = if j.val = 0 then S else if j.val = 1 then [false] else [] := by
  fin_cases j <;> rfl

theorem cpStage (y rest : List Bool) : ∃ o : Fin 4 → List Bool,
    Step (Rewind.machine cpW.toProg.compile) (2 * (14 * y.length + 5) + 2) (fun _ => 0) (cpIn (frame y ++ rest))
      (fun _ => 0) o ∧
    o 0 = frame y ++ rest ∧ o 1 = [false] ∧ o 2 = frame y := by
  set σ := σC (frame y ++ rest) with hσ
  obtain ⟨τ, hw, e1, -, e0, -, -, -, ec⟩ := NearCubicWires.WireExponent3_5.PrimT.CarWM.copyFrame_spec 0 (0 : Fin 2) 1
    (by decide) [] y rest σ (by simp [hσ, σC]) rfl rfl
  obtain ⟨o, st, ho⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step 0 cpW σ τ _ hw
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 4) = Fin.castAdd 1 (0 : Fin 3) from rfl, ho]; show τ.st 0 = _; rw [e0]; rfl
  · rw [show (1 : Fin 4) = Fin.castAdd 1 (1 : Fin 3) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 4) = Fin.castAdd 1 (2 : Fin 3) from rfl, ho]; show τ.st 1 = _; rw [e1]; rfl

end NearCubicWires.WireExponent3_5.UnionMachine.CWParStages
