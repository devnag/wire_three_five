import Proof.SourceAssembly.SourceRequestCurPrims
import Proof.SourceAssembly.SourceRequestTermSegA

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.CurComp
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding NearCubicWires.SourceRequest.CurPrims
open NearCubicWires.SourceFactorSel.Count (sumM mulM wordM sum_step mul_step word0_step)
noncomputable section

/-! ## `x / J`, `x % J` -/

def divmodLocal :=
  Composition.machine (divM (0 : Fin 11) 1 2 10)
  (Composition.machine (mulM (2 : Fin 11) 1 4 10)
  (Composition.machine (wordM false (0 : Fin 11) 5 10)
  (Composition.machine (wordM false (4 : Fin 11) 6 10)
  (Composition.machine (diffM (5 : Fin 11) 6 7 10)
    (tcopyM (7 : Fin 11) 3 8 9 10)))))

def divmodM {U : Nat} (sl : Fin 11 → Fin U) := RecoveryFocus.machine sl divmodLocal

/-! ## `x - y` -/

def subLocal :=
  Composition.machine (wordM false (0 : Fin 9) 3 8)
  (Composition.machine (wordM false (1 : Fin 9) 4 8)
  (Composition.machine (diffM (3 : Fin 9) 4 5 8)
    (tcopyM (5 : Fin 9) 2 6 7 8)))

def subCost (x : Nat) : Nat := 10 * x + 40

theorem sub_run (x y Qa Qb S C : Nat) (E : Fin 9 → List Bool) (hy : y ≤ x) (hS : x + 2 ≤ S) (hC : 2 * x + 5 ≤ C)
    (h0 : E 0 = ZeroPadding.pad Qa (List.replicate x true)) (h1 : E 1 = ZeroPadding.pad Qb (List.replicate y true))
    (hscr : ∀ j : Fin 9, 2 ≤ j.val → j.val < 8 → E j = List.replicate S false)
    (h8 : E 8 = List.replicate C false) :
    ∃ E' : Fin 9 → List Bool, Step subLocal (subCost x) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 2 = ZeroPadding.pad S (List.replicate (x - y) true) ∧
      (∀ j : Fin 9, ¬ (2 ≤ j.val ∧ j.val < 8) → E' j = E j) ∧
      (∀ j : Fin 9, 2 ≤ j.val → j.val < 8 → (E' j).length = S) := by
  set E1 := Function.update E 3 (ZeroPadding.pad S (CompareMachine.word x)) with hE1
  set E2 := Function.update E1 4 (ZeroPadding.pad S (CompareMachine.word y)) with hE2
  set E3 := Function.update E2 5 (ZeroPadding.pad S (CompareMachine.word (x - y))) with hE3
  set E4 := Function.update (Function.update (Function.update E3 2
    (ZeroPadding.pad S (List.replicate (x - y) true))) 6 (ZeroPadding.pad S (List.replicate (x - y) true)))
    7 (ZeroPadding.pad S (CompareMachine.word (x - y))) with hE4
  have s1 := word0_step (0 : Fin 9) 3 8 (by decide) (by decide) (by decide) x Qa S C hS (by omega)
    (fun _ => 0) E (fun _ _ => rfl) h0 (hscr 3 (by decide) (by decide)) h8
  have s2 := word0_step (1 : Fin 9) 4 8 (by decide) (by decide) (by decide) y Qb S C (by omega) (by omega)
    (fun _ => 0) E1 (fun _ _ => rfl) (by simp [E1, h1]) (by simp [E1, hscr 4 (by decide) (by decide)])
    (by simp [E1, h8])
  have s3 := diff_step (3 : Fin 9) 4 5 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    x y S S S C hy hS (by omega) (by omega) (by omega) (fun _ => 0) E2 (fun _ _ => rfl)
    (by simp [E1, E2]) (by simp [E2]) (by simp [E1, E2, hscr 5 (by decide) (by decide)]) (by simp [E1, E2, h8])
  have s4 := tcopy_step (5 : Fin 9) 2 6 7 8 (by decide) (x - y) S S C (by omega) (by omega) (by omega)
    (fun _ => 0) E3 (fun _ _ => rfl) (by simp [E3])
    (by simp [E1, E2, E3, hscr 2 (by decide) (by decide)])
    (by simp [E1, E2, E3, hscr 6 (by decide) (by decide)])
    (by simp [E1, E2, E3, hscr 7 (by decide) (by decide)])
    (by simp [E1, E2, E3, h8])
  have hall : Step subLocal _ _ _ _ _ := s1.seq (s2.seq (s3.seq s4))
  refine ⟨E4, hall.enlarge ?_, ?_, ?_, ?_⟩
  · unfold subCost; omega
  · simp [E1, E2, E3, E4]
  · intro j hj
    have hne : ∀ c : Fin 9, 2 ≤ c.val → c.val < 8 → j ≠ c := fun c h1 h2 e => hj (e ▸ ⟨h1, h2⟩)
    simp [E1, E2, E3, E4, hne 2 (by decide) (by decide), hne 3 (by decide) (by decide),
      hne 4 (by decide) (by decide), hne 5 (by decide) (by decide), hne 6 (by decide) (by decide),
      hne 7 (by decide) (by decide)]
  · intro j h2 h8'
    fin_cases j <;> simp [E1, E2, E3, E4, ZeroPadding.pad_length, CompareMachine.word] at h2 h8' ⊢ <;> omega

def subM {U : Nat} (sl : Fin 9 → Fin U) := RecoveryFocus.machine sl subLocal

/-! ## The block test `[s ≤ x]` -/

def testLocal := Composition.machine (wordM false (0 : Fin 5) 3 4) (cmpM (3 : Fin 5) 1 2 4)

def testM {U : Nat} (sl : Fin 5 → Fin U) := RecoveryFocus.machine sl testLocal

/-! ## Unary copy -/

theorem copy_local (n Qa S C : Nat) (hC : n + 1 ≤ C) :
    Step PCPUnaryCopy.machine (2 * n + 4) (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate n true), List.replicate S false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate n true), ZeroPadding.pad S (List.replicate n true),
        List.replicate C false] := by
  have base := Step.of_ready (PCPUnaryCopy.copy_ready n Qa S C)
  refine base.congr rfl ?_
  funext i
  fin_cases i
  · rfl
  · rfl
  · show List.replicate (max C (n + 1)) false = _
    rw [Nat.max_eq_left hC]
    rfl

def copyM {U : Nat} (a d l : Fin U) := RecoveryFocus.machine (![a, d, l] : Fin 3 → Fin U) PCPUnaryCopy.machine

/-- **Unary copy, docked** (`Function.update` of the destination). -/
theorem copy_step {U : Nat} (a d l : Fin U) (h1 : a ≠ d) (h2 : a ≠ l) (h3 : d ≠ l)
    (n Qa S C : Nat) (hC : n + 1 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ z, z = a ∨ z = d ∨ z = l → H z = 0)
    (ha : A a = ZeroPadding.pad Qa (List.replicate n true))
    (hd : A d = List.replicate S false) (hl : A l = List.replicate C false) :
    Step (copyM a d l) (2 * n + 4) H A H (Function.update A d (ZeroPadding.pad S (List.replicate n true))) :=
  SLoad.step_update (copy_local n Qa S C hC) 1
    (by intro i hi; fin_cases i <;> first | rfl | exact absurd rfl hi)
    _ (SLoad.triple_injective a d l h1 h2 h3) H A
    (by
      intro i; fin_cases i
      · exact hH _ (Or.inl rfl)
      · exact hH _ (Or.inr (Or.inl rfl))
      · exact hH _ (Or.inr (Or.inr rfl)))
    (by intro i; fin_cases i <;> assumption)

end
end NearCubicWires.SourceRequest.CurComp

