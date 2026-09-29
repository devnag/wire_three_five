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

/-! ## The block test `[s ≤ x]` -/

/-! ## Unary copy -/

end
end NearCubicWires.SourceRequest.CurComp

