import Proof.SourceAssembly.SourceFactorSelCount

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.CurPrims
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
noncomputable section

/-! ## Local runs -/

theorem pad_word (R n : Nat) (h : n + 2 ≤ R) :
    ZeroPadding.pad R (UnaryTemplate.tape n) = ZeroPadding.pad R (CompareMachine.word n) :=
  (ExtDecompositionBatch.pad_template R n h).symm

theorem pad_zeros_le (C k : Nat) (h : k ≤ C) :
    ZeroPadding.pad C (List.replicate k false) = List.replicate C false := by
  rw [Rewind.Workspace.pad_zeros, Nat.max_eq_left h]

theorem diff_local (n m Qa Qb S C : Nat) (hm : m ≤ n) (hQa : n + 2 ≤ Qa) (hQb : m + 2 ≤ Qb)
    (hS : n - m + 2 ≤ S) (hC : n + 3 ≤ C) :
    Step MatrixUnaryDifference.resetMachine (2 * n + 8) (fun _ => 0)
      ![ZeroPadding.pad Qa (CompareMachine.word n), ZeroPadding.pad Qb (CompareMachine.word m),
        List.replicate S false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad Qa (CompareMachine.word n), ZeroPadding.pad Qb (CompareMachine.word m),
        ZeroPadding.pad S (CompareMachine.word (n - m)), List.replicate C false] := by
  obtain ⟨base, hb, hf, hs⟩ := MatrixUnaryDifference.difference_run n m hm
  obtain ⟨r, hr, ht, hlog, hh, hsteps, _⟩ :=
    Rewind.Workspace.reset_workspace MatrixUnaryDifference.machine _ _ base hb 0
  have hi : (Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
      (MatrixUnaryDifference.input n m) (fun _ : Fin 1 => List.replicate 0 false)) =
      (![UnaryTemplate.tape n, UnaryTemplate.tape m, [], []] : Fin 4 → List Bool) := by
    funext i; fin_cases i <;> rfl
  change run MatrixUnaryDifference.resetMachine (2 * base.steps + 2)
    (Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
      (MatrixUnaryDifference.input n m) (fun _ : Fin 1 => List.replicate 0 false)) = some r at hr
  rw [hi, hs] at hr
  have hready : ClockJoin.ReadyRun MatrixUnaryDifference.resetMachine (2 * n + 8)
      ![UnaryTemplate.tape n, UnaryTemplate.tape m, [], []]
      ![UnaryTemplate.tape n, UnaryTemplate.tape m, UnaryTemplate.tape (n - m),
        List.replicate (n + 3) false] := by
    refine ⟨r, (by simpa only [show 2 * (n + 3) + 2 = 2 * n + 8 by omega] using hr), ?_, hh, by omega⟩
    funext i
    fin_cases i
    · simpa [hf, MatrixUnaryDifference.output] using ht 0
    · simpa [hf, MatrixUnaryDifference.output] using ht 1
    · simpa [hf, MatrixUnaryDifference.output] using ht 2
    · simpa [hs] using hlog
  have base' := (SLoad.MaskFrame.step_of_clockReady hready).pad ![Qa, Qb, S, C]
  refine (base'.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i
    · exact pad_word Qa n hQa
    · exact pad_word Qb m hQb
    · exact SourceFactorSel.Desc.pad_nil S
    · exact SourceFactorSel.Desc.pad_nil C
  · funext i
    fin_cases i
    · exact pad_word Qa n hQa
    · exact pad_word Qb m hQb
    · exact pad_word S (n - m) hS
    · exact pad_zeros_le C _ hC

theorem tcopy_local (n Qa S C : Nat) (hQa : n + 2 ≤ Qa) (hS : n + 2 ≤ S) (hC : 2 * n + 5 ≤ C) :
    Step MatrixTemplateCopy.resetMachine (4 * n + 12) (fun _ => 0)
      ![ZeroPadding.pad Qa (CompareMachine.word n), List.replicate S false, List.replicate S false,
        List.replicate S false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad Qa (CompareMachine.word n), ZeroPadding.pad S (List.replicate n true),
        ZeroPadding.pad S (List.replicate n true), ZeroPadding.pad S (CompareMachine.word n),
        List.replicate C false] := by
  obtain ⟨base, hb, h0, h1, h2, h3, hs⟩ := MatrixTemplateCopy.copy_run n
  obtain ⟨r, hr, ht, hlog, hh, hsteps, _⟩ :=
    Rewind.Workspace.reset_workspace MatrixTemplateCopy.machine _ _ base hb 0
  have hi : (Fin.addCases (motive := fun _ : Fin (4 + 1) => List Bool)
      (MatrixTemplateCopy.input n) (fun _ : Fin 1 => List.replicate 0 false)) =
      (![UnaryTemplate.tape n, [], [], [], []] : Fin 5 → List Bool) := by
    funext i; fin_cases i <;> rfl
  change run MatrixTemplateCopy.resetMachine (2 * base.steps + 2)
    (Fin.addCases (motive := fun _ : Fin (4 + 1) => List Bool)
      (MatrixTemplateCopy.input n) (fun _ : Fin 1 => List.replicate 0 false)) = some r at hr
  rw [hi, hs] at hr
  have hready : ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4 * n + 12)
      ![UnaryTemplate.tape n, [], [], [], []]
      ![UnaryTemplate.tape n, List.replicate n true, List.replicate n true, UnaryTemplate.tape n,
        List.replicate (2 * n + 5) false] := by
    refine ⟨r, (by simpa only [show 2 * (2 * n + 5) + 2 = 4 * n + 12 by omega] using hr), ?_, hh, by omega⟩
    funext i
    fin_cases i
    · simpa using (ht 0).trans h0
    · simpa using (ht 1).trans h1
    · simpa using (ht 2).trans h2
    · simpa using (ht 3).trans h3
    · simpa [hs] using hlog
  have base' := (SLoad.MaskFrame.step_of_clockReady hready).pad ![Qa, S, S, S, C]
  refine (base'.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i
    · exact pad_word Qa n hQa
    · exact SourceFactorSel.Desc.pad_nil S
    · exact SourceFactorSel.Desc.pad_nil S
    · exact SourceFactorSel.Desc.pad_nil S
    · exact SourceFactorSel.Desc.pad_nil C
  · funext i
    fin_cases i
    · exact pad_word Qa n hQa
    · rfl
    · rfl
    · exact pad_word S n hS
    · exact pad_zeros_le C _ hC

/-! ## Docked forms (`Function.update` of the output port(s); heads unchanged) -/

def diffM {U : Nat} (a b d l : Fin U) :=
  RecoveryFocus.machine (![a, b, d, l] : Fin 4 → Fin U) MatrixUnaryDifference.resetMachine
def tcopyM {U : Nat} (a d e f l : Fin U) :=
  RecoveryFocus.machine (![a, d, e, f, l] : Fin 5 → Fin U) MatrixTemplateCopy.resetMachine

theorem quad_inj {U : Nat} (a b d l : Fin U) (h1 : a ≠ b) (h2 : a ≠ d) (h3 : a ≠ l) (h4 : b ≠ d)
    (h5 : b ≠ l) (h6 : d ≠ l) : Function.Injective (![a, b, d, l] : Fin 4 → Fin U) :=
  SLoad.MaskFrame.quad_injective a b d l h1 h2 h3 h4 h5 h6

theorem diff_step {U : Nat} (a b d l : Fin U) (h1 : a ≠ b) (h2 : a ≠ d) (h3 : a ≠ l) (h4 : b ≠ d)
    (h5 : b ≠ l) (h6 : d ≠ l) (n m Qa Qb S C : Nat) (hm : m ≤ n) (hQa : n + 2 ≤ Qa) (hQb : m + 2 ≤ Qb)
    (hS : n - m + 2 ≤ S) (hC : n + 3 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ z, z = a ∨ z = b ∨ z = d ∨ z = l → H z = 0)
    (ha : A a = ZeroPadding.pad Qa (CompareMachine.word n)) (hb : A b = ZeroPadding.pad Qb (CompareMachine.word m))
    (hd : A d = List.replicate S false) (hl : A l = List.replicate C false) :
    Step (diffM a b d l) (2 * n + 8) H A H
      (Function.update A d (ZeroPadding.pad S (CompareMachine.word (n - m)))) :=
  SLoad.step_update (diff_local n m Qa Qb S C hm hQa hQb hS hC) 2
    (by intro i hi; fin_cases i <;> first | rfl | exact absurd rfl hi)
    _ (quad_inj a b d l h1 h2 h3 h4 h5 h6) H A
    (by
      intro i; fin_cases i
      · exact hH _ (Or.inl rfl)
      · exact hH _ (Or.inr (Or.inl rfl))
      · exact hH _ (Or.inr (Or.inr (Or.inl rfl)))
      · exact hH _ (Or.inr (Or.inr (Or.inr rfl))))
    (by intro i; fin_cases i <;> assumption)

/-- Three-output update of an install (the template copy writes three tapes). -/
theorem install_update3 {t u : Nat} (slot : Fin t → Fin u) (hi : Function.Injective slot)
    (A : Fin u → List Bool) (tin tout : Fin t → List Bool) (j1 j2 j3 : Fin t)
    (hkeep : ∀ i, i ≠ j1 → i ≠ j2 → i ≠ j3 → tout i = tin i) (it : ∀ i, A (slot i) = tin i) :
    install slot A tout = Function.update (Function.update (Function.update A (slot j1) (tout j1))
      (slot j2) (tout j2)) (slot j3) (tout j3) := by
  funext x
  by_cases h3 : x = slot j3
  · subst h3; rw [install_slot slot hi, Function.update_self]
  · rw [Function.update_of_ne h3]
    by_cases h2 : x = slot j2
    · subst h2; rw [install_slot slot hi, Function.update_self]
    · rw [Function.update_of_ne h2]
      by_cases h1 : x = slot j1
      · subst h1; rw [install_slot slot hi, Function.update_self]
      · rw [Function.update_of_ne h1]
        by_cases hp : ∃ k, slot k = x
        · obtain ⟨k, rfl⟩ := hp
          rw [install_slot slot hi, hkeep k (fun e => h1 (by rw [e])) (fun e => h2 (by rw [e]))
            (fun e => h3 (by rw [e])), it]
        · exact install_other slot A tout x (by intro k hk; exact hp ⟨k, hk⟩)

theorem tcopy_step {U : Nat} (a d e f l : Fin U) (hinj : Function.Injective (![a, d, e, f, l] : Fin 5 → Fin U))
    (n Qa S C : Nat) (hQa : n + 2 ≤ Qa) (hS : n + 2 ≤ S) (hC : 2 * n + 5 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hH : ∀ z, z = a ∨ z = d ∨ z = e ∨ z = f ∨ z = l → H z = 0)
    (ha : A a = ZeroPadding.pad Qa (CompareMachine.word n))
    (hd : A d = List.replicate S false) (he : A e = List.replicate S false) (hf : A f = List.replicate S false)
    (hl : A l = List.replicate C false) :
    Step (tcopyM a d e f l) (4 * n + 12) H A H
      (Function.update (Function.update (Function.update A d (ZeroPadding.pad S (List.replicate n true)))
        e (ZeroPadding.pad S (List.replicate n true))) f (ZeroPadding.pad S (CompareMachine.word n))) := by
  have st := (tcopy_local n Qa S C hQa hS hC).dock (![a, d, e, f, l] : Fin 5 → Fin U) hinj H A
    (by
      intro i; fin_cases i
      · exact hH _ (Or.inl rfl)
      · exact hH _ (Or.inr (Or.inl rfl))
      · exact hH _ (Or.inr (Or.inr (Or.inl rfl)))
      · exact hH _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact hH _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    (by intro i; fin_cases i <;> assumption)
  rw [dockH_existing _ H (fun _ => 0) (by
      intro i; fin_cases i
      · exact hH _ (Or.inl rfl)
      · exact hH _ (Or.inr (Or.inl rfl))
      · exact hH _ (Or.inr (Or.inr (Or.inl rfl)))
      · exact hH _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact hH _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))] at st
  rw [install_update3 _ hinj A
      ![ZeroPadding.pad Qa (CompareMachine.word n), List.replicate S false, List.replicate S false,
        List.replicate S false, List.replicate C false]
      ![ZeroPadding.pad Qa (CompareMachine.word n), ZeroPadding.pad S (List.replicate n true),
        ZeroPadding.pad S (List.replicate n true), ZeroPadding.pad S (CompareMachine.word n),
        List.replicate C false] 1 2 3 (by
      intro i h1 h2 h3; fin_cases i
      · rfl
      · exact absurd rfl h1
      · exact absurd rfl h2
      · exact absurd rfl h3
      · rfl)
    (by intro i; fin_cases i <;> assumption)] at st
  exact st

end
end NearCubicWires.SourceRequest.CurPrims

