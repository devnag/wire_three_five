import Proof.SourceAssembly.SourceFactorSelDesc
import Proof.SourceAssembly.SourceRequestMonomialSpec

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.Count
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
noncomputable section

/-! ## Primitives -/

theorem sum_local (r s Qa Qb S C : Nat) (hC : r + s + 2 ≤ C) :
    Step ClockUnarySum.machine (2 * (r + s) + 6) (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate r true), ZeroPadding.pad Qb (List.replicate s true),
        List.replicate S false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate r true), ZeroPadding.pad Qb (List.replicate s true),
        ZeroPadding.pad S (List.replicate (r + s) true), List.replicate C false] := by
  have base := (SLoad.MaskFrame.step_of_clockReady (ClockUnarySum.sum_ready r s)).pad ![Qa, Qb, S, C]
  refine (base.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i
    · rfl
    · rfl
    · exact Desc.pad_nil S
    · exact Desc.pad_nil C
  · funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · show ZeroPadding.pad C (List.replicate (r + s + 2) false) = _
      rw [Rewind.Workspace.pad_zeros, Nat.max_eq_left hC]
      rfl

theorem mul_local (d e Qa Qb S C : Nat) (hC : d * (2 * e + 3) + 2 ≤ C) :
    Step ClockUnaryProduct.machine (2 * (d * (2 * e + 3) + 2) + 2) (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate d true), ZeroPadding.pad Qb (CompareMachine.word e),
        List.replicate S false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate d true), ZeroPadding.pad Qb (CompareMachine.word e),
        ZeroPadding.pad S (List.replicate (d * e) true), List.replicate C false] := by
  obtain ⟨rc, hrun, t0, t1, t2, t3, hh, hs⟩ := ClockUnaryProduct.product_run d e
  have hin : (Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
      ![List.replicate d true, false :: List.replicate e true, []] (fun _ : Fin 1 => [])) =
      (![List.replicate d true, CompareMachine.word e, [], []] : Fin 4 → List Bool) := by
    funext i
    fin_cases i <;> rfl
  rw [hin] at hrun
  have hready : ClockJoin.ReadyRun ClockUnaryProduct.machine (2 * (d * (2 * e + 3) + 2) + 2)
      ![List.replicate d true, CompareMachine.word e, [], []]
      ![List.replicate d true, CompareMachine.word e, List.replicate (d * e) true,
        List.replicate (d * (2 * e + 3) + 2) false] := by
    refine ⟨rc, hrun, ?_, hh, le_of_eq hs⟩
    funext i
    fin_cases i
    · exact t0
    · exact t1
    · exact t2
    · exact t3
  have base := (SLoad.MaskFrame.step_of_clockReady hready).pad ![Qa, Qb, S, C]
  refine (base.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i
    · rfl
    · rfl
    · exact Desc.pad_nil S
    · exact Desc.pad_nil C
  · funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · show ZeroPadding.pad C (List.replicate (d * (2 * e + 3) + 2) false) = _
      rw [Rewind.Workspace.pad_zeros, Nat.max_eq_left hC]
      rfl

theorem word_local (x : Bool) (n Qa R C : Nat) (hR : n + x.toNat + 2 ≤ R) (hC : n + 3 ≤ C) :
    Step (DimensionTemplate.machine x) (2 * n + 8) (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate n true), List.replicate R false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate n true), ZeroPadding.pad R (CompareMachine.word (n + x.toNat)),
        List.replicate C false] := by
  have base := (SLoad.MaskFrame.step_of_clockReady (DimensionTemplate.ready x n)).pad ![Qa, R, C]
  refine (base.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i
    · rfl
    · exact Desc.pad_nil R
    · exact Desc.pad_nil C
  · funext i
    fin_cases i
    · rfl
    · show ZeroPadding.pad R (UnaryTemplate.tape (n + x.toNat)) = _
      rw [ExtDecompositionBatch.pad_template R (n + x.toNat) hR]
      rfl
    · show ZeroPadding.pad C (List.replicate (n + 3) false) = _
      rw [Rewind.Workspace.pad_zeros, Nat.max_eq_left hC]
      rfl

/-- Docked sum `![a, b, dst, log]`. -/
def sumM {U : Nat} (a b d l : Fin U) := RecoveryFocus.machine (![a, b, d, l] : Fin 4 → Fin U) ClockUnarySum.machine
/-- Docked product `![a, b, dst, log]` (`b` holds `word e`). -/
def mulM {U : Nat} (a b d l : Fin U) :=
  RecoveryFocus.machine (![a, b, d, l] : Fin 4 → Fin U) ClockUnaryProduct.machine
/-- Docked unary→word `![a, dst, log]` (`+ x.toNat`). -/
def wordM {U : Nat} (x : Bool) (a d l : Fin U) :=
  RecoveryFocus.machine (![a, d, l] : Fin 3 → Fin U) (DimensionTemplate.machine x)

theorem sum_step {U : Nat} (a b d l : Fin U) (h1 : a ≠ b) (h2 : a ≠ d) (h3 : a ≠ l) (h4 : b ≠ d)
    (h5 : b ≠ l) (h6 : d ≠ l) (r s Qa Qb S C : Nat) (hC : r + s + 2 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ x, x = a ∨ x = b ∨ x = d ∨ x = l → H x = 0)
    (ha : A a = ZeroPadding.pad Qa (List.replicate r true)) (hb : A b = ZeroPadding.pad Qb (List.replicate s true))
    (hd : A d = List.replicate S false) (hl : A l = List.replicate C false) :
    Step (sumM a b d l) (2 * (r + s) + 6) H A H
      (Function.update A d (ZeroPadding.pad S (List.replicate (r + s) true))) :=
  SLoad.step_update (sum_local r s Qa Qb S C hC) 2
    (by
      intro i hi
      fin_cases i
      · rfl
      · rfl
      · exact absurd rfl hi
      · rfl)
    _ (SLoad.MaskFrame.quad_injective a b d l h1 h2 h3 h4 h5 h6) H A
    (by
      intro i
      fin_cases i
      · exact hH _ (Or.inl rfl)
      · exact hH _ (Or.inr (Or.inl rfl))
      · exact hH _ (Or.inr (Or.inr (Or.inl rfl)))
      · exact hH _ (Or.inr (Or.inr (Or.inr rfl))))
    (by
      intro i
      fin_cases i
      · exact ha
      · exact hb
      · exact hd
      · exact hl)

theorem mul_step {U : Nat} (a b d l : Fin U) (h1 : a ≠ b) (h2 : a ≠ d) (h3 : a ≠ l) (h4 : b ≠ d)
    (h5 : b ≠ l) (h6 : d ≠ l) (x e Qa Qb S C : Nat) (hC : x * (2 * e + 3) + 2 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ y, y = a ∨ y = b ∨ y = d ∨ y = l → H y = 0)
    (ha : A a = ZeroPadding.pad Qa (List.replicate x true)) (hb : A b = ZeroPadding.pad Qb (CompareMachine.word e))
    (hd : A d = List.replicate S false) (hl : A l = List.replicate C false) :
    Step (mulM a b d l) (2 * (x * (2 * e + 3) + 2) + 2) H A H
      (Function.update A d (ZeroPadding.pad S (List.replicate (x * e) true))) :=
  SLoad.step_update (mul_local x e Qa Qb S C hC) 2
    (by
      intro i hi
      fin_cases i
      · rfl
      · rfl
      · exact absurd rfl hi
      · rfl)
    _ (SLoad.MaskFrame.quad_injective a b d l h1 h2 h3 h4 h5 h6) H A
    (by
      intro i
      fin_cases i
      · exact hH _ (Or.inl rfl)
      · exact hH _ (Or.inr (Or.inl rfl))
      · exact hH _ (Or.inr (Or.inr (Or.inl rfl)))
      · exact hH _ (Or.inr (Or.inr (Or.inr rfl))))
    (by
      intro i
      fin_cases i
      · exact ha
      · exact hb
      · exact hd
      · exact hl)

theorem word_step {U : Nat} (x : Bool) (a d l : Fin U) (h1 : a ≠ d) (h2 : a ≠ l) (h3 : d ≠ l)
    (n Qa R C : Nat) (hR : n + x.toNat + 2 ≤ R) (hC : n + 3 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ y, y = a ∨ y = d ∨ y = l → H y = 0)
    (ha : A a = ZeroPadding.pad Qa (List.replicate n true))
    (hd : A d = List.replicate R false) (hl : A l = List.replicate C false) :
    Step (wordM x a d l) (2 * n + 8) H A H
      (Function.update A d (ZeroPadding.pad R (CompareMachine.word (n + x.toNat)))) :=
  SLoad.step_update (word_local x n Qa R C hR hC) 1
    (by
      intro i hi
      fin_cases i
      · rfl
      · exact absurd rfl hi
      · rfl)
    _ (SLoad.triple_injective a d l h1 h2 h3) H A
    (by
      intro i
      fin_cases i
      · exact hH _ (Or.inl rfl)
      · exact hH _ (Or.inr (Or.inl rfl))
      · exact hH _ (Or.inr (Or.inr rfl)))
    (by
      intro i
      fin_cases i
      · exact ha
      · exact hd
      · exact hl)

/-- A flag `[b]` read as the unary number `b.toNat`. -/
theorem flag_unary (Q : Nat) (b : Bool) :
    ZeroPadding.pad Q [b] = ZeroPadding.pad (max Q 1) (List.replicate b.toNat true) := by
  cases b
  · simp only [ZeroPadding.pad, Bool.toNat_false, List.replicate_zero, List.nil_append, List.length_nil,
      List.length_singleton, Nat.sub_zero]
    rw [show max Q 1 = (Q - 1) + 1 by omega, List.replicate_succ]
    rfl
  · simp only [ZeroPadding.pad, Bool.toNat_true, List.replicate_one, List.length_singleton]
    congr 2
    omega

theorem word0_step {U : Nat} (a d l : Fin U) (h1 : a ≠ d) (h2 : a ≠ l) (h3 : d ≠ l)
    (n Qa R C : Nat) (hR : n + 2 ≤ R) (hC : n + 3 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ y, y = a ∨ y = d ∨ y = l → H y = 0)
    (ha : A a = ZeroPadding.pad Qa (List.replicate n true))
    (hd : A d = List.replicate R false) (hl : A l = List.replicate C false) :
    Step (wordM false a d l) (2 * n + 8) H A H
      (Function.update A d (ZeroPadding.pad R (CompareMachine.word n))) :=
  word_step false a d l h1 h2 h3 n Qa R C hR hC H A hH ha hd hl

/-! ## The moment phase: `N = JL·JL` -/

/-! ## The clause phase: `N = a + (b + a·b)`, `a = JL + [nL]`, `b = JR + [nR]` -/

/-! ## The penalty phase: one side, `penLen s J`, switched on the auxiliary flag

Side universe `Fin 10`: `0` `1^J` · `1` aux flag `[!s]` · `2` `word J` · `3` `J²` · `4` `word J²` (aux) / `1` (sys) ·
`5` `J³` · `6` `J²·J²` · `7` partial sum · `8` result · `9` log. -/

theorem read_flag (Q : Nat) (b : Bool) : readTapeBit (ZeroPadding.pad Q [b]) 0 = b := by
  simp [ZeroPadding.pad, readTapeBit]



/-! ## The per-phase stage at `siteLen` -/

/-! ## At the consumer's quantity -/

section consumer
open NearCubicWires.SourceInterfaces NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairSource.CloseoutFinal

end consumer


end
end NearCubicWires.SourceFactorSel.Count
