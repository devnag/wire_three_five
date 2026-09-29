import Proof.Wire_3_5.UnionMachine.Plan

/-! # C6 front, U2b: the hierarchy request word (P3:3632-3653)

Realizes the input of "Apply the outer PCP to `H`" (P3:3632-3653) as the union's front computes it: the hierarchy
source constructor's input `hierarchyInput H ⟨N, x⟩ = frame x ++ frame (H.time N).bits` (the framed refuter input and
the hierarchy clock in binary), framed once more for the compound native input of the PCPP source
(`PCPPNativeInputFields.word`, the padded source). Two base machines, docked:
* `CloseoutHierarchyRequest.machine kclk C` (`request_run`): from `frame x`, `frame x ++ frame (C·(N^{kclk+2}+1)).bits`;
* `CloseoutCaseTwo.HierarchyFrame.machine` (`frame_run`): from that word, its frame.

Main statement: **`hier_ready`**: a ready run from the framed input to `frame (hierarchyInput H ⟨N, x⟩)` on `hOut`, at
the explicit cost `hierCost`. Paper quantity: the hierarchy's source request. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontHierarchy
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

variable (k : ℕ)

/-- The request machine's tapes. -/
noncomputable abbrev rT : ℕ := RepairSource.CloseoutHierarchyRequest.tapes k

/-- The layout: the request machine's tapes, then five for the framing machine. -/
noncomputable abbrev HT : ℕ := rT k + 5

noncomputable def rs (i : Fin (rT k)) : Fin (HT k) := Fin.castAdd 5 i
noncomputable def fx (j : Fin 5) : Fin (HT k) := Fin.natAdd (rT k) j

theorem rs_inj : Function.Injective (rs k) := by
  intro i j h; exact Fin.ext (by simpa [rs] using congrArg Fin.val h)

/-- The framing machine's slots: its input (tape `0`) is the request word, the rest its own. -/
noncomputable def frs (j : Fin 6) : Fin (HT k) :=
  if h : j.val = 0 then rs k (RepairSource.CloseoutHierarchyRequest.fresh k 0) else fx k ⟨j.val - 1, by omega⟩

theorem frs_inj : Function.Injective (frs k) := by
  intro i j h
  have hv := congrArg Fin.val h
  have h0 : (RepairSource.CloseoutHierarchyRequest.fresh k 0).val < rT k :=
    (RepairSource.CloseoutHierarchyRequest.fresh k 0).isLt
  unfold frs at hv
  split_ifs at hv with hi hj hj <;> simp [rs, fx] at hv <;> apply Fin.ext <;> omega

/-- The output tape: the framing machine's tape `4`. -/
noncomputable def hOut : Fin (HT k) := frs k 4

/-- **The hierarchy word machine.** -/
noncomputable def hierMachine (C : ℕ) :=
  Composition.machine (RecoveryFocus.machine (rs k) (RepairSource.CloseoutHierarchyRequest.machine k C))
    (RecoveryFocus.machine (frs k) CloseoutCaseTwo.HierarchyFrame.machine)

/-- The input: the request machine's input. -/
noncomputable def hInput (bits : List Bool) : Fin (HT k) → List Bool :=
  fun i => if h : i.val < rT k then RepairSource.CloseoutHierarchyRequest.input k bits ⟨i.val, h⟩ else []

/-- The explicit cost. -/
noncomputable def hierCost (C : ℕ) (bits : List Bool) (T : ℕ) : ℕ :=
  RepairSource.CloseoutHierarchyRequest.budget k C bits + 1 +
    CloseoutCaseTwo.HierarchyFrame.budget bits T.bits

/-- **The hierarchy word**: from the framed input, a ready run leaving `frame (hierarchyInput H ⟨N, x⟩)` on `hOut`. -/
theorem hier_ready (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) {N : ℕ} (x : BitInput N) :
    ∃ out : Fin (HT k) → List Bool,
      ClockJoin.ReadyRun (hierMachine k H.coefficient) (hierCost k H.coefficient (List.ofFn x) (H.time N))
        (hInput k (List.ofFn x)) out ∧
      out (hOut k) = RepairOrdinary.frame
        (RepairSource.ProjectionNormalization.HierarchySourceInput.hierarchyInput H ⟨N, x⟩) := by
  have hlen : (List.ofFn x).length = N := List.length_ofFn
  obtain ⟨o1, g1r, h1⟩ := RepairSource.CloseoutHierarchyRequest.request_run H (List.ofFn x)
  rw [hlen] at h1
  have g1 := g1r.focus (rs k) (rs_inj k) (hInput k (List.ofFn x)) (by
    intro j
    simp [hInput, rs])
  set a1 := install (rs k) (hInput k (List.ofFn x)) o1 with ha1
  obtain ⟨o2, g2r, h2, _⟩ := CloseoutCaseTwo.HierarchyFrame.frame_run (List.ofFn x) (H.time N).bits
  have g2 := g2r.focus (frs k) (frs_inj k) a1 (by
    intro j
    by_cases hj : j.val = 0
    · have e : frs k j = rs k (RepairSource.CloseoutHierarchyRequest.fresh k 0) := by simp [frs, hj]
      rw [e, ha1, install_slot _ (rs_inj k), h1]
      have ej : j = 0 := Fin.ext hj
      subst ej
      rfl
    · have e : frs k j = fx k ⟨j.val - 1, by omega⟩ := by simp [frs, hj]
      rw [e, ha1, install_other _ _ _ _ (fun i h => by
        have := congrArg Fin.val h; simp [rs, fx] at this; have := i.isLt; omega)]
      have hge : ¬ (fx k ⟨j.val - 1, by omega⟩).val < rT k := by simp [fx]
      simp only [hInput, hge, dif_neg, not_false_eq_true]
      simp [CloseoutCaseTwo.HierarchyFrame.input, SourceHandoff.sourceTapes, hj])
  refine ⟨_, ClockJoin.join _ _ _ _ _ _ _ g1 g2, ?_⟩
  rw [hOut, install_slot _ (frs_inj k), h2]
  rfl

end NearCubicWires.WireExponent3_5.UnionMachine.FrontHierarchy
