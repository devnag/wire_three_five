import Proof.Wire_3_5.UnionMachine.FrontWidth

/-! # C6 front, U2: the native width's run at an explicit cost

`FrontWidthTail.tail_ready` and `FrontWidth.qMachine_ready` state their cost existentially; the front's
time needs it explicitly. This module re-runs the same proofs (the same machines, the same stages) and names the sum:
* **`tailCost`**, **`tail_ready_c`**; **`qCost`**, **`qMachine_ready_c`**.

Paper quantity: `q(N)` (P3:3637-3640), at the machine's explicit time. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontWidthCost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWidthTail (tailMachine tailInput tailOf tailOf_eq)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWidth

/-- The tail's cost. -/
noncomputable def tailCost (A y : ℕ) : ℕ :=
  (2 * wordTwo.length + 2) + 1 + ((2 * (y + 2) + 6) + 1 + (RepairSource.CloseoutSchedule.Clog.budget (y + 2) + 1 +
    ((2 * Nat.clog 2 (y + 2) + 6) + 1 + ((2 * (wordA A).length + 2) + 1 +
      (UWalkNumbers.productCost (Nat.clog 2 (y + 2) + 1) A + 1 + (2 * (y + (Nat.clog 2 (y + 2) + 1) * A) + 6))))))

/-- **The tail at its explicit cost** (`FrontWidthTail.tail_ready`'s proof). -/
theorem tail_ready_c (A y : ℕ) : ∃ out : Fin 28 → List Bool,
    ClockJoin.ReadyRun (tailMachine A) (tailCost A y) (tailInput y) out ∧ out 3 = List.replicate y true ∧
      out 26 = List.replicate (tailOf A y) true := by
  set a2 := tailInput y with ha2
  -- step 3: the fixed word `1^2` on tapes 5, 6
  have h3 := (UWalkNumbers.fixed_ready wordTwo).focus slotsF2 (by decide) a2 (by
    intro j; fin_cases j <;> rfl)
  set a3 := install slotsF2 a2 ![wordTwo, List.replicate wordTwo.length false] with ha3
  -- step 4: the sum `y + 2` on tapes 3, 5, 7, 8
  have h4 := (ClockUnarySum.sum_ready y 2).focus slotsS1 (by decide) a3 (by
    intro j; fin_cases j
    · show a3 3 = _; rw [ha3, install_other _ _ _ _ (by decide)]; rfl
    · show a3 5 = _; rw [ha3, show (5 : Fin 28) = slotsF2 0 from rfl, install_slot _ (by decide)]; rfl
    · show a3 7 = _; rw [ha3, install_other _ _ _ _ (by decide)]; rfl
    · show a3 8 = _; rw [ha3, install_other _ _ _ _ (by decide)]; rfl)
  set a4 := install slotsS1 a3 ![List.replicate y true, List.replicate 2 true,
    List.replicate (y + 2) true, List.replicate (y + 2 + 2) false] with ha4
  -- step 5: `⌈log₂(y+2)⌉` on the clog slots; its output word is on tape 18
  have hbelow : ∀ i : Fin 28, 9 ≤ i.val → i.val ≤ 25 → a4 i = [] := by
    intro i h9 h25
    have e0 : ∀ j, slotsS1 j ≠ i := by
      intro j; fin_cases j <;> (intro h; have := congrArg Fin.val h; simp [slotsS1] at this; omega)
    have e1 : ∀ j, slotsF2 j ≠ i := by
      intro j; fin_cases j <;> (intro h; have := congrArg Fin.val h; simp [slotsF2] at this; omega)
    rw [ha4, install_other _ _ _ _ e0, ha3, install_other _ _ _ _ e1]
    simp [a2, tailInput]; omega
  obtain ⟨outC, hC, hC10⟩ := RepairSource.CloseoutSchedule.Clog.clog_run (y + 2) (by omega)
  have h5 := hC.focus slotsC (by decide) a4 (by
    intro j
    by_cases hj : j = 0
    · subst hj
      show a4 7 = _
      rw [ha4, show (7 : Fin 28) = slotsS1 2 from rfl, install_slot _ (by decide)]
      simp [RepairSource.CloseoutSchedule.Clog.input]
    · have hv : 9 ≤ (slotsC j).val ∧ (slotsC j).val ≤ 25 := by fin_cases j <;> simp_all [slotsC]
      rw [hbelow _ hv.1 hv.2]
      simp [RepairSource.CloseoutSchedule.Clog.input, hj])
  set a5 := install slotsC a4 outC with ha5
  -- step 6: `1^{z+1}` on tape 20 from the word `0 1^z` on tape 18
  have h6 := (UWalkUnary.ready false true 0 (Nat.clog 2 (y + 2))).focus slotsU (by decide) a5 (by
    intro j; fin_cases j
    · show a5 18 = _
      rw [ha5, show (18 : Fin 28) = slotsC 10 from rfl, install_slot _ (by decide), hC10]
      simp [UWalkUnary.input, UWalkUnary.source]
    · show a5 20 = _; rw [ha5, install_other _ _ _ _ (by decide), hbelow _ (by decide) (by decide)]; rfl
    · show a5 21 = _; rw [ha5, install_other _ _ _ _ (by decide), hbelow _ (by decide) (by decide)]; rfl)
  set a6 := install slotsU a5 (UWalkUnary.result false true 0 (Nat.clog 2 (y + 2))) with ha6
  -- step 7: the fixed word `0 1^A` on tapes 22, 23
  have h7 := (UWalkNumbers.fixed_ready (wordA A)).focus slotsF3 (by decide) a6 (by
    intro j; fin_cases j
    · show a6 22 = _
      rw [ha6, install_other _ _ _ _ (by decide), ha5, install_other _ _ _ _ (by decide),
        hbelow _ (by decide) (by decide)]
    · show a6 23 = _
      rw [ha6, install_other _ _ _ _ (by decide), ha5, install_other _ _ _ _ (by decide),
        hbelow _ (by decide) (by decide)])
  set a7 := install slotsF3 a6 ![wordA A, List.replicate (wordA A).length false] with ha7
  -- step 8: the product `(z+1)·A` on tapes 20, 22, 24, 25
  have h8 := (UWalkNumbers.product_ready (Nat.clog 2 (y + 2) + 1) A).focus slotsP2 (by decide) a7 (by
    intro j; fin_cases j
    · show a7 20 = _
      rw [ha7, install_other _ _ _ _ (by decide), ha6, show (20 : Fin 28) = slotsU 1 from rfl,
        install_slot _ (by decide)]
      simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead, UWalkNumbers.productInput]
    · show a7 22 = _; rw [ha7, show (22 : Fin 28) = slotsF3 0 from rfl, install_slot _ (by decide)]; rfl
    · show a7 24 = _
      rw [ha7, install_other _ _ _ _ (by decide), ha6, install_other _ _ _ _ (by decide), ha5,
        install_other _ _ _ _ (by decide), hbelow _ (by decide) (by decide)]; rfl
    · show a7 25 = _
      rw [ha7, install_other _ _ _ _ (by decide), ha6, install_other _ _ _ _ (by decide), ha5,
        install_other _ _ _ _ (by decide), hbelow _ (by decide) (by decide)]; rfl)
  set a8 := install slotsP2 a7 (UWalkNumbers.productOutput (Nat.clog 2 (y + 2) + 1) A) with ha8
  -- step 9: the sum `y + (z+1)·A` on tapes 3, 24, 26, 27
  have hx3 : a8 3 = List.replicate y true := by
    rw [ha8, install_other _ _ _ _ (by decide), ha7, install_other _ _ _ _ (by decide), ha6,
      install_other _ _ _ _ (by decide), ha5, install_other _ _ _ _ (by decide), ha4,
      show (3 : Fin 28) = slotsS1 0 from rfl, install_slot _ (by decide)]
    rfl
  have h26 : ∀ i : Fin 28, 26 ≤ i.val → a8 i = [] := by
    intro i h
    have e : ∀ {m : ℕ} (s : Fin m → Fin 28), (∀ j, (s j).val < 26) → ∀ j, s j ≠ i := by
      intro m s hs j hj; have := hs j; rw [hj] at this; omega
    rw [ha8, install_other _ _ _ _ (e _ (by decide)), ha7, install_other _ _ _ _ (e _ (by decide)), ha6,
      install_other _ _ _ _ (e _ (by decide)), ha5, install_other _ _ _ _ (e _ (by decide)), ha4,
      install_other _ _ _ _ (e _ (by decide)), ha3, install_other _ _ _ _ (e _ (by decide))]
    simp [a2, tailInput]; omega
  have h9 := (ClockUnarySum.sum_ready y ((Nat.clog 2 (y + 2) + 1) * A)).focus slotsS2 (by decide) a8 (by
    intro j; fin_cases j
    · exact hx3
    · show a8 24 = _; rw [ha8, show (24 : Fin 28) = slotsP2 2 from rfl, install_slot _ (by decide)]; rfl
    · exact h26 26 (by decide)
    · exact h26 27 (by decide))
  refine ⟨_, ClockJoin.enlarge _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ h3 (ClockJoin.join _ _ _ _ _ _ _ h4
    (ClockJoin.join _ _ _ _ _ _ _ h5 (ClockJoin.join _ _ _ _ _ _ _ h6
    (ClockJoin.join _ _ _ _ _ _ _ h7 (ClockJoin.join _ _ _ _ _ _ _ h8 h9)))))) (le_of_eq (by unfold tailCost; rfl)),
    ?_, ?_⟩
  · rw [show (3 : Fin 28) = slotsS2 0 from rfl, install_slot _ (by decide)]
    rfl
  · rw [show (26 : Fin 28) = slotsS2 2 from rfl, install_slot _ (by decide)]
    rfl

/-- The width's cost. -/
noncomputable def qCost (k A : ℕ) (x : List Bool) : ℕ :=
  HierarchyFromInput.budget (k + 2) 1 x + 1 + ((11 * HierarchyBinary.width 1 (k + 2) x.length + 20) + 1 + (1 + 1 +
    (FrontClog.clogCost (HierarchyBinary.width 1 (k + 2) x.length) + 1 +
      tailCost A (Nat.clog 2 (x.length ^ (k + 2))))))

/-- **The width at its explicit cost** (`FrontWidth.qMachine_ready`'s proof). -/
theorem qMachine_ready_c (k A : ℕ) (x : List Bool) :
    ∃ out : Fin (QT k) → List Bool, ClockJoin.ReadyRun (qMachine k A) (qCost k A x) (qInput k x) out ∧
      out (qOut k) = List.replicate (Ledger.nativeWidth k A x.length) true := by
  set N := x.length with hN
  set W := HierarchyBinary.width 1 (k + 2) N with hW
  -- stage 1: base's hierarchy input machine
  obtain ⟨r1, hr1, hout1, h11, _, hh1, hs1⟩ := HierarchyFromInput.from_input_run (k + 2) 1 (hD k) x
  have hin1 : ∀ j, qInput k x (hs k j) = HierarchyFromInput.input (k + 2) x j := by
    intro j
    simp only [qInput, inT, HierarchyFromInput.input]
    by_cases hj : j.val = 2
    · have e : j = HierarchyFromInput.field (k + 2) 2 := Fin.ext (by simp [HierarchyFromInput.field, hj])
      subst e
      simp [HierarchyFromInput.field]
    · have hne : hs k j ≠ hs k (HierarchyFromInput.field (k + 2) 2) := by
        intro h; apply hj; have := congrArg Fin.val h; simpa [hs_val, HierarchyFromInput.field] using this
      simp [hne, hj]
  have g1 := ClockJoin.ReadyRun.focus (⟨r1, hr1, rfl, hh1, hs1⟩ :
      ClockJoin.ReadyRun (HierarchyFromInput.machine (k + 2) 1 (hD k)) (HierarchyFromInput.budget (k + 2) 1 x)
        (HierarchyFromInput.input (k + 2) x) r1.final.tapes) (hs k) (hs_inj k) (qInput k x) hin1
  set a1 := install (hs k) (qInput k x) r1.final.tapes with ha1
  have a1_hs : ∀ j, a1 (hs k j) = r1.final.tapes j := fun j => install_slot _ (hs_inj k) _ _ j
  have a1_ge : ∀ i : Fin (QT k), hT k ≤ i.val → a1 i = [] := by
    intro i hi
    have hne : ∀ j, hs k j ≠ i := by
      intro j h
      have h1 := congrArg Fin.val h
      have h2 := j.isLt
      rw [hs_val] at h1
      omega
    rw [ha1, install_other _ _ _ _ hne]
    have hin : i ≠ inT k := by
      intro h
      have h1 := congrArg Fin.val h
      simp only [inT, hs_val, HierarchyFromInput.field] at h1
      have h35 : 35 ≤ hT k := HierarchyFromInput.tapes_lower (k + 2)
      omega
    simp [qInput, hin]
  -- stage 2: blank registers
  have hca : cntT k ≠ auxT k := hs_ne_ex k _ _
  have hct : tgt k (cntT k) = false := by
    have h35 : 35 ≤ hT k := HierarchyFromInput.tapes_lower (k + 2)
    simp [tgt, cntT, hs_val, HierarchyFromInput.field]
    omega
  have hat : tgt k (auxT k) = false := by simp [tgt, auxT, FrontWidth.ex_val]
  have hside : ∀ i, FrontFill.side (auxT k) (tgt k) i → hT k ≤ i.val := by
    intro i hi
    rcases hi with h | h
    · simp [tgt] at h; omega
    · rw [h]; simp [auxT, FrontWidth.ex_val]
  have e2 := FrontFill.fillP_exec (cntT k) (auxT k) (tgt k) (fun _ => 0) a1 hca hct hat W
    (by rw [cntT, a1_hs, h11]) (fun _ _ => rfl) (fun i hi => a1_ge i (hside i hi))
  have hH2 : (FrontFill.stB (cntT k) (auxT k) (tgt k) (fun _ => 0) a1 W 0).H = fun _ => 0 := by
    funext i; simp only [FrontFill.stB]; split_ifs <;> omega
  have g2 : ClockJoin.ReadyRun (FrontFill.fillP (cntT k) (auxT k) (tgt k)).compile (11 * W + 20) a1
      (FrontFill.stB (cntT k) (auxT k) (tgt k) (fun _ => 0) a1 W 0).A := by
    have := Exec.step e2
    rw [hH2] at this
    exact ready_of_step this
  set a2 := (FrontFill.stB (cntT k) (auxT k) (tgt k) (fun _ => 0) a1 W 0).A with ha2
  have a2_other : ∀ i, ¬ FrontFill.side (auxT k) (tgt k) i → a2 i = a1 i := by
    intro i hi
    simp only [ha2, FrontFill.stB]
    have ht : tgt k i = false := by
      cases h : tgt k i
      · rfl
      · exact absurd (Or.inl h) hi
    have hx : i ≠ auxT k := fun h => hi (Or.inr h)
    simp [ht, hx]
  have a2_reg : ∀ i, tgt k i = true → a2 i = List.replicate (2 * W + 3) false := by
    intro i hi; simp [ha2, FrontFill.stB, hi]
  -- stage 3: the cell
  have e3 := Exec.act (⟨fun _ => 0, a2⟩ : Bank (QT k)) (fun i => if i = cellT k then some false else none)
    (fun _ => .stay)
  set a3 := ((⟨fun _ => 0, a2⟩ : Bank (QT k)).act (fun i => if i = cellT k then some false else none)
    (fun _ => .stay)).A with ha3
  have g3 : ClockJoin.ReadyRun (cellP k).compile 1 a2 a3 := by
    have := Exec.step e3
    exact ready_of_step this
  have hcell_side : ¬ FrontFill.side (auxT k) (tgt k) (cellT k) := by
    rintro (h | h)
    · simp [tgt, cellT, FrontWidth.ex_val] at h
    · exact absurd (congrArg Fin.val h) (by simp [cellT, auxT, FrontWidth.ex_val])
  have a3_cell : a3 (cellT k) = [false] := by
    simp only [ha3, Bank.act, if_true]
    rw [a2_other _ hcell_side, a1_ge _ (by simp [cellT, FrontWidth.ex_val])]
    rfl
  have a3_other : ∀ i, i ≠ cellT k → a3 i = a2 i := by
    intro i hi; simp [ha3, Bank.act, hi]
  have a3_ex : ∀ j : Fin 37, 7 ≤ j.val → j.val ≠ 7 → a3 (ex k j) = [] := by
    intro j h1 h2
    rw [a3_other _ (fun h => h2 (by have := congrArg Fin.val h; simp [cellT, FrontWidth.ex_val] at this; omega))]
    rw [a2_other _ (by
      rintro (h | h)
      · simp [tgt, FrontWidth.ex_val] at h; omega
      · have := congrArg Fin.val h; simp [auxT, FrontWidth.ex_val] at this; omega)]
    exact a1_ge _ (by simp [FrontWidth.ex_val])
  -- stage 4: `⌈log₂ N^{k+2}⌉` on the register bank
  set cap := 2 * W + 2 with hcap
  set σ0 : FrontClog.CS := ⟨fun _ => 0, ![frame (binary W (N ^ (k + 2) + 1)), [], []], fun _ => 0, false⟩
    with hσ0
  obtain ⟨τ, hτ, hY, hsh, hval⟩ := FrontClog.clogP_spec cap W (N ^ (k + 2)) σ0 (width_pos k N) (width_fits k N)
    le_rfl rfl rfl rfl rfl rfl rfl (fun _ => rfl)
  have hstep4 := (WExec.exec cap hτ).step
  have hH0 : (wenc cap σ0).H = fun _ => 0 := by
    funext j; simp only [wenc]; split <;> rfl
  have hHτ : (wenc cap τ).H = fun _ => 0 := by
    funext j; simp only [wenc]; split <;> simp [hsh, hval]
  rw [hH0, hHτ] at hstep4
  have g4r := ready_of_step hstep4
  have hin4 : ∀ j, a3 (wsl k j) = (wenc cap σ0).A j := by
    intro j
    fin_cases j
    · show a3 (outT k) = _
      rw [a3_other _ (fun h => by have := congrArg Fin.val h; have := outT_lt k; simp [cellT, FrontWidth.ex_val] at *; omega)]
      rw [a2_other _ (by
        rintro (h | h)
        · have := outT_lt k; simp [tgt] at h; omega
        · have := congrArg Fin.val h; have := outT_lt k; simp [auxT, FrontWidth.ex_val] at *; omega)]
      rw [outT, a1_hs, hout1, one_mul]
      rfl
    · show a3 (cellT k) = _; rw [a3_cell]; rfl
    · show a3 (ex k 8) = _; rw [a3_ex 8 (by decide) (by decide)]; rfl
    · show a3 (ex k 9) = _; rw [a3_ex 9 (by decide) (by decide)]; rfl
    all_goals
      (show a3 (ex k _) = _
       rw [a3_other _ (fun h => by have := congrArg Fin.val h; simp [cellT, FrontWidth.ex_val] at this),
         a2_reg _ (by simp [tgt, FrontWidth.ex_val])]
       simp [wenc, role, σ0, regTape_zero, cap])
  have g4 := g4r.focus (wsl k) (wsl_inj k) a3 hin4
  set a4 := install (wsl k) a3 (wenc cap τ).A with ha4
  have a4_Y : a4 (YT k) = List.replicate (Nat.clog 2 (N ^ (k + 2))) true := by
    have e : YT k = wsl k 3 := by apply Fin.ext; simp [wsl, YT, FrontWidth.ex_val]
    rw [e, ha4, install_slot _ (wsl_inj k)]
    simp [wenc, role, hY]
  have a4_ge : ∀ i : Fin (QT k), hT k + 10 ≤ i.val → a4 i = [] := by
    intro i hi
    rw [ha4, install_other _ _ _ _ (wsl_image k i hi)]
    have hq : QT k = hT k + 37 := rfl
    have hi' : i = ex k ⟨i.val - hT k, by have := i.isLt; omega⟩ := by
      apply Fin.ext; simp [FrontWidth.ex_val]; omega
    rw [hi']
    exact a3_ex _ (by simp; omega) (by simp; omega)
  -- stage 5: the tail
  obtain ⟨out5, g5r, _, h526⟩ := tail_ready_c A (Nat.clog 2 (N ^ (k + 2)))
  have hin5 : ∀ j, a4 (tsl k j) = FrontWidthTail.tailInput (Nat.clog 2 (N ^ (k + 2))) j := by
    intro j
    by_cases h3 : j.val = 3
    · have e : tsl k j = YT k := by simp [tsl, h3]
      rw [e, a4_Y]; simp [FrontWidthTail.tailInput, h3]
    · rw [a4_ge _ (by rw [tsl_val]; split_ifs <;> omega)]
      simp [FrontWidthTail.tailInput, h3]
  have g5 := g5r.focus (tsl k) (tsl_inj k) a4 hin5
  refine ⟨_, ClockJoin.enlarge _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ g1 (ClockJoin.join _ _ _ _ _ _ _ g2
    (ClockJoin.join _ _ _ _ _ _ _ g3 (ClockJoin.join _ _ _ _ _ _ _ g4 g5)))) (le_of_eq (by unfold qCost; rfl)), ?_⟩
  rw [qOut, install_slot _ (tsl_inj k), h526, FrontWidthTail.tailOf_eq]
  rfl

end NearCubicWires.WireExponent3_5.UnionMachine.FrontWidthCost
