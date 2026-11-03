import Proof.Wire_3_5.UnionMachine.PlanBase
import Proof.CaseAnalysis.FinalLengthGate

/-! # C6, U0: the length gate and the rejecting bank (P3:3675-3680)

Realizes "At the finitely many source lengths where this fixed envelope exceeds the refuter's `N/10` guess budget, the
machine rejects outright" (P3:3675-3680) inside the front of the union worker (M4 `Plan.FrontAt`): below its onset `C`
the front reaches the loop's REJECTING bank (the empty call table, the rejecting accumulators `(1,0,0,0,0,0)`,
capacity `1`, no scratch), on which the verified loop stops at once and the decision rejects; at lengths `≥ C` it runs
the rest of the front from the refuter's tapes with a set flag.

* `rejOut`, `rejKept`, `decision_rej`: the rejecting output and its decision (`false`);
* `rejP` (two simultaneous actions on the nine kept tapes of the loop bank: table `[false]`, cell `[false]`, the
  rounding register `regTape 1 0`, the accumulators `regTape 1 (1,0,0,0,0,0)`), `rejM` (docked at those tapes),
  **`rej_step`**: from blank loop tapes it leaves exactly the rejecting bank on every loop tape;
* **`gateThen C acc`** = base's `C10LengthGate.counter` (reads the framed input two cells at a time) followed by a
  two-way branch on its flag (FinalPass's `iteMachine`): **`gate_reject`** (length `< C`: the rejecting bank within
  `2N + 6` steps) and **`gate_pass`** (length `≥ C`: `acc` from the refuter's tapes with the flag set, after `4C+2`
  steps).

Donors: base `C10LengthGate.counter` / `counter_reject` / `counter_pass_clean` (the gate), FinalPass `Prog`,
`iteMachine`, `ite_branch_step` (the branch and the writer), base `Step.dock` (docking). Paper quantity of the main
statements: the rejecting output of the front below its onset (`rejOut`, `decisionOf rejAcc = false`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontGate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.RepairSource.CloseoutFinal

/-! ## The rejecting output -/

/-- The rejecting accumulators: `V⁺ = 1 > 0 = V⁻`. -/
def rejAcc : Fin 6 → ℕ := ![1, 0, 0, 0, 0, 0]

theorem decision_rej : decisionOf rejAcc = false := by decide

/-- The loop's kept data on the rejecting bank. -/
def rejKept : Sched.Kept := ⟨[false], 0, 0, rejAcc⟩

section Out
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

/-- **The rejecting output of the front**: the empty table, the rejecting accumulators, capacity `1`, no scratch. -/
def rejOut : FrontOut I := ⟨[], rejAcc, 0, 1, 0, 0, 0, 0⟩

theorem accOf_nil (p : ℕ) (acc0 : Fin 6 → ℕ) (j : ℕ) : Sched.accOf P p acc0 [] j = acc0 := by
  funext i; simp [Sched.accOf]

theorem rejOut_kept : (rejOut (I := I)).kept P = rejKept := by
  simp [FrontOut.kept, rejOut, rejKept, Sched.KOf, Sched.tblOf, Sched.posOf, accOf_nil,
    UnionMachine.Entry.tableWord]

theorem rejOut_keptEnd : (rejOut (I := I)).keptEnd P = rejKept := by
  simp [FrontOut.keptEnd, rejOut, rejKept, Sched.KOf, Sched.tblOf, Sched.posOf, accOf_nil,
    UnionMachine.Entry.tableWord]

end Out

/-! ## The rejecting bank's writer -/

/-- The nine kept tapes of the loop bank written by the rejecting writer: table, cell, rounding register, the six
accumulators. -/
def kk : Fin 9 → Fin 31 := ![0, 1, 13, 24, 25, 26, 27, 28, 29]

theorem kk_inj : Function.Injective kk := by decide

/-- First action: write `false` on all nine tapes, step right on the seven registers. -/
def w1 : Fin 9 → Option Bool := fun _ => some false
def m1 : Fin 9 → HeadMove := fun j => if 2 ≤ j.val then .right else .stay

/-- Second action: write the registers' second cell (`true` for the first accumulator), step back left except there. -/
def w2 : Fin 9 → Option Bool := fun j => if j.val < 2 then none else if j.val = 3 then some true else some false
def m2 : Fin 9 → HeadMove := fun j => if j.val < 2 ∨ j.val = 3 then .stay else .left

/-- **The rejecting writer** on the nine kept tapes. -/
def rejP : Prog 9 := .seq (.act w1 m1) (.act w2 m2)

/-- The writer's final heads and tapes. -/
def rejH : Fin 9 → ℕ := fun j => if j.val = 3 then 1 else 0
def rejA : Fin 9 → List Bool := fun j =>
  if j.val < 2 then [false] else if j.val = 3 then [false, true] else [false, false]

theorem rejP_exec : Exec rejP ⟨fun _ => 0, fun _ => []⟩ ⟨rejH, rejA⟩ 3 := by
  have h := Exec.seq (Exec.act (⟨fun _ => 0, fun _ => []⟩ : Bank 9) w1 m1)
    (Exec.act ((⟨fun _ => 0, fun _ => []⟩ : Bank 9).act w1 m1) w2 m2)
  have e : ((⟨fun _ => 0, fun _ => []⟩ : Bank 9).act w1 m1).act w2 m2 = ⟨rejH, rejA⟩ := by
    have hH : (((⟨fun _ => 0, fun _ => []⟩ : Bank 9).act w1 m1).act w2 m2).H = rejH := by
      funext j; fin_cases j <;> rfl
    have hA : (((⟨fun _ => 0, fun _ => []⟩ : Bank 9).act w1 m1).act w2 m2).A = rejA := by
      funext j; fin_cases j <;> rfl
    cases h' : ((⟨fun _ => 0, fun _ => []⟩ : Bank 9).act w1 m1).act w2 m2 with
    | mk H A => rw [h'] at hH hA; simp only at hH hA; subst hH hA; rfl
  rw [e] at h
  exact h

section Dock
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)

/-- The writer's slots: the nine kept tapes of the loop bank inside the worker. -/
noncomputable def rs9 (j : Fin 9) : Fin (NW P tf) := Plan.lp P tf (Scrub.inner (Sched.fx P (kk j)))

theorem inner_inj {u : ℕ} : Function.Injective (Scrub.inner (t := u)) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [Scrub.inner, Fin.val_castAdd] at this
  exact Fin.ext this

theorem rs9_inj : Function.Injective (rs9 P tf) :=
  (Plan.lp_inj P tf).comp (inner_inj.comp ((Sched.fx_inj P).comp kk_inj))

/-- **The rejecting writer, docked.** -/
noncomputable def rejM : Machine (NW P tf) rejP.size := RecoveryFocus.machine (rs9 P tf) rejP.compile

/-- The rejecting bank's loop tapes outside the nine kept ones are blank, their heads at `0`. -/
theorem bank_rej_other (i : Fin (NL P)) (hi : ∀ j, i ≠ Scrub.inner (Sched.fx P (kk j))) :
    bankH P rejKept i = 0 ∧ bankA P 1 0 0 rejKept i = [] := by
  refine Fin.addCases (motive := fun i => (∀ j, i ≠ Scrub.inner (Sched.fx P (kk j))) →
    bankH P rejKept i = 0 ∧ bankA P 1 0 0 rejKept i = []) (fun i' hi' => ?_) (fun e _ => ?_) i hi
  · refine Fin.addCases (motive := fun i' => (∀ j, Fin.castAdd 1 i' ≠ Scrub.inner (Sched.fx P (kk j))) →
      bankH P rejKept (Fin.castAdd 1 i') = 0 ∧ bankA P 1 0 0 rejKept (Fin.castAdd 1 i') = [])
      (fun i'' hi'' => ?_) (fun e _ => ?_) i' hi'
    · -- a stage tape `i''`
      have hin : (Fin.castAdd 1 (Fin.castAdd 1 i'') : Fin (NL P)) = Scrub.inner i'' := rfl
      rw [hin] at hi'' ⊢
      simp only [bankH, bankA, Scrub.heads_inner, Scrub.bank_inner, Scrub.blank]
      by_cases hlt : i''.val < 31
      · have hfx : i'' = Sched.fx P ⟨i''.val, hlt⟩ := by apply Fin.ext; simp [Sched.fx_val]
        have hk : ∀ j, (⟨i''.val, hlt⟩ : Fin 31) ≠ kk j := by
          intro j hj; apply hi'' j; rw [hfx, hj]
        have hk' : ¬ (i''.val = 0 ∨ i''.val = 1 ∨ i''.val = 13 ∨ (24 ≤ i''.val ∧ i''.val ≤ 29)) := by
          intro h
          rcases h with h | h | h | ⟨h1, h2⟩
          · exact hk 0 (Fin.ext (by simp [kk, h]))
          · exact hk 1 (Fin.ext (by simp [kk, h]))
          · exact hk 2 (Fin.ext (by simp [kk, h]))
          · interval_cases hv : i''.val
            · exact hk 3 (Fin.ext (by simp [kk, hv]))
            · exact hk 4 (Fin.ext (by simp [kk, hv]))
            · exact hk 5 (Fin.ext (by simp [kk, hv]))
            · exact hk 6 (Fin.ext (by simp [kk, hv]))
            · exact hk 7 (Fin.ext (by simp [kk, hv]))
            · exact hk 8 (Fin.ext (by simp [kk, hv]))
        have hs : Sched.scr P i'' = true := by
          simp only [Sched.scr, Sched.keptV, Bool.not_eq_true']
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          omega
        rw [hs]
        refine ⟨?_, by simp⟩
        rw [hfx, Sched.iterH_fx]
        simp only [Sched.fixedH, rejKept]
        split_ifs <;> omega
      · have hs : Sched.scr P i'' = true := by
          simp only [Sched.scr, Sched.keptV, Bool.not_eq_true']
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          omega
        rw [hs]
        refine ⟨?_, by simp⟩
        simp [Sched.iterH, hlt]
    · -- the log tape
      simp [bankH, bankA, Scrub.heads, Scrub.bank]
  · -- the driver tape
    simp [bankH, bankA, Scrub.heads, Scrub.bank]

/-- The rejecting bank on the nine kept tapes is the writer's output. -/
theorem bank_rej_kept (j : Fin 9) :
    bankH P rejKept (Scrub.inner (Sched.fx P (kk j))) = rejH j ∧
      bankA P 1 0 0 rejKept (Scrub.inner (Sched.fx P (kk j))) = rejA j := by
  fin_cases j <;>
    simp [bankH, bankA, Scrub.heads_inner, Scrub.bank_inner, Scrub.blank, Sched.scr, Sched.keptV, Sched.fx_val,
      Sched.iterH_fx, Sched.iterA_fx, Sched.fixedH, Sched.fixedA, kk, rejKept, rejAcc, rejH, rejA, regTape]

/-- **The rejecting writer**: from blank loop tapes it leaves exactly the rejecting bank on every loop tape, and
touches nothing else. -/
theorem rej_step (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (hH : ∀ i, H (Plan.lp P tf i) = 0)
    (hA : ∀ i, A (Plan.lp P tf i) = []) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool), Step (rejM P tf) 3 H A H' A' ∧
      (∀ i, H' (Plan.lp P tf i) = bankH P rejKept i) ∧ (∀ i, A' (Plan.lp P tf i) = bankA P 1 0 0 rejKept i) ∧
      (∀ i, (∀ j, i ≠ Plan.lp P tf j) → H' i = H i ∧ A' i = A i) := by
  have hstep := (Exec.step rejP_exec).dock (rs9 P tf) (rs9_inj P tf) H A (fun j => hH _) (fun j => hA _)
  refine ⟨_, _, hstep, ?_, ?_, ?_⟩
  · intro i
    by_cases hk : ∃ j, i = Scrub.inner (Sched.fx P (kk j))
    · obtain ⟨j, rfl⟩ := hk
      show dockH (rs9 P tf) H rejH (rs9 P tf j) = _
      rw [dockH_slot (rs9 P tf) (rs9_inj P tf)]
      exact (bank_rej_kept P j).1.symm
    · push Not at hk
      rw [dockH_other (rs9 P tf) H rejH (Plan.lp P tf i) (fun j h => hk j ((Plan.lp_inj P tf) h).symm), hH]
      exact (bank_rej_other P i hk).1.symm
  · intro i
    by_cases hk : ∃ j, i = Scrub.inner (Sched.fx P (kk j))
    · obtain ⟨j, rfl⟩ := hk
      show install (rs9 P tf) A rejA (rs9 P tf j) = _
      rw [install_slot (rs9 P tf) (rs9_inj P tf)]
      exact (bank_rej_kept P j).2.symm
    · push Not at hk
      rw [install_other (rs9 P tf) A rejA (Plan.lp P tf i) (fun j h => hk j ((Plan.lp_inj P tf) h).symm), hA]
      exact (bank_rej_other P i hk).2.symm
  · intro i hi
    exact ⟨dockH_other (rs9 P tf) H rejH i (fun j h => hi _ h.symm),
      install_other (rs9 P tf) A rejA i (fun j h => hi _ h.symm)⟩

end Dock

/-! ## The gate -/

section Gate
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)

/-- The refuter's framed input: the worker's tape `0`. -/
noncomputable def inT : Fin (NW P tf) := ⟨0, by show 0 < 2 + NL P + tf; omega⟩

variable (htf : 1 ≤ tf)

/-- The gate's flag: the front's first own tape. -/
noncomputable def flagT : Fin (NW P tf) := ⟨2 + NL P, by show 2 + NL P < 2 + NL P + tf; omega⟩

theorem flagT_ne_lp (i : Fin (NL P)) : flagT P tf htf ≠ Plan.lp P tf i := by
  intro h
  have := congrArg Fin.val h
  simp only [flagT, Plan.lp] at this
  have := i.isLt
  omega

theorem inT_ne_lp (i : Fin (NL P)) : inT P tf ≠ Plan.lp P tf i := by
  intro h
  have := congrArg Fin.val h
  simp only [inT, Plan.lp] at this
  omega

theorem flagT_ne_inT : flagT P tf htf ≠ inT P tf := by
  intro h
  have := congrArg Fin.val h
  simp only [flagT, inT] at this
  omega

/-- **The gate**: base's length counter on the framed input, then the rest of the front on a set flag, or the
rejecting writer on a cleared one. -/
noncomputable def gateThen (C : ℕ) {s : ℕ} (acc : Machine (NW P tf) s) :=
  Composition.machine (C10LengthGate.counter C (inT P tf) (flagT P tf htf))
    (iteMachine (flagT P tf htf) acc (rejM P tf))

theorem entryA_lp {N : ℕ} (x : BitInput N) (w : List Bool) (i : Fin (NL P)) :
    entryA (u := NW P tf) x w (Plan.lp P tf i) = [] := by
  simp only [entryA, Plan.lp]
  split_ifs with h1 h2 <;> first | omega | rfl

theorem entryA_in {N : ℕ} (x : BitInput N) (w : List Bool) :
    entryA (u := NW P tf) x w (inT P tf) = RepairOrdinary.frame (List.ofFn x) := by
  simp [entryA, inT]

theorem entryA_flag {N : ℕ} (x : BitInput N) (w : List Bool) : entryA (u := NW P tf) x w (flagT P tf htf) = [] := by
  have h0 : (flagT P tf htf).val ≠ 0 := by simp [flagT]
  have h1 : (flagT P tf htf).val ≠ 1 := by simp only [flagT]; omega
  simp only [entryA]
  rw [if_neg h0, if_neg h1]

/-- **Below the onset the gate rejects outright**: the rejecting bank on every loop tape within `2N + 6` steps. -/
theorem gate_reject (C : ℕ) {s : ℕ} (acc : Machine (NW P tf) s) {N : ℕ} (x : BitInput N) (w : List Bool)
    (hN : N < C) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (gateThen P tf htf C acc) (2 * N + 1 + 1 + (3 + 1)) (fun _ => 0) (entryA x w) H' A' ∧
      (∀ i, H' (Plan.lp P tf i) = bankH P rejKept i) ∧ (∀ i, A' (Plan.lp P tf i) = bankA P 1 0 0 rejKept i) := by
  have hlen : (List.ofFn x).length = N := List.length_ofFn
  have hc := C10LengthGate.counter_reject C (inT P tf) (flagT P tf htf) (fun _ => 0) (entryA x w) N (by omega)
    (fun j hj he => by
      rw [entryA_in]
      simpa using C10LengthGate.frame_short (List.ofFn x) j (by rw [hlen]; omega) he)
    (by rw [entryA_in]; simpa [hlen] using C10LengthGate.frame_stop (List.ofFn x))
  set H1 := C10LengthGate.exitHeads (inT P tf) (fun _ => 0) (0 + 2 * N) with hH1
  set A1 := C10LengthGate.exitTapes (flagT P tf htf) (entryA x w) (H1 (flagT P tf htf)) false with hA1
  have hH1lp : ∀ i, H1 (Plan.lp P tf i) = 0 := by
    intro i; simp [H1, C10LengthGate.exitHeads, (inT_ne_lp P tf i).symm]
  have hA1lp : ∀ i, A1 (Plan.lp P tf i) = [] := by
    intro i
    simp only [A1, C10LengthGate.exitTapes]
    rw [if_neg (flagT_ne_lp P tf htf i).symm]
    exact entryA_lp P tf x w i
  have hbit : (⟨H1, A1⟩ : Bank (NW P tf)).bit (flagT P tf htf) = false := by
    have hh : H1 (flagT P tf htf) = 0 := by
      simp [H1, C10LengthGate.exitHeads, flagT_ne_inT P tf htf]
    simp only [Bank.bit, A1, C10LengthGate.exitTapes, if_true, hh, entryA_flag P tf htf x w]
    rfl
  obtain ⟨H', A', hr, hHr, hAr, -⟩ := rej_step P tf H1 A1 hH1lp hA1lp
  have hite : Step (iteMachine (flagT P tf htf) acc (rejM P tf)) (3 + 1) H1 A1 H' A' :=
    ite_branch_step (flagT P tf htf) acc (rejM P tf) ⟨H1, A1⟩ ⟨H', A'⟩ 3 (iteR s) (rejM P tf)
      (by simp [hbit]) (ite_halted_R _ _ _) (ite_step_R _ _ _) hr
  refine ⟨H', A', ?_, hHr, hAr⟩
  exact hc.seq hite

/-- **Past the onset the gate passes**: after `4C + 2` steps the rest of the front runs from the refuter's tapes with
the flag set. -/
theorem gate_pass (C : ℕ) {s : ℕ} (acc : Machine (NW P tf) s) {N : ℕ} (x : BitInput N) (w : List Bool)
    (hN : C ≤ N) (n : ℕ) (Ho : Fin (NW P tf) → ℕ) (Ao : Fin (NW P tf) → List Bool)
    (hacc : Step acc n (fun _ => 0) (C10LengthGate.exitTapes (flagT P tf htf) (entryA x w) 0 true) Ho Ao) :
    Step (gateThen P tf htf C acc) (4 * C + 1 + 1 + (n + 1)) (fun _ => 0) (entryA x w) Ho Ao := by
  have hlen : (List.ofFn x).length = N := List.length_ofFn
  have hc := C10LengthGate.counter_pass_clean C (inT P tf) (flagT P tf htf) (fun _ => 0) (entryA x w)
    (fun j hj he => by
      rw [entryA_in]
      simpa using C10LengthGate.frame_short (List.ofFn x) j (by rw [hlen]; omega) he)
  have hbit : (⟨fun _ => 0, C10LengthGate.exitTapes (flagT P tf htf) (entryA x w) 0 true⟩ : Bank (NW P tf)).bit
      (flagT P tf htf) = true := by
    simp only [Bank.bit, C10LengthGate.exitTapes, if_true, entryA_flag P tf htf x w]
    rfl
  have hite : Step (iteMachine (flagT P tf htf) acc (rejM P tf)) (n + 1) (fun _ => 0)
      (C10LengthGate.exitTapes (flagT P tf htf) (entryA x w) 0 true) Ho Ao :=
    ite_branch_step (flagT P tf htf) acc (rejM P tf)
      ⟨fun _ => 0, C10LengthGate.exitTapes (flagT P tf htf) (entryA x w) 0 true⟩ ⟨Ho, Ao⟩ n (iteL rejP.size) acc
      (by rw [hbit]; rfl) (ite_halted_L _ _ _) (ite_step_L _ _ _) hacc
  exact hc.seq hite

end Gate


end NearCubicWires.WireExponent3_5.UnionMachine.FrontGate
