import Proof.Wire_3_5.UnionMachine.Plan

/-! # C6, U7: the decision (P3:3485-3489, "accept only if [...]")

Realizes the last step of the union machine's tests: "accept only if `V̂ ≤ 2v₀`, `Q̂ ≤ 1 + v₀` and `μ̂ ≥ τ`"
(`tr:thresholds`, P3:3485-3489), with the slack of, on the schedule loop's final bank. The front preloads
each test's threshold into the test's accumulator pair (M4 `FrontsF`), so the three tests are the unary comparisons
`V⁺ ≤ V⁻`, `Q⁺ ≤ Q⁻`, `μ⁻ ≤ μ⁺` of the six accumulators (`Plan.decisionOf`).

The program uses only the six accumulator registers and the result cell (no scratch register, so it runs on the
loop's scrubbed bank as it is): `cmpDown A B` counts `B` down while counting `A` down, leaving `A = a − b` (truncated),
which is `0` exactly when `a ≤ b`; the cell is set when the three remainders vanish.

Paper quantity of the main type: **`Plan.DecideF`** (the residual U7 of the plan): on the loop's final bank the result
cell becomes `decisionOf` of the accumulators within `20·(cap + 1)` steps (`decideF`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Decision
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan

/-- The decision bank: one stream (the call table, untouched), the cell, the six accumulators. -/
abbrev DS := WState 0 6

variable (cap : ℕ)

/-- `A := A ∸ B`, `B := 0`: count `B` down, and `A` with it while it is positive. -/
def cmpDown (A B : Fin 6) : WM 0 6 := .whr B (.seq (.dec B) (.ifr A (.dec A) .skip))

theorem cmpDown_spec (A B : Fin 6) (hAB : A ≠ B) :
    ∀ (b : ℕ) (σ : DS), σ.val B = b → σ.val A ≤ cap → σ.val B ≤ cap →
      ∃ τ : DS, WExec cap (cmpDown A B) σ τ (6 * b + 1) ∧ τ.val B = 0 ∧ τ.val A = σ.val A - b ∧
        (∀ r, r ≠ A → r ≠ B → τ.val r = σ.val r) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell
  | 0, σ, hb, _, _ => ⟨σ, WExec.mono (WExec.whrF hb) (by omega), hb, by simp, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | b + 1, σ, hb, hA, hB => by
    have e1 := WExec.dec (cap := cap) B σ hB
    rw [hb] at e1
    set σ1 := σ.setv B b with hσ1
    have hA1 : σ1.val A = σ.val A := by simp [σ1, Function.update_apply, hAB]
    have hB1 : σ1.val B = b := by simp [σ1]
    by_cases ha : σ.val A = 0
    · have e2 : WExec cap (.ifr A (.dec A) .skip) σ1 σ1 1 := WExec.ifrF (by rw [hA1, ha]) (WExec.skip σ1)
      obtain ⟨τ, eτ, h1, h2, h3, h4, h5, h6⟩ := cmpDown_spec A B hAB b σ1 hB1 (by rw [hA1]; omega) (by omega)
      refine ⟨τ, WExec.mono (WExec.whrT (by omega) (e1.seq e2) eτ) (by omega), h1, ?_, ?_, h4, h5, h6⟩
      · rw [h2, hA1, ha]; simp
      · intro r h1' h2'; rw [h3 r h1' h2']; simp [σ1, Function.update_apply, h2']
    · have e2 := WExec.dec (cap := cap) A σ1 (by rw [hA1]; exact hA)
      set σ2 := σ1.setv A (σ1.val A - 1) with hσ2
      have e3 : WExec cap (.ifr A (.dec A) .skip) σ1 σ2 2 := WExec.ifrT (by rw [hA1]; exact ha) e2
      have hA2 : σ2.val A = σ.val A - 1 := by simp [σ2, hA1]
      have hB2 : σ2.val B = b := by simp [σ2, σ1, Function.update_apply, hAB.symm]
      obtain ⟨τ, eτ, h1, h2, h3, h4, h5, h6⟩ := cmpDown_spec A B hAB b σ2 hB2 (by rw [hA2]; omega) (by omega)
      refine ⟨τ, WExec.mono (WExec.whrT (by omega) (e1.seq e3) eτ) (by omega), h1, ?_, ?_, h4, h5, h6⟩
      · rw [h2, hA2]; omega
      · intro r h1' h2'
        rw [h3 r h1' h2']
        simp [σ2, σ1, Function.update_apply, h1', h2']

/-- The cell becomes `true` when the three remainders `V`, `Q`, `μ` are `0`. -/
def tailP : WM 0 6 := .ifr 0 .skip (.ifr 2 .skip (.ifr 5 .skip (.setc true)))

theorem tailP_spec (σ : DS) :
    ∃ τ : DS, WExec cap tailP σ τ 5 ∧
      τ.cell = (σ.cell || (decide (σ.val 0 = 0) && decide (σ.val 2 = 0) && decide (σ.val 5 = 0))) ∧
        τ.st = σ.st ∧ τ.sh = σ.sh := by
  by_cases h0 : σ.val 0 = 0
  · by_cases h2 : σ.val 2 = 0
    · by_cases h5 : σ.val 5 = 0
      · exact ⟨σ.setc true, WExec.mono (WExec.ifrF h0 (WExec.ifrF h2 (WExec.ifrF h5 (WExec.setc true σ))))
          (by omega), by simp [h0, h2, h5], rfl, rfl⟩
      · exact ⟨σ, WExec.mono (WExec.ifrF h0 (WExec.ifrF h2 (WExec.ifrT h5 (WExec.skip σ)))) (by omega),
          by simp [h5], rfl, rfl⟩
    · exact ⟨σ, WExec.mono (WExec.ifrF h0 (WExec.ifrT h2 (WExec.skip σ))) (by omega), by simp [h2], rfl, rfl⟩
  · exact ⟨σ, WExec.mono (WExec.ifrT h0 (WExec.skip σ)) (by omega), by simp [h0], rfl, rfl⟩

/-- **The decision program.** -/
def decideP : WM 0 6 := .seq (cmpDown 0 1) (.seq (cmpDown 2 3) (.seq (cmpDown 5 4) tailP))

/-- The decision's cost bound. -/
def decCost (c : ℕ) : ℕ := 18 * c + 20

theorem decCost_le (c : ℕ) : decCost c ≤ 20 * (c + 1) := by unfold decCost; omega

/-- **The decision program decides**: from registers within `cap` and a clear cell, the cell becomes
`decisionOf` of the registers. -/
theorem decideP_spec (σ : DS) (hc : σ.cell = false) (hcap : ∀ r, σ.val r ≤ cap) :
    ∃ τ : DS, WExec cap decideP σ τ (decCost cap) ∧ τ.cell = decisionOf σ.val ∧ τ.st = σ.st ∧ τ.sh = σ.sh := by
  obtain ⟨τ1, e1, a1, b1, c1, s1, h1, l1⟩ := cmpDown_spec cap 0 1 (by decide) (σ.val 1) σ rfl (hcap 0) (hcap 1)
  obtain ⟨τ2, e2, a2, b2, c2, s2, h2, l2⟩ := cmpDown_spec cap 2 3 (by decide) (τ1.val 3) τ1 rfl
    (by rw [c1 2 (by decide) (by decide)]; exact hcap 2) (by rw [c1 3 (by decide) (by decide)]; exact hcap 3)
  obtain ⟨τ3, e3, a3, b3, c3, s3, h3, l3⟩ := cmpDown_spec cap 5 4 (by decide) (τ2.val 4) τ2 rfl
    (by rw [c2 5 (by decide) (by decide), c1 5 (by decide) (by decide)]; exact hcap 5)
    (by rw [c2 4 (by decide) (by decide), c1 4 (by decide) (by decide)]; exact hcap 4)
  obtain ⟨τ4, e4, hcell, s4, h4⟩ := tailP_spec cap τ3
  have v1 : τ1.val 3 = σ.val 3 := c1 3 (by decide) (by decide)
  have v4 : τ2.val 4 = σ.val 4 := by rw [c2 4 (by decide) (by decide), c1 4 (by decide) (by decide)]
  have h1' := hcap 1
  have h3' := hcap 3
  have h4' := hcap 4
  refine ⟨τ4, WExec.mono (e1.seq (e2.seq (e3.seq e4))) ?_, ?_, ?_, ?_⟩
  · unfold decCost; rw [v1, v4]; omega
  · rw [hcell, l3, l2, l1, hc]
    have r0 : τ3.val 0 = σ.val 0 - σ.val 1 := by
      rw [c3 0 (by decide) (by decide), c2 0 (by decide) (by decide), b1]
    have r2 : τ3.val 2 = σ.val 2 - σ.val 3 := by rw [c3 2 (by decide) (by decide), b2, v1, c1 2 (by decide) (by decide)]
    have r5 : τ3.val 5 = σ.val 5 - σ.val 4 := by
      rw [b3, v4, c2 5 (by decide) (by decide), c1 5 (by decide) (by decide)]
    rw [r0, r2, r5]
    unfold decisionOf
    simp only [Bool.false_or]
    congr 1
    · congr 1
      · exact decide_eq_decide.mpr (by omega)
      · exact decide_eq_decide.mpr (by omega)
    · exact decide_eq_decide.mpr (by omega)
  · rw [s4, s3, s2, s1]
  · rw [h4, h3, h2, h1]

/-! ## Docked at the loop's final bank -/

section Dock
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

/-- The loop tape of a decision-bank tape: the stream is the call table (`0`), then the cell (`1`), then the
accumulators (`24 + r`). -/
def dbv (j : Fin (0 + 2 + 6)) : ℕ := if j.val < 2 then j.val else j.val + 22

theorem dbv_lt (j : Fin (0 + 2 + 6)) : dbv j < 31 := by have := j.isLt; unfold dbv; split_ifs <;> omega

/-- **The decision bank's slots** in the loop's scrubbed layout. -/
noncomputable def db (j : Fin (0 + 2 + 6)) : Fin (NL P) := Scrub.inner (Sched.fx P ⟨dbv j, dbv_lt j⟩)

theorem db_inj : Function.Injective (db P) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [db, Scrub.inner, Fin.val_castAdd, Sched.fx_val] at hv
  apply Fin.ext
  unfold dbv at hv
  split_ifs at hv <;> omega

/-- The decision bank at the loop's kept data: the table on the stream, a clear cell, the accumulators. -/
def σD (K : Sched.Kept) : DS := ⟨![K.pos], ![K.tbl], fun r => K.acc r, false⟩

theorem db_entry (cap R Lg : ℕ) (K : Sched.Kept) (j : Fin (0 + 2 + 6)) :
    bankH P K (db P j) = (wenc cap (σD K)).H j ∧ bankA P cap R Lg K (db P j) = (wenc cap (σD K)).A j := by
  fin_cases j <;>
    simp [db, dbv, bankH, bankA, Scrub.heads_inner, Scrub.bank_inner, Scrub.blank, Sched.scr, Sched.keptV,
      Sched.iterH_fx, Sched.iterA_fx, Sched.fixedH, Sched.fixedA, Sched.fx_val, wenc, role, σD]

theorem cellSlot_eq : cellSlot P = db P 1 := by
  apply Fin.ext
  simp [cellSlot, db, dbv, Scrub.inner, Sched.fx_val]

/-- **U7 at one primitive**: the decision program docked at the loop's final bank. -/
noncomputable def decideAt : DecideAt P 20 where
  sd := decideP.toProg.size
  M := RecoveryFocus.machine (db P) decideP.toProg.compile
  cost := decCost
  hcost := decCost_le
  run := fun cap R Lg K _ hacc => by
    obtain ⟨τ, hτ, hcell, _, _⟩ := decideP_spec cap (σD K) rfl hacc
    refine ⟨_, _, (WExec.exec cap hτ).step.dock (db P) (db_inj P) (bankH P K) (bankA P cap R Lg K)
      (fun j => (db_entry P cap R Lg K j).1) (fun j => (db_entry P cap R Lg K j).2), ?_⟩
    rw [cellSlot_eq, dockH_slot (db P) (db_inj P), install_slot (db P) (db_inj P)]
    have hH : (wenc cap τ).H 1 = 0 := by simp [wenc, role]
    have hA : (wenc cap τ).A 1 = [τ.cell] := by simp [wenc, role]
    rw [hH, hA, hcell]
    simp [σD, readTapeBit]

end Dock

/-- **Residual U7 of the plan** (`Plan.DecideF`), with `Kd = 20`. -/
noncomputable def decideF : DecideF := ⟨20, fun P => decideAt P⟩


end NearCubicWires.WireExponent3_5.UnionMachine.Decision
