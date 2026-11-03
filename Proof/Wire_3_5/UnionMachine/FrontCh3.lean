import Proof.Wire_3_5.UnionMachine.FrontNums
import Proof.Wire_3_5.UnionMachine.FrontFmtHd
import Proof.Wire_3_5.UnionMachine.FrontEntriesStage
import Proof.PCP.PCPSerializerCapacityPower

/-! # C6 front, the chain, phase 3: the counts (P3:3669-3674)

On the valid path, after phase 2 (the PCPP output word) and the tag's branch (mode `m`), the chain's counts, each a
stage docked by the kit on its own region:
* **`powStage`**: base's unary power (`PCPSerializerCapacity.Power`) from `1^q`: `1^{C·(q+1)^D}` (the fill count
  `1^W`, the description envelope `1^L`);
* **`metaStage`**: base's metadata counter on a framed word: `1^{|x|}`, `1^{|w|}`;
* `hdStageF` (`FrontFmtHd.hdW` docked: the request head), `numsStageF` (M44 `numsW` docked: `1^E`, `1^s`, `1^sys`,
  `1^aux`, `1^{nv}`, `0 1^{nv}`).
Every stage keeps the tapes below its region and leaves the tapes past it blank; heads stay as they were.

Paper quantity: none (the chain's plumbing; the counts are the guess's sizes). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCh3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots NearCubicWires.WireExponent3_5.UnionMachine.FrontWM
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWfDock NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit

section Stages
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)

/-- One shared input at local tape `0`. -/
noncomputable def sh1 {t : ℕ} (a : Fin (NW P tf)) (j : Fin t) : Option (Fin (NW P tf)) :=
  if j.val = 0 then some a else none

theorem sh1_I {t : ℕ} (a : Fin (NW P tf)) : ∀ i j b, sh1 (t := t) P tf a i = some b → sh1 P tf a j = some b → i = j := by
  intro i j b hi hj
  unfold sh1 at hi hj
  split_ifs at hi hj with h1 h2
  exact Fin.ext (by omega)

theorem sh1_L {t : ℕ} (a : Fin (NW P tf)) (k0 : ℕ) (ha : 2 + NL P ≤ a.val ∧ a.val < 2 + NL P + k0) :
    ∀ i b, sh1 (t := t) P tf a i = some b → 2 + NL P ≤ b.val ∧ b.val < 2 + NL P + k0 := by
  intro i b hi
  unfold sh1 at hi
  split_ifs at hi
  rw [← Option.some.inj hi]; exact ha

theorem sh1_zero {t : ℕ} (a : Fin (NW P tf)) (j : Fin t) (h : j.val = 0) : sh1 P tf a j = some a := by
  unfold sh1; rw [if_pos h]

theorem sh1_ne {t : ℕ} (a : Fin (NW P tf)) (j : Fin t) (h : j.val ≠ 0) : sh1 P tf a j = none := by
  unfold sh1; rw [if_neg h]

/-- A ready stage with one shared input at tape `0` (kept), docked: its outputs, the rest kept. -/
theorem ready1 {t s : ℕ} (p : Machine t s) (n : ℕ) (tin tout : Fin t → List Bool) (hr : ClockJoin.ReadyRun p n tin tout)
    (hin0 : ∀ j : Fin t, j.val ≠ 0 → tin j = []) (hkeep : ∀ j : Fin t, j.val = 0 → tout j = tin j)
    (k0 : ℕ) (hk : k0 + t ≤ tf) (a : Fin (NW P tf)) (ha : 2 + NL P ≤ a.val ∧ a.val < 2 + NL P + k0)
    (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H A k0)
    (hA : ∀ j : Fin t, j.val = 0 → A a = tin j) (hH : H a = 0) :
    Step (RecoveryFocus.machine (sl P tf (sh1 P tf a) k0 hk) p) n H A H (install (sl P tf (sh1 P tf a) k0 hk) A tout) ∧
      (∀ j, (install (sl P tf (sh1 P tf a) k0 hk) A tout) (sl P tf (sh1 P tf a) k0 hk j) = tout j) ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → install (sl P tf (sh1 P tf a) k0 hk) A tout y = A y) ∧
      PristineH P tf H (install (sl P tf (sh1 P tf a) k0 hk) A tout) (k0 + t) := by
  have hs := step_of_ready hr
  obtain ⟨st, hinj, hpr⟩ := dockS_step P tf p n tin tout (fun _ => 0) hs (sh1 P tf a) k0 hk (sh1_I P tf a)
    (sh1_L P tf a k0 ha) H A hPr
    (fun i b hi => by
      unfold sh1 at hi; split_ifs at hi with h0
      rw [← Option.some.inj hi]; exact ⟨hA i h0, hH⟩)
    (fun i hi => by unfold sh1 at hi; split_ifs at hi with h0; exact hin0 i h0)
  have hH0 : ∀ j, H (sl P tf (sh1 P tf a) k0 hk j) = 0 := by
    intro j
    by_cases h0 : j.val = 0
    · rw [sl_some P tf _ k0 hk j a (sh1_zero P tf a j h0)]; exact hH
    · rw [sl_none P tf _ k0 hk j (sh1_ne P tf a j h0)]; exact (hPr.1 _ (by rw [rg_val]; omega)).2
  rw [ExtDecompositionBatch.dockH_existing _ H _ hH0] at st hpr
  refine ⟨st, fun j => install_slot _ hinj _ _ j, fun y hy => ?_, hpr⟩
  by_cases hya : y = a
  · rw [hya]
    by_cases ht : 0 < t
    · have e : sl P tf (sh1 P tf a) k0 hk ⟨0, ht⟩ = a := sl_some P tf _ k0 hk _ a (sh1_zero P tf a _ rfl)
      calc install (sl P tf (sh1 P tf a) k0 hk) A tout a
          = install (sl P tf (sh1 P tf a) k0 hk) A tout (sl P tf (sh1 P tf a) k0 hk ⟨0, ht⟩) := by rw [e]
        _ = tout ⟨0, ht⟩ := install_slot _ hinj _ _ _
        _ = tin ⟨0, ht⟩ := hkeep _ rfl
        _ = A a := (hA _ rfl).symm
    · exact install_other _ _ _ _ (fun j => absurd j.isLt (by omega))
  · exact install_low P tf _ k0 hk A tout y hy (fun i b hi e => by
      unfold sh1 at hi; split_ifs at hi
      rw [← Option.some.inj hi] at e; exact hya e.symm)

/-! ### The unary power -/

open NearCubicWires.RepairOrdinary.PCPSerializerCapacity in
/-- **The unary power** from `1^q` (shared at `a`): `1^{C·(q+1)^D}` on the stage's output slot. -/
theorem powStage (D C q k0 : ℕ)
    (hk : k0 + RepairSource.ProjectionNormalization.DimensionPolynomial.tapes D ≤ tf) (a : Fin (NW P tf))
    (ha : 2 + NL P ≤ a.val ∧ a.val < 2 + NL P + k0) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A k0) (hq : A a = List.replicate q true ∧ H a = 0) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (RecoveryFocus.machine (sl P tf (sh1 P tf a) k0 hk) (Power.machine D C)) (Power.budget D C q) H A H A' ∧
      A' (sl P tf (sh1 P tf a) k0 hk (Power.outputSlot D)) = List.replicate (C * (q + 1) ^ D) true ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → A' y = A y) ∧
      PristineH P tf H A' (k0 + RepairSource.ProjectionNormalization.DimensionPolynomial.tapes D) := by
  obtain ⟨out, hr, h0, hout⟩ := Power.capacity_run D C q
  obtain ⟨st, hsl, hlow, hpr⟩ := ready1 P tf _ _ _ out hr
    (fun j hj => by simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, hj])
    (fun j hj => by
      have : j = ⟨0, by simp [RepairSource.ProjectionNormalization.DimensionPolynomial.tapes]⟩ := Fin.ext hj
      subst this; rw [h0]; simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input])
    k0 hk a ha H A hPr
    (fun j hj => by rw [hq.1]; simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, hj]) hq.2
  exact ⟨_, st, by rw [hsl]; exact hout, hlow, hpr⟩

/-! ### The metadata counter -/

open NearCubicWires.RepairSource.CloseoutSchedule in
/-- **The counter** on a framed word (shared at `a`): `0 1^{|bits|}` on tape `1`, `1^{|bits|}` on tape `2`. -/
theorem metaStage (bits : List Bool) (k0 : ℕ) (hk : k0 + 8 ≤ tf) (a : Fin (NW P tf))
    (ha : 2 + NL P ≤ a.val ∧ a.val < 2 + NL P + k0) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A k0) (hx : A a = frame bits ∧ H a = 0) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (RecoveryFocus.machine (sl P tf (sh1 P tf a) k0 hk) FrontEntriesStage.countM)
        (4 * bits.length + 5 + 1 + (2 * bits.length + 6)) H A H A' ∧
      A' (sl P tf (sh1 P tf a) k0 hk 2) = List.replicate bits.length true ∧
      A' (sl P tf (sh1 P tf a) k0 hk 1) = RepairSource.VerifierDecoding.CompareMachine.word bits.length ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → A' y = A y) ∧ PristineH P tf H A' (k0 + 8) := by
  have hr : ClockJoin.ReadyRun FrontEntriesStage.countM (4 * bits.length + 5 + 1 + (2 * bits.length + 6))
      (Metadata.input bits) (Metadata.copied bits) :=
    ClockJoin.join _ _ _ _ _ _ _ (Metadata.length_run bits) (Metadata.copy_run bits)
  obtain ⟨st, hsl, hlow, hpr⟩ := ready1 P tf _ _ _ _ hr
    (fun j hj => by fin_cases j <;> simp_all [Metadata.input])
    (fun j hj => by fin_cases j <;> simp_all [Metadata.input, Metadata.copied])
    k0 hk a ha H A hPr (fun j hj => by fin_cases j <;> simp_all [Metadata.input]) hx.2
  refine ⟨_, st, ?_, ?_, hlow, hpr⟩
  · rw [hsl]; rfl
  · rw [hsl]; rfl

end Stages

/-! ### Any ready stage with shared inputs -/

section Multi
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)

/-- **A ready stage docked** with shared inputs it keeps: its outputs at its slots, the tapes below its region kept,
the tapes past it blank, heads unchanged. -/
theorem readyN {t s : ℕ} (p : Machine t s) (n : ℕ) (tin tout : Fin t → List Bool) (hr : ClockJoin.ReadyRun p n tin tout)
    (ins : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (hk : k0 + t ≤ tf)
    (hinsI : ∀ i j a, ins i = some a → ins j = some a → i = j)
    (hinsL : ∀ i a, ins i = some a → 2 + NL P ≤ a.val ∧ a.val < 2 + NL P + k0)
    (hkeep : ∀ j a, ins j = some a → tout j = tin j)
    (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H A k0)
    (hin : ∀ i a, ins i = some a → A a = tin i ∧ H a = 0) (hnone : ∀ i, ins i = none → tin i = []) :
    Step (RecoveryFocus.machine (sl P tf ins k0 hk) p) n H A H (install (sl P tf ins k0 hk) A tout) ∧
      (∀ j, (install (sl P tf ins k0 hk) A tout) (sl P tf ins k0 hk j) = tout j) ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → install (sl P tf ins k0 hk) A tout y = A y) ∧
      PristineH P tf H (install (sl P tf ins k0 hk) A tout) (k0 + t) := by
  have hs := step_of_ready hr
  obtain ⟨st, hinj, hpr⟩ := dockS_step P tf p n tin tout (fun _ => 0) hs ins k0 hk hinsI hinsL H A hPr hin hnone
  have hH0 : ∀ j, H (sl P tf ins k0 hk j) = 0 := by
    intro j
    cases hj : ins j with
    | some a => rw [sl_some P tf _ k0 hk j a hj]; exact (hin j a hj).2
    | none => rw [sl_none P tf _ k0 hk j hj]; exact (hPr.1 _ (by rw [rg_val]; omega)).2
  rw [ExtDecompositionBatch.dockH_existing _ H _ hH0] at st hpr
  refine ⟨st, fun j => install_slot _ hinj _ _ j, fun y hy => ?_, hpr⟩
  by_cases hsh : ∃ j a, ins j = some a ∧ a = y
  · obtain ⟨j, a, hj, rfl⟩ := hsh
    calc install (sl P tf ins k0 hk) A tout a = install (sl P tf ins k0 hk) A tout (sl P tf ins k0 hk j) := by
          rw [sl_some P tf _ k0 hk j a hj]
      _ = tout j := install_slot _ hinj _ _ _
      _ = tin j := hkeep j a hj
      _ = A a := (hin j a hj).1.symm
  · push Not at hsh
    exact install_low P tf _ k0 hk A tout y hy (fun i b hi e => hsh i b hi e)

end Multi

/-! ### Any word-program stage with shared streams it keeps -/

section WMulti
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  {ns nr : ℕ}

/-- **A word-program stage docked** (M44 `wfD_step`) whose shared streams are kept: its streams' front tapes end with
the exit's streams, the tapes below its region are kept, the tapes past it blank, heads unchanged. -/
theorem wfN (Pm : WM ns nr) (W n : ℕ) (σ τ : WState ns nr) (hw : WExec (2 * W + 2) Pm σ τ n)
    (hs0 : ∀ i, σ.sh i = 0) (hv0 : ∀ r, σ.val r = 0) (hc0 : σ.cell = false)
    (ins : Fin (ns + 1) → Option (Fin (NW P tf))) (cntT : Fin (NW P tf)) (k0 : ℕ) (hk : k0 + WT ns nr ≤ tf)
    (hinsI : ∀ i j a, ins i = some a → ins j = some a → i = j)
    (hinsL : ∀ i a, ins i = some a → 2 + NL P ≤ a.val ∧ a.val < 2 + NL P + k0)
    (hcL : 2 + NL P ≤ cntT.val ∧ cntT.val < 2 + NL P + k0) (hcs : ∀ i, ins i ≠ some cntT)
    (hkeep : ∀ i a, ins i = some a → τ.st i = σ.st i)
    (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H A k0)
    (hin : ∀ i a, ins i = some a → A a = σ.st i ∧ H a = 0) (hnone : ∀ i, ins i = none → σ.st i = [])
    (hcnt : A cntT = List.replicate W true ∧ H cntT = 0) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (wfD P tf Pm ins cntT k0 hk) ((11 * W + 20) + 1 + (1 + 1 + (2 * n + 2))) H A H A' ∧
      (∀ i, A' (stT P tf ins cntT k0 hk i) = τ.st i) ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → A' y = A y) ∧
      PristineH P tf H A' (k0 + WT ns nr) := by
  obtain ⟨A1, st, hst, hcnt1, hoth, hpr⟩ := wfD_step P tf Pm W n σ τ hw hs0 hv0 hc0 ins cntT k0 hk hinsI hinsL hcL
    hcs H A hPr hin hnone hcnt
  refine ⟨A1, st, hst, fun y hy => ?_, hpr⟩
  by_cases hyc : y = cntT
  · rw [hyc, hcnt1, hcnt.1]
  by_cases hsh : ∃ i a, ins i = some a ∧ a = y
  · obtain ⟨i, a, hi, rfl⟩ := hsh
    rw [← stT_some P tf ins cntT k0 hk i a hi, hst, hkeep i a hi, stT_some P tf ins cntT k0 hk i a hi,
      (hin i a hi).1]
  · push Not at hsh
    refine hoth y (fun j e => ?_)
    unfold sl at e
    cases hj : shW (nr := nr) P tf ins cntT j with
    | none =>
      rw [hj] at e
      simp only [Option.getD_none] at e
      have := congrArg Fin.val e
      rw [rg_val] at this
      omega
    | some a =>
      rw [hj] at e
      simp only [Option.getD_some] at e
      rcases shW_cases P tf ins cntT j a hj with ⟨-, rfl⟩ | ⟨i, -, hi⟩
      · exact hyc e.symm
      · exact hsh i a hi e

end WMulti

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCh3
