import Proof.Packets.PacketsMetaCompose
import Proof.Packets.PacketsGlueMetaChild
import Proof.CaseAnalysis.CapacityPower
import Proof.CaseAnalysis.FinalSelectorLoadMasks

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
noncomputable section

/-! ## Renaming the output tape -/

/-- Swap tape 1 with the output tape `o`. -/
def swapSlots (e : ℕ) (o : Fin (2 + e)) : Fin (2 + e) → Fin (2 + e) :=
  fun k => if k = ⟨1, by omega⟩ then o else if k = o then ⟨1, by omega⟩ else k

theorem swapSlots_injective (e : ℕ) (o : Fin (2 + e)) : Function.Injective (swapSlots e o) := by
  intro a b h
  unfold swapSlots at h
  split_ifs at h <;> first | (subst_vars; rfl) | (exact h) | (simp_all) | (exact (h.symm ▸ rfl))

theorem swapSlots_val_zero (e : ℕ) (o : Fin (2 + e)) (ho : o.val ≠ 0) (k : Fin (2 + e)) :
    (swapSlots e o k).val = 0 ↔ k.val = 0 := by
  unfold swapSlots
  by_cases h1 : k = ⟨1, by omega⟩
  · rw [if_pos h1]
    have hk : k.val = 1 := by rw [h1]
    constructor
    · intro h; exact absurd h ho
    · intro h; omega
  · rw [if_neg h1]
    by_cases h2 : k = o
    · rw [if_pos h2]
      have hk : k.val = o.val := by rw [h2]
      constructor
      · intro h; simp at h
      · intro h; exact absurd (hk ▸ h) ho
    · rw [if_neg h2]

/-- **A map from a machine with its output on tape `o`.** -/
def UnaryMap.ofSwap {e s : ℕ} {f : ℕ → ℕ} (M : Machine (2 + e) s) (o : Fin (2 + e)) (ho : o.val ≠ 0)
    (cost : ℕ → ℕ)
    (run : ∀ x, ∃ A' : Fin (2 + e) → List Bool,
      Step M (cost x) (fun _ => 0) (unIn (2 + e) x) (fun _ => 0) A' ∧ A' o = List.replicate (f x) true) :
    UnaryMap f where
  extra := e
  states := s
  machine := RecoveryFocus.machine (swapSlots e o) M
  cost := cost
  run := by
    intro x
    obtain ⟨A', hs, hA'⟩ := run x
    have d := hs.dock (swapSlots e o) (swapSlots_injective e o) (fun _ => 0) (unIn (2 + e) x)
      (fun _ => rfl)
      (by
        intro k
        unfold unIn
        by_cases hk : k.val = 0
        · rw [if_pos ((swapSlots_val_zero e o ho k).mpr hk), if_pos hk]
        · rw [if_neg (fun h => hk ((swapSlots_val_zero e o ho k).mp h)), if_neg hk])
    have e1 : swapSlots e o o = ⟨1, by omega⟩ := by
      unfold swapSlots
      by_cases h1 : o = ⟨1, by omega⟩
      · rw [if_pos h1]; exact h1
      · rw [if_neg h1, if_pos rfl]
    refine ⟨_, _, d, ?_, ?_⟩
    · rw [← e1, install_slot _ (swapSlots_injective e o)]
      exact hA'
    · rw [← e1, dockH_slot _ (swapSlots_injective e o)]

/-! ## `2^x` -/

theorem power_step (d : ℕ) : ∃ A' : Fin (2 + 15) → List Bool,
    Step RepairSource.CloseoutCapacity.Power.machine (RepairSource.CloseoutCapacity.Power.budget d)
      (fun _ => 0) (unIn (2 + 15) d) (fun _ => 0) A' ∧ A' ⟨15, by omega⟩ = List.replicate (2 ^ d) true := by
  obtain ⟨out, hr, h15, _⟩ := RepairSource.CloseoutCapacity.Power.power_run d
  exact ⟨out, CloseoutFinalSelector.step_of_clock hr, h15⟩

def powMap : UnaryMap (fun x => 2 ^ x) :=
  UnaryMap.ofSwap (e := 15) RepairSource.CloseoutCapacity.Power.machine ⟨15, by omega⟩ (by simp)
    RepairSource.CloseoutCapacity.Power.budget power_step

theorem power_budget_le (d : ℕ) :
    RepairSource.CloseoutCapacity.Power.budget d ≤ 200 * (2 ^ d + 1) ^ 2 := by
  have hd : d < 2 ^ d := Nat.lt_two_pow_self
  unfold RepairSource.CloseoutCapacity.Power.budget MatrixScorePower.budget MatrixUnaryTemplate.budget
  nlinarith

/-! ## `x + c`: the copy-plus machine -/

namespace CopyPlus

/-- Tapes: 0 unary input, 1 output. State 0 copies; states `1..c` append; `c+1` halts. -/
def machine (c : ℕ) : Machine 2 (c + 2) where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == c + 1
  rule := fun q b =>
    if q.val = 0 then
      (if b 0 then some ⟨0, ![none, some true], ![.right, .right]⟩
       else some ⟨⟨1, by omega⟩, fun _ => none, fun _ => .stay⟩)
    else if h : q.val ≤ c then some ⟨⟨q.val + 1, by omega⟩, ![none, some true], ![.stay, .right]⟩
    else none

def cfg (c : ℕ) (q : Fin (c + 2)) (x i j : ℕ) : Configuration 2 (c + 2) :=
  ⟨q, ![i, j], ![List.replicate x true, List.replicate j true]⟩

theorem copy_step (c x i : ℕ) (hi : i < x) :
    step (machine c) (cfg c 0 x i i) = some (cfg c 0 x (i + 1) (i + 1)) := by
  have hr : readTapeBit (List.replicate x true) i = true := read_replicate_true x i hi
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end_replicate]

theorem end_step (c x : ℕ) :
    step (machine c) (cfg c 0 x x x) = some (cfg c ⟨1, by omega⟩ x x x) := by
  have hr : readTapeBit (List.replicate x true) x = false := read_replicate_end x true
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem plus_step (c x q j : ℕ) (hq : 1 ≤ q) (hqc : q ≤ c) :
    step (machine c) (cfg c ⟨q, by omega⟩ x x j) = some (cfg c ⟨q + 1, by omega⟩ x x (j + 1)) := by
  have hq0 : ¬ q = 0 := by omega
  simp [step, machine, cfg, hq0, hqc]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end_replicate]

theorem copy_timed (c x : ℕ) : ∀ i, i ≤ x → Timed (machine c) (x - i) (cfg c 0 x i i) (cfg c 0 x x x) := by
  intro i hi
  induction h : x - i generalizing i with
  | zero =>
    have : i = x := by omega
    subst this
    exact Timed.refl _ _
  | succ k ih =>
    have t1 := Timed.single (p := machine c) (by simp [machine, cfg]) (copy_step c x i (by omega))
    have t2 := ih (i + 1) (by omega) (by omega)
    have t := t1.trans t2
    rw [show 1 + k = k + 1 by omega] at t
    exact t

theorem plus_timed (c x : ℕ) : ∀ (q j : ℕ) (_hq : 1 ≤ q) (_hqc : q ≤ c + 1),
    Timed (machine c) (c + 1 - q) (cfg c ⟨q, by omega⟩ x x j) (cfg c ⟨c + 1, by omega⟩ x x (j + (c + 1 - q))) := by
  intro q j hq hqc
  induction h : c + 1 - q generalizing q j with
  | zero =>
    have : q = c + 1 := by omega
    subst this
    exact Timed.refl _ _
  | succ k ih =>
    have hne : q ≠ c + 1 := by omega
    have t1 := Timed.single (p := machine c) (by simp [machine, cfg, hne]) (plus_step c x q j hq (by omega))
    have t2 := ih (q + 1) (j + 1) (by omega) (by omega) (by omega)
    have t := t1.trans t2
    rw [show 1 + k = k + 1 by omega, show j + 1 + k = j + (k + 1) by omega] at t
    exact t

theorem run (c x : ℕ) : Step (machine c) (x + 1 + c) ![0, 0] ![List.replicate x true, []]
    ![x, x + c] ![List.replicate x true, List.replicate (x + c) true] := by
  have t1 := copy_timed c x 0 (by omega)
  have t2 := Timed.single (p := machine c) (by simp [machine, cfg]) (end_step c x)
  have t3 := plus_timed c x 1 x (by omega) (by omega)
  rw [show c + 1 - 1 = c by omega] at t3
  have t := (t1.trans t2).trans t3
  obtain ⟨r, hr, hf, hs⟩ := t.run (by simp [machine, cfg])
  refine ⟨r, ?_, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩
  have hc : (⟨(machine c).start, ![0, 0], ![List.replicate x true, []]⟩ : Configuration 2 (c + 2)) =
      cfg c 0 x 0 0 := rfl
  rw [hc]
  simpa using hr

end CopyPlus

/-- **`x + c` in unary.** -/
def plusMap (c : ℕ) : UnaryMap (fun x => x + c) where
  extra := 1
  states := c + 2 + 2
  machine := MaskedReset.machine (CopyPlus.machine c) (fun _ => true)
  cost := fun x => 2 * (x + 1 + c) + 2
  run := by
    intro x
    obtain ⟨k, hm⟩ := step_mask0 (CopyPlus.run c x) (fun _ => true) (by intro i _; fin_cases i <;> rfl)
    refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_⟩
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp only [Fin.addCases_right]
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp [unIn]
    · rfl
    · rfl

end
end NearCubicWires.PacketsGlue.RequestMeta

