import Proof.Wire_3_5.Transfer.TransferUnionSound
import Proof.Wire_3_5.UnionMachine.UnionEventual

/-! # C6, part 1: the weak machine of a worker (P3:3669-3697)

The union weak machine is base's `OrdinaryWeakMachine` whose verifier is a WORKER machine followed by base's
acceptance gate (`UAcceptanceCarrier.verifier`: two steps, accepting iff the worker's result cell is set), exactly the
shape of the Theorem 2.5 repository's union machine (`CloseoutWitness.Weak.machine`). Unlike base's `Weak.machine`, the worker is required to
halt only on the refuter's witnesses (`⌊N/16⌋` bits, P3:3675-3680), not on every bit list.

* `WitnessRun p ht result fuel meaning`: on every input and every `⌊N/16⌋`-bit witness the worker halts within
  `fuel N` steps with its result cell set iff `meaning N x w`;
* **`weakOf`**, **`weakOf_accepts`**: the weak machine accepts `x` iff some witness has the meaning;
* the useless inhabitants (the 's controls): `rejectAll` (never accepts) and `acceptAll` (accepts every input of
  positive length); **`rejectAll_not_complete`**: it is not eventually complete for a setup with accepting guesses at
  arbitrarily large lengths; **`acceptAll_not_oneSided`**: it is not one-sided for a language with no-instances at
  arbitrarily large lengths. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.Transfer

/-! ## The weak machine of a worker -/

section Weak
variable {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t) (result : Fin t) (fuel : ℕ → ℕ)
  (meaning : (n : ℕ) → BitInput n → List Bool → Prop)

/-- The worker's runs on the refuter's witnesses: halting within `fuel N`, with the result cell set iff the meaning
holds. -/
def WitnessRun : Prop :=
  ∀ (n : ℕ) (x : BitInput n) (w : BitInput (n / 16)), ∃ r,
    run p (fuel n) ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) (List.ofFn w)) = some r ∧
      (r.final.scanned result = true ↔ meaning n x (List.ofFn w))

/-- **The weak machine of a worker**: the worker, then base's two-step acceptance gate. -/
def weakOf (h : WitnessRun p ht result fuel meaning) : OrdinaryWeakMachine where
  verifier := UAcceptanceCarrier.verifier p ht result
  runtime := fun n => fuel n + 2
  halts := by
    intro n x w
    obtain ⟨r, hr, _⟩ := h n x w
    exact ⟨_, (UAcceptanceCarrier.verifier_run p ht result (fuel n) _ _ r hr).1⟩

/-- **The weak machine accepts** exactly when some `⌊N/16⌋`-bit witness has the meaning. -/
theorem weakOf_accepts (h : WitnessRun p ht result fuel meaning) (n : ℕ) (x : BitInput n) :
    (weakOf p ht result fuel meaning h).accepts n x ↔ ∃ w : BitInput (n / 16), meaning n x (List.ofFn w) := by
  unfold OrdinaryWeakMachine.accepts Verifier.language
  apply exists_congr
  intro w
  obtain ⟨r, hr, hm⟩ := h n x w
  exact (UAcceptanceCarrier.accepts_transfer p ht result (fuel n) _ _ r hr).trans hm

end Weak

/-! ## The useless inhabitants -/

/-- A three-tape worker writing `b` into its result cell (tape `2`) in one step. -/
def setWorker (b : Bool) : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun i => if i.val = 2 then some b else none, fun _ => .stay⟩
    else none

theorem setWorker_run (b : Bool) (A : Fin 3 → List Bool) (hA : A 2 = []) :
    ∃ r, run (setWorker b) 1 A = some r ∧ r.final.scanned 2 = b := by
  refine ⟨_, rfl, ?_⟩
  simp [setWorker, initialConfiguration, applyAction, Configuration.scanned, hA, writeTapeBit, readTapeBit,
    HeadMove.apply]

theorem three_le : 2 ≤ 3 := by omega

theorem setWorker_witnessRun (b : Bool) :
    WitnessRun (setWorker b) three_le (2 : Fin 3) (fun _ => 1) (fun n _ _ => b = true ∧ 0 ≤ n) := by
  intro n x w
  obtain ⟨r, hr, hs⟩ := setWorker_run b ((UAcceptanceCarrier.verifier (setWorker b) three_le (2 : Fin 3)).inputTapes
    (List.ofFn x) (List.ofFn w)) (by simp [Verifier.inputTapes, UAcceptanceCarrier.verifier])
  exact ⟨r, hr, by rw [hs]; simp⟩

/-- **The machine that never accepts.** -/
def rejectAll : OrdinaryWeakMachine := weakOf _ _ _ _ _ (setWorker_witnessRun false)

theorem rejectAll_rejects (n : ℕ) (x : BitInput n) : ¬ rejectAll.accepts n x := by
  rw [rejectAll, weakOf_accepts]
  rintro ⟨_, h, _⟩
  exact Bool.false_ne_true h

section Controls

end Controls


end NearCubicWires.WireExponent3_5.UnionMachine
