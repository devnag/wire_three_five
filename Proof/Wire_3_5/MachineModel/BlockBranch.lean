import Proof.Wire_3_5.MachineModel.BlockCost
import Proof.Amplification.RecoveryCursorCalls

/-! # Block v3 (S5): the conditional block (branch on a scanned bit)

Paper: the primitive's programs decide per step.
- The elimination (P3:2950-2957): a row is XORed into the others exactly when its pivot bit is set.
- The weak machine (P3:3669-3680): each guess is admitted only after a checked guard.
- The filters (P3:2016-2104): a bit decides the branch.

The paper quantity of the main type is the value on which the branch is taken: the bit under the head
of one tape at the entry bank. `branch i b c` runs `b` when that bit is set and `c` otherwise, as ONE
machine: the finite call graph `RecoveryCalls.machine` over an idle test point, `b` and `c`. Its exit
bank is the taken branch's (`branch_exit`), and its cost is the taken branch's cost plus the two paid
transfers (`branch_cost`), within `max b.cost c.cost + 2`, a class-agnostic overhead
(`Within.branch`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.BlockPlatform

/-- The test point: a one-state program that has already halted. -/
def idle (t : ℕ) : Machine t 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

section
variable {t : ℕ}

/-- The bit the branch reads: tape `i` under its head, at the entry bank. -/
def entryBit (H : Fin t → ℕ) (A : Fin t → List Bool) (i : Fin t) : Bool := readTapeBit (A i) (H i)

end

/-! ## One-sided branches over fixed machines

A uniform program runs the SAME machine at every input, but only the taken branch has a run at a given
input (the other branch's preconditions may fail there). `branchM i p q` is the conditional over two
machines. `branchT` and `branchF` are its blocks when the bit is set, respectively clear: only the taken
branch needs a `Block`. -/

section
variable {t : ℕ}

def sizesM (s₁ s₂ : ℕ) : Fin 3 → ℕ := ![1, s₁, s₂]

def programsM {s₁ s₂ : ℕ} (p : Machine t s₁) (q : Machine t s₂) : (j : Fin 3) → Machine t (sizesM s₁ s₂ j)
  | 0 => idle t
  | 1 => p
  | 2 => q

def nextM (s₁ s₂ : ℕ) (i : Fin t) : (j : Fin 3) → Fin (sizesM s₁ s₂ j) → (Fin t → Bool) → Option (Fin 3)
  | 0, _, bits => if bits i then some 1 else some 2
  | 1, _, _ => none
  | 2, _, _ => none

/-- The conditional over two fixed machines. -/
noncomputable def branchM (i : Fin t) {s₁ s₂ : ℕ} (p : Machine t s₁) (q : Machine t s₂) :=
  RecoveryCalls.machine (sizesM s₁ s₂) (programsM p q) 0 (nextM s₁ s₂ i)

theorem branchM_timed (i : Fin t) {s₁ s₂ : ℕ} (p : Machine t s₁) (q : Machine t s₂) (l : Fin 3) (hl : l = 1 ∨ l = 2)
    (H : Fin t → ℕ) (A : Fin t → List Bool)
    (hpick : (if entryBit H A i then (1 : Fin 3) else 2) = l)
    (fuel : ℕ) (r : ExecutionReceipt t (sizesM s₁ s₂ l))
    (hr : runFrom (programsM p q l) fuel ⟨(programsM p q l).start, H, A⟩ = some r) :
    ∃ n ≤ 0 + 1 + (fuel + 1), Timed (branchM i p q) n
      (controlConfig (RecoveryCalls.code (sizesM s₁ s₂) 0) ⟨(idle t).start, H, A⟩)
      (RecoveryCalls.stopped (sizesM s₁ s₂) r.final.heads r.final.tapes) := by
  have hidle := runFrom_zero_of_halted (idle t) ⟨(idle t).start, H, A⟩ rfl
  obtain ⟨u, hu, first⟩ := call_receipt (sizesM s₁ s₂) (programsM p q) 0 (nextM s₁ s₂ i) 0 l 0
    ⟨(idle t).start, H, A⟩ _ hidle (by
      change (if readTapeBit (A i) (H i) then some (1 : Fin 3) else some 2) = some l
      rw [← hpick]
      unfold entryBit
      split <;> rfl)
  obtain ⟨v, hv, tail⟩ := stop_receipt (sizesM s₁ s₂) (programsM p q) 0 (nextM s₁ s₂ i) l fuel _ r hr
    (by rcases hl with rfl | rfl <;> rfl)
  exact ⟨u + v, by omega, first.trans tail⟩

/-- The taken branch is `b` (the bit is set); the other branch is only a machine. -/
noncomputable def branchT (i : Fin t) (b : Block t) {s₂ : ℕ} (q : Machine t s₂)
    (hbit : entryBit b.entryH b.entryA i = true) : Block t where
  states := Fintype.card (RecoveryCalls.Control (sizesM b.states s₂))
  machine := branchM i b.machine q
  cost := b.cost + 2
  entryH := b.entryH
  entryA := b.entryA
  exitH := b.exitH
  exitA := b.exitA
  run := by
    obtain ⟨r, hr, hh, ht, _⟩ := b.run
    obtain ⟨n, hn, htimed⟩ := branchM_timed i b.machine q 1 (Or.inl rfl) b.entryH b.entryA (by rw [if_pos hbit])
      b.cost r hr
    obtain ⟨actual, ha, haf, has⟩ := htimed.run (by simp [branchM, RecoveryCalls.machine, RecoveryCalls.stopped])
    have more := runFrom_moreFuel (branchM i b.machine q) n (b.cost + 2 - n) _ actual ha
    rw [Nat.add_sub_of_le (by omega)] at more
    refine ⟨actual, more, ?_, ?_, by omega⟩
    · rw [haf, ← hh]; rfl
    · rw [haf, ← ht]; rfl

/-- The taken branch is `c` (the bit is clear); the other branch is only a machine. -/
noncomputable def branchF (i : Fin t) {s₁ : ℕ} (p : Machine t s₁) (c : Block t)
    (hbit : entryBit c.entryH c.entryA i = false) : Block t where
  states := Fintype.card (RecoveryCalls.Control (sizesM s₁ c.states))
  machine := branchM i p c.machine
  cost := c.cost + 2
  entryH := c.entryH
  entryA := c.entryA
  exitH := c.exitH
  exitA := c.exitA
  run := by
    obtain ⟨r, hr, hh, ht, _⟩ := c.run
    obtain ⟨n, hn, htimed⟩ := branchM_timed i p c.machine 2 (Or.inr rfl) c.entryH c.entryA
      (by rw [if_neg (by simp [hbit])]) c.cost r hr
    obtain ⟨actual, ha, haf, has⟩ := htimed.run (by simp [branchM, RecoveryCalls.machine, RecoveryCalls.stopped])
    have more := runFrom_moreFuel (branchM i p c.machine) n (c.cost + 2 - n) _ actual ha
    rw [Nat.add_sub_of_le (by omega)] at more
    refine ⟨actual, more, ?_, ?_, by omega⟩
    · rw [haf, ← hh]; rfl
    · rw [haf, ← ht]; rfl

@[simp] theorem branchT_cost (i : Fin t) (b : Block t) {s₂ : ℕ} (q : Machine t s₂)
    (hbit : entryBit b.entryH b.entryA i = true) : (branchT i b q hbit).cost = b.cost + 2 := rfl
@[simp] theorem branchF_cost (i : Fin t) {s₁ : ℕ} (p : Machine t s₁) (c : Block t)
    (hbit : entryBit c.entryH c.entryA i = false) : (branchF i p c hbit).cost = c.cost + 2 := rfl

end


end NearCubicWires.WireExponent3_5.Block
