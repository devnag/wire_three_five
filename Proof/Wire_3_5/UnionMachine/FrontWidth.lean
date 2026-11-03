import Proof.Wire_3_5.UnionMachine.FrontFill
import Proof.Wire_3_5.UnionMachine.FrontClog
import Proof.Wire_3_5.UnionMachine.FrontWidthTail
import Proof.Wire_3_5.Ledger.LedgerWidth
import Proof.Hierarchy.HierarchyFromInput

/-! # C6 front, U2: the native width `q(N)` in unary (P3:3637-3640)

Realizes "pad the outer verifier to the exact width `q(N)=⌈log₂T(N)⌉+A_pad⌈log₂(log₂T(N)+2)⌉+A_pad`" (P3:3637-3640) as
a machine the union's front runs from the refuter's framed input `x` (`N = |x|`, `T(N) = N^{kclk+2}`):
1. base's `HierarchyFromInput` (`C = 1`): `binary W (N^{k+2}+1)` framed, and `1^W`, `W = (k+2)·ell N + 4`;
2. `FrontFill.fillP`: six register tapes blank at capacity `2W + 2`;
3. the register bank's cell `[false]`;
4. `FrontClog.clogP` docked on the bank: `1^{⌈log₂ N^{k+2}⌉}`;
5. `FrontWidthTail.tailMachine` docked with its input tape on that word: `1^{q(N)}`.

Main statement: **`qMachine_ready`**: a ready run (all heads back at `0`) from the framed input to `1^{q(N)}` on
`qOut`, with `q(N) = Ledger.nativeWidth kclk A_pad N`, the ledger's width `B.q N` (the union's `n` field, the oracle's
arity and the padded width past the onset). Paper quantity: `q(N)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontWidth
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.UnionMachine

variable (k A : ℕ)

theorem hD : 0 < k + 2 := by omega

/-- The hierarchy-input machine's tapes. -/
noncomputable abbrev hT : ℕ := HierarchyFromInput.tapes (k + 2)

/-- The width machine's tapes: base's, then 37 of its own. -/
noncomputable abbrev QT : ℕ := hT k + 37

/-- Base's tapes inside. -/
noncomputable def hs (i : Fin (hT k)) : Fin (QT k) := Fin.castAdd 37 i

/-- The extra tapes: `0–5` registers, `6` marker, `7` cell, `8` `B`, `9` `Y`, `10–36` the tail's own. -/
noncomputable def ex (j : Fin 37) : Fin (QT k) := Fin.natAdd (hT k) j

theorem hs_val (i : Fin (hT k)) : (hs k i).val = i.val := rfl
theorem ex_val (j : Fin 37) : (ex k j).val = hT k + j.val := rfl

theorem hs_inj : Function.Injective (hs k) := by
  intro i j h; exact Fin.ext (by simpa [hs_val] using congrArg Fin.val h)
theorem hs_ne_ex (i : Fin (hT k)) (j : Fin 37) : hs k i ≠ ex k j := by
  intro h; have := congrArg Fin.val h; simp only [hs_val, ex_val] at this; have := i.isLt; omega

/-- The input field, the count and the framed binary clock of base's machine. -/
noncomputable def inT : Fin (QT k) := hs k (HierarchyFromInput.field (k + 2) 2)
noncomputable def cntT : Fin (QT k) := hs k (HierarchyFromInput.field (k + 2) 11)
noncomputable def outT : Fin (QT k) := hs k (HierarchyFromInput.outputTape (k + 2) (hD k))

/-- The register tapes (the fill's targets). -/
noncomputable def tgt (i : Fin (QT k)) : Bool := decide (hT k ≤ i.val ∧ i.val < hT k + 6)

noncomputable def auxT : Fin (QT k) := ex k 6
noncomputable def cellT : Fin (QT k) := ex k 7
noncomputable def YT : Fin (QT k) := ex k 9

/-- The register bank's slots: stream `A` = the clock word, the cell, streams `B`, `Y`, the six registers. -/
noncomputable def wsl (j : Fin (2 + 2 + 6)) : Fin (QT k) :=
  if j.val = 0 then outT k else ex k ⟨if j.val = 1 then 7 else if j.val = 2 then 8 else if j.val = 3 then 9
    else j.val - 4, by have := j.isLt; split_ifs <;> omega⟩

/-- The tail's slots: its input tape `3` is `Y`, the others are the tail's own. -/
noncomputable def tsl (j : Fin 28) : Fin (QT k) :=
  if j.val = 3 then YT k else ex k ⟨if j.val < 3 then 10 + j.val else 9 + j.val, by have := j.isLt; split_ifs <;> omega⟩

/-- The width's output tape. -/
noncomputable def qOut : Fin (QT k) := tsl k 26

/-- The cell's writer. -/
noncomputable def cellP : Prog (QT k) := .act (fun i => if i = cellT k then some false else none) (fun _ => .stay)

/-- **The width machine.** -/
noncomputable def qMachine :=
  Composition.machine (RecoveryFocus.machine (hs k) (HierarchyFromInput.machine (k + 2) 1 (hD k)))
  (Composition.machine (FrontFill.fillP (cntT k) (auxT k) (tgt k)).compile
  (Composition.machine (cellP k).compile
  (Composition.machine (RecoveryFocus.machine (wsl k) FrontClog.clogP.toProg.compile)
    (RecoveryFocus.machine (tsl k) (FrontWidthTail.tailMachine A)))))

/-- The input: the framed `x` on base's input field. -/
noncomputable def qInput (x : List Bool) : Fin (QT k) → List Bool := fun i => if i = inT k then frame x else []

/-! ## Bookkeeping -/

/-- A step between zero heads is a ready run. -/
theorem ready_of_step {t s : ℕ} {p : Machine t s} {n : ℕ} {A A' : Fin t → List Bool}
    (h : Step p n (fun _ => 0) A (fun _ => 0) A') : ClockJoin.ReadyRun p n A A' := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  exact ⟨r, hr, ht, fun i => by rw [hh], hs⟩

theorem outT_lt : (outT k).val < hT k := (HierarchyFromInput.outputTape (k + 2) (hD k)).isLt

theorem wsl_val (j : Fin (2 + 2 + 6)) (hj : j.val ≠ 0) : (wsl k j).val = hT k +
    (if j.val = 1 then 7 else if j.val = 2 then 8 else if j.val = 3 then 9 else j.val - 4) := by
  simp [wsl, hj, ex_val]

theorem wsl_inj : Function.Injective (wsl k) := by
  intro i j h
  have hv := congrArg Fin.val h
  have ho := outT_lt k
  have hi := i.isLt
  have hj := j.isLt
  by_cases hi0 : i.val = 0
  · by_cases hj0 : j.val = 0
    · exact Fin.ext (by omega)
    · rw [wsl_val k j hj0] at hv
      simp only [wsl, hi0, if_true] at hv
      split_ifs at hv <;> omega
  · rw [wsl_val k i hi0] at hv
    by_cases hj0 : j.val = 0
    · simp only [wsl, hj0, if_true] at hv
      split_ifs at hv <;> omega
    · rw [wsl_val k j hj0] at hv
      apply Fin.ext
      split_ifs at hv <;> omega

theorem tsl_val (j : Fin 28) : (tsl k j).val = hT k +
    (if j.val = 3 then 9 else if j.val < 3 then 10 + j.val else 9 + j.val) := by
  unfold tsl YT
  by_cases h3 : j.val = 3
  · simp [h3, ex_val]
  · simp only [h3, if_false]; simp [ex_val]

theorem tsl_inj : Function.Injective (tsl k) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [tsl_val, tsl_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem tsl_ge (j : Fin 28) : hT k + 9 ≤ (tsl k j).val := by
  rw [tsl_val]; split_ifs <;> omega

theorem wsl_image (i : Fin (QT k)) (h : hT k + 10 ≤ i.val) : ∀ j, wsl k j ≠ i := by
  intro j hj
  have hv := congrArg Fin.val hj
  have ho := outT_lt k
  by_cases hj0 : j.val = 0
  · simp only [wsl, hj0, if_true] at hv; omega
  · rw [wsl_val k j hj0] at hv
    have := j.isLt
    split_ifs at hv <;> omega

/-! ## The run -/

theorem width_eq (N : ℕ) : HierarchyBinary.width 1 (k + 2) N = (k + 2) * PCPResourceLedger.ell N + 4 := by
  have h1 : (1 : ℕ).bits.length = 1 := by rfl
  simp only [HierarchyBinary.width, h1]

theorem width_fits (N : ℕ) : 2 * N ^ (k + 2) + 2 ≤ 2 ^ HierarchyBinary.width 1 (k + 2) N := by
  have hp := HierarchyBinary.power_bound (k + 2) N
  rw [width_eq, show (2 : ℕ) ^ ((k + 2) * PCPResourceLedger.ell N + 4) =
    2 ^ ((k + 2) * PCPResourceLedger.ell N) * 16 by rw [pow_add]; norm_num]
  have h1 : 1 ≤ 2 ^ ((k + 2) * PCPResourceLedger.ell N) := Nat.one_le_two_pow
  omega

theorem width_pos (N : ℕ) : 1 ≤ HierarchyBinary.width 1 (k + 2) N := by rw [width_eq]; omega

end NearCubicWires.WireExponent3_5.UnionMachine.FrontWidth
