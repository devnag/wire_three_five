import Proof.MachineModel.BlockPlatform
import Proof.MachineModel.OrdinarySortCarrier

/-! # Block v3 (S5): any receipt-level run is a `Block`

Paper: every component of the primitive is a costed program whose running time is summed into
`prim:runtime` (P3:3105-3108): "The running time, including an optional common-coset selection, is
`2^{n/2+O(k)}n^{C_D} + 2^{O(Ψ_i+Ψ_aux)} + 2^{n-k/4}n^{C_D}`." The components reuse the Theorem 2.5
machines, whose run lemmas are stated at the receipt level (`runFrom p n c = some r` plus facts about
`r`), often only for some of the tapes. A `Block` (`BlockPlatform.Block`) needs the full exit bank.

`ofRunFrom`/`ofRun` take the exit bank of the receipt itself; `runFrom` is a function, so the bank
is that of EVERY successful receipt (`ofRunFrom_exitA`, `ofRunFrom_exitH`), and each partial
specification of the run lemma transfers to the block (`ofRunFrom_spec`). The block's cost is the
run lemma's fuel: the paper quantity is that fuel, the component's running time.

First instance: the Theorem 2.5 radix sorter (`SortCarrier`) as a block whose output tape is the
sorted stream at the sorter's own linear budget. Sorting is the paper's tool for the selection joins
(P3:1343-1347: "Enumerate each half's score vectors. For each of the sixteen corner patterns, count
pairs satisfying its four weak inequalities") and for the printer (P3:1743-1744: "For each `j`, sort
the `2U` labelled entries in its `A` column and `B` row"). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform

/-- Any receipt-level run from a start configuration is a `Block` whose exit bank is the receipt's. -/
noncomputable def ofRunFrom {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r) : Block t :=
  ofStep (Step.of_run (p := p) (n := n) (hin := H) (tin := A) (Classical.choose_spec h) rfl rfl)

/-- A run from the initial configuration (`run p n T`, all heads at cell 0). -/
noncomputable def ofRun {t s : ℕ} (p : Machine t s) (n : ℕ) (T : Fin t → List Bool)
    (h : ∃ r, run p n T = some r) : Block t :=
  ofRunFrom p n (fun _ => 0) T h

@[simp] theorem ofRunFrom_cost {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r) : (ofRunFrom p n H A h).cost = n := rfl

@[simp] theorem ofRunFrom_entryH {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r) : (ofRunFrom p n H A h).entryH = H := rfl

@[simp] theorem ofRunFrom_entryA {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r) : (ofRunFrom p n H A h).entryA = A := rfl

@[simp] theorem ofRunFrom_machine {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r) : (ofRunFrom p n H A h).machine = p := rfl

/-- Determinism: the block's exit tapes are those of ANY successful receipt. -/
theorem ofRunFrom_exitA {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r) (r : ExecutionReceipt t s)
    (hr : runFrom p n ⟨p.start, H, A⟩ = some r) : (ofRunFrom p n H A h).exitA = r.final.tapes := by
  have e : Classical.choose h = r := Option.some.inj ((Classical.choose_spec h).symm.trans hr)
  change (Classical.choose h).final.tapes = r.final.tapes
  rw [e]

/-- Determinism: the block's exit heads are those of ANY successful receipt. -/
theorem ofRunFrom_exitH {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r) (r : ExecutionReceipt t s)
    (hr : runFrom p n ⟨p.start, H, A⟩ = some r) : (ofRunFrom p n H A h).exitH = r.final.heads := by
  have e : Classical.choose h = r := Option.some.inj ((Classical.choose_spec h).symm.trans hr)
  change (Classical.choose h).final.heads = r.final.heads
  rw [e]

@[simp] theorem ofRun_cost {t s : ℕ} (p : Machine t s) (n : ℕ) (T : Fin t → List Bool)
    (h : ∃ r, run p n T = some r) : (ofRun p n T h).cost = n := rfl

@[simp] theorem ofRun_entryH {t s : ℕ} (p : Machine t s) (n : ℕ) (T : Fin t → List Bool)
    (h : ∃ r, run p n T = some r) : (ofRun p n T h).entryH = fun _ => 0 := rfl

@[simp] theorem ofRun_entryA {t s : ℕ} (p : Machine t s) (n : ℕ) (T : Fin t → List Bool)
    (h : ∃ r, run p n T = some r) : (ofRun p n T h).entryA = T := rfl

theorem ofRun_exitA {t s : ℕ} (p : Machine t s) (n : ℕ) (T : Fin t → List Bool)
    (h : ∃ r, run p n T = some r) (r : ExecutionReceipt t s) (hr : run p n T = some r) :
    (ofRun p n T h).exitA = r.final.tapes :=
  ofRunFrom_exitA p n (fun _ => 0) T h r hr

theorem ofRun_exitH {t s : ℕ} (p : Machine t s) (n : ℕ) (T : Fin t → List Bool)
    (h : ∃ r, run p n T = some r) (r : ExecutionReceipt t s) (hr : run p n T = some r) :
    (ofRun p n T h).exitH = r.final.heads :=
  ofRunFrom_exitH p n (fun _ => 0) T h r hr

/-! ## The sorter as a block -/

open NearCubicWires.RepairOrdinary.StablePartition NearCubicWires.RepairOrdinary.RadixSemantics


end NearCubicWires.WireExponent3_5.Block
