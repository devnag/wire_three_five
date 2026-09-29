import Proof.Wire_3_5.UnionMachine.FrontGate
import Proof.Wire_3_5.UnionMachine.FrontLoopKit

/-! # C6 front, the chain's kit: regions, shared tapes, docking between zero heads, branches

The front's machine runs its stages one after another on the worker's tapes `NW P tf` (the refuter's input `0`, the
witness `1`, the loop bank, then the front's own `tf` tapes). Each stage sits on a REGION of the front's tapes
(**`rg`**: local tape `j` on front tape `k0 + j`) except for the input tapes it shares with earlier stages (**`sl`**).
Before a stage its region is blank (**`Pristine`**: every front tape from `k0` on, and every loop tape, blank);
afterwards the next stage's region still is (**`pristine_after`**).
* **`dockZ`**: a stage between zero heads, docked at injective slots of an ambient bank holding its entry;
* **`iteT`**, **`iteF`**: FinalPass's two-way branch on a flag tape's first cell.

Paper quantity: none (the front's plumbing). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit

/-! ## Docking between zero heads -/

theorem dockZ {t u s : ℕ} {p : Machine t s} {n : ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (slots : Fin t → Fin u) (hinj : Function.Injective slots)
    (A : Fin u → List Bool) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n (fun _ => 0) A (fun _ => 0) (install slots A tout) := by
  have hd := Step.dockAt h slots hinj (fun _ => 0) A (fun _ => rfl) hA
  rwa [dockH_self slots hinj _ _ (fun _ => rfl)] at hd

/-! ## Branches -/

theorem iteT {t a b n : ℕ} (i : Fin t) (p : Machine t a) (q : Machine t b) {H H' : Fin t → ℕ}
    {A A' : Fin t → List Bool} (hb : readTapeBit (A i) (H i) = true) (h : Step p n H A H' A') :
    Step (iteMachine i p q) (n + 1) H A H' A' :=
  ite_branch_step i p q ⟨H, A⟩ ⟨H', A'⟩ n (iteL b) p (by simp [Bank.bit, hb]) (ite_halted_L _ _ _)
    (ite_step_L _ _ _) h

theorem iteF {t a b n : ℕ} (i : Fin t) (p : Machine t a) (q : Machine t b) {H H' : Fin t → ℕ}
    {A A' : Fin t → List Bool} (hb : readTapeBit (A i) (H i) = false) (h : Step q n H A H' A') :
    Step (iteMachine i p q) (n + 1) H A H' A' :=
  ite_branch_step i p q ⟨H, A⟩ ⟨H', A'⟩ n (iteR a) q (by simp [Bank.bit, hb]) (ite_halted_R _ _ _)
    (ite_step_R _ _ _) h

/-! ## Regions and shared tapes -/

section Region
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)

/-- **A region**: local tape `j` on front tape `k0 + j`. -/
noncomputable def rg {t : ℕ} (k0 : ℕ) (h : k0 + t ≤ tf) (j : Fin t) : Fin (NW P tf) :=
  ⟨2 + NL P + (k0 + j.val), by have := j.isLt; show _ < 2 + NL P + tf; omega⟩

theorem rg_val {t : ℕ} (k0 : ℕ) (h : k0 + t ≤ tf) (j : Fin t) : (rg P tf k0 h j).val = 2 + NL P + (k0 + j.val) :=
  rfl

theorem rg_inj {t : ℕ} (k0 : ℕ) (h : k0 + t ≤ tf) : Function.Injective (rg P tf k0 h) := by
  intro a b e
  have := congrArg Fin.val e
  simp only [rg_val] at this
  exact Fin.ext (by omega)

/-- **Shared tapes, then the region.** -/
noncomputable def sl {t : ℕ} (sh : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (h : k0 + t ≤ tf) (j : Fin t) : Fin (NW P tf) :=
  (sh j).getD (rg P tf k0 h j)

theorem sl_inj {t : ℕ} (sh : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (h : k0 + t ≤ tf)
    (hsh : ∀ i j a, sh i = some a → sh j = some a → i = j) (hlow : ∀ i a, sh i = some a → a.val < 2 + NL P + k0) :
    Function.Injective (sl P tf sh k0 h) := by
  intro a b e
  unfold sl at e
  cases ha : sh a with
  | none =>
    cases hb : sh b with
    | none => rw [ha, hb] at e; exact rg_inj P tf k0 h e
    | some y =>
      rw [ha, hb] at e
      have h1 := hlow b y hb
      simp only [Option.getD_none, Option.getD_some] at e
      have := congrArg Fin.val e
      rw [rg_val] at this
      omega
  | some x =>
    cases hb : sh b with
    | none =>
      rw [ha, hb] at e
      have h1 := hlow a x ha
      simp only [Option.getD_none, Option.getD_some] at e
      have := congrArg Fin.val e
      rw [rg_val] at this
      omega
    | some y =>
      rw [ha, hb] at e
      simp only [Option.getD_some] at e
      subst e
      exact hsh a b x ha hb

theorem sl_some {t : ℕ} (sh : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (h : k0 + t ≤ tf) (j : Fin t)
    (a : Fin (NW P tf)) (hj : sh j = some a) : sl P tf sh k0 h j = a := by
  unfold sl; rw [hj]; rfl

theorem sl_none {t : ℕ} (sh : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (h : k0 + t ≤ tf) (j : Fin t)
    (hj : sh j = none) : sl P tf sh k0 h j = rg P tf k0 h j := by
  unfold sl; rw [hj]; rfl

theorem sl_lt {t : ℕ} (sh : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (h : k0 + t ≤ tf)
    (hlow : ∀ i a, sh i = some a → a.val < 2 + NL P + k0) (j : Fin t) :
    (sl P tf sh k0 h j).val < 2 + NL P + (k0 + t) := by
  unfold sl
  cases hj : sh j with
  | none => simp only [Option.getD_none, rg_val]; have := j.isLt; omega
  | some a => simp only [Option.getD_some]; have := hlow j a hj; omega

/-! ## Blank regions -/

theorem lp_val (i : Fin (NL P)) : (lp P tf i).val = 2 + i.val := rfl

/-! ## With heads -/

/-- **Blank and at head `0`**: every front tape from `k0` on and every loop tape. -/
def PristineH (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (k0 : ℕ) : Prop :=
  (∀ y : Fin (NW P tf), 2 + NL P + k0 ≤ y.val → A y = [] ∧ H y = 0) ∧ ∀ i, A (lp P tf i) = [] ∧ H (lp P tf i) = 0

theorem not_slot_of_ge {t : ℕ} (sh : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (h : k0 + t ≤ tf)
    (hlow : ∀ i a, sh i = some a → a.val < 2 + NL P + k0) (y : Fin (NW P tf)) (hy : 2 + NL P + (k0 + t) ≤ y.val) :
    ∀ j, sl P tf sh k0 h j ≠ y := fun j e => by
  have := sl_lt P tf sh k0 h hlow j
  rw [e] at this; omega

theorem not_slot_lp {t : ℕ} (sh : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (h : k0 + t ≤ tf)
    (hshL : ∀ i a, sh i = some a → 2 + NL P ≤ a.val ∨ a.val < 2) (i : Fin (NL P)) :
    ∀ j, sl P tf sh k0 h j ≠ lp P tf i := fun j e => by
  have hi := i.isLt
  have hl := lp_val P tf i
  unfold sl at e
  cases hj : sh j with
  | none =>
    rw [hj] at e
    simp only [Option.getD_none] at e
    have := congrArg Fin.val e
    rw [rg_val, hl] at this
    omega
  | some a =>
    rw [hj] at e
    simp only [Option.getD_some] at e
    have := hshL j a hj
    rw [e, hl] at this
    omega

/-- **After a stage on shared tapes and its region, the rest is still blank at head `0`.** -/
theorem pristineH_after {t : ℕ} (sh : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (h : k0 + t ≤ tf)
    (hlow : ∀ i a, sh i = some a → a.val < 2 + NL P + k0) (hshL : ∀ i a, sh i = some a → 2 + NL P ≤ a.val ∨ a.val < 2)
    (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (hout : Fin t → ℕ) (out : Fin t → List Bool)
    (hA : PristineH P tf H A k0) :
    PristineH P tf (dockH (sl P tf sh k0 h) H hout) (install (sl P tf sh k0 h) A out) (k0 + t) := by
  refine ⟨fun y hy => ?_, fun i => ?_⟩
  · have hn := not_slot_of_ge P tf sh k0 h hlow y hy
    rw [install_other _ _ _ _ hn, dockH_other _ _ _ _ hn]
    exact hA.1 y (by omega)
  · have hn := not_slot_lp P tf sh k0 h hshL i
    rw [install_other _ _ _ _ hn, dockH_other _ _ _ _ hn]
    exact hA.2 i

/-- A pristine tape of the region is blank at head `0`. -/
theorem pristineH_rg {t : ℕ} (k0 : ℕ) (h : k0 + t ≤ tf) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hA : PristineH P tf H A k0) (j : Fin t) : A (rg P tf k0 h j) = [] ∧ H (rg P tf k0 h j) = 0 :=
  hA.1 _ (by rw [rg_val]; omega)

/-! ## Reading a docked bank -/

theorem install_rg {t : ℕ} (sh : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (h : k0 + t ≤ tf)
    (hinj : Function.Injective (sl P tf sh k0 h)) (A : Fin (NW P tf) → List Bool) (out : Fin t → List Bool) (j : Fin t)
    (hj : sh j = none) : install (sl P tf sh k0 h) A out (rg P tf k0 h j) = out j := by
  rw [← sl_none P tf sh k0 h j hj, install_slot _ hinj]

theorem install_sh {t : ℕ} (sh : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (h : k0 + t ≤ tf)
    (hinj : Function.Injective (sl P tf sh k0 h)) (A : Fin (NW P tf) → List Bool) (out : Fin t → List Bool) (j : Fin t)
    (a : Fin (NW P tf)) (hj : sh j = some a) : install (sl P tf sh k0 h) A out a = out j := by
  rw [← sl_some P tf sh k0 h j a hj, install_slot _ hinj]

theorem install_low {t : ℕ} (sh : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (h : k0 + t ≤ tf)
    (A : Fin (NW P tf) → List Bool) (out : Fin t → List Bool) (y : Fin (NW P tf)) (hy : y.val < 2 + NL P + k0)
    (hns : ∀ i a, sh i = some a → a ≠ y) : install (sl P tf sh k0 h) A out y = A y := by
  refine install_other _ _ _ _ (fun j e => ?_)
  unfold sl at e
  cases hj : sh j with
  | none =>
    rw [hj] at e
    simp only [Option.getD_none] at e
    have := congrArg Fin.val e
    rw [rg_val] at this
    omega
  | some a =>
    rw [hj] at e
    simp only [Option.getD_some] at e
    exact hns j a hj e

theorem dockH_rg {t : ℕ} (sh : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (h : k0 + t ≤ tf)
    (hinj : Function.Injective (sl P tf sh k0 h)) (H : Fin (NW P tf) → ℕ) (out : Fin t → ℕ) (j : Fin t)
    (hj : sh j = none) : dockH (sl P tf sh k0 h) H out (rg P tf k0 h j) = out j := by
  rw [← sl_none P tf sh k0 h j hj, dockH_slot _ hinj]

theorem dockH_sh {t : ℕ} (sh : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (h : k0 + t ≤ tf)
    (hinj : Function.Injective (sl P tf sh k0 h)) (H : Fin (NW P tf) → ℕ) (out : Fin t → ℕ) (j : Fin t)
    (a : Fin (NW P tf)) (hj : sh j = some a) : dockH (sl P tf sh k0 h) H out a = out j := by
  rw [← sl_some P tf sh k0 h j a hj, dockH_slot _ hinj]

theorem dockH_low {t : ℕ} (sh : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (h : k0 + t ≤ tf)
    (H : Fin (NW P tf) → ℕ) (out : Fin t → ℕ) (y : Fin (NW P tf)) (hy : y.val < 2 + NL P + k0)
    (hns : ∀ i a, sh i = some a → a ≠ y) : dockH (sl P tf sh k0 h) H out y = H y := by
  refine dockH_other _ _ _ _ (fun j e => ?_)
  unfold sl at e
  cases hj : sh j with
  | none =>
    rw [hj] at e
    simp only [Option.getD_none] at e
    have := congrArg Fin.val e
    rw [rg_val] at this
    omega
  | some a =>
    rw [hj] at e
    simp only [Option.getD_some] at e
    exact hns j a hj e

end Region

/-- **A stage docked at any ambient heads**: zero heads at its slots in, its own exit heads out. -/
theorem dockAny {t u s : ℕ} {p : Machine t s} {n : ℕ} {tin tout : Fin t → List Bool} {hout : Fin t → ℕ}
    (h : Step p n (fun _ => 0) tin hout tout) (slots : Fin t → Fin u) (hinj : Function.Injective slots)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (slots j) = 0) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n H A (dockH slots H hout) (install slots A tout) :=
  Step.dockAt h slots hinj H A hH hA

theorem dockAnyR {t u s : ℕ} {p : Machine t s} {n : ℕ} {tin tout : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p n tin tout) (slots : Fin t → Fin u) (hinj : Function.Injective slots)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (slots j) = 0) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n H A (dockH slots H (fun _ => 0)) (install slots A tout) :=
  dockAny (step_of_ready h) slots hinj H A hH hA

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
