import Proof.Wire_3_5.FinalPass.AssemblyDock2
import Proof.Wire_3_5.FinalPass.SeamsBank2Base
import Proof.Wire_3_5.FinalPass.SeamsProg3Base
import Proof.Wire_3_5.Primitive.Writers.DockW

/-! # BridgeT, part 1: the seeds phase's bank layout (P3:3170-3181)

S4 (`SeedsWS2`) is a word machine on `ns + 2 + nr` tapes. The seeds phase (`SeedsProg4`) runs on one bank shared with
the front's halves and the out machine: **`tB`** tapes, namely the input tape `0`, S4's tapes (**`e4`**, shifted by
one), the THR room (**`thrT`**), the core room (**`coreT`**) and the idle room (**`idleT`**, kept by the seeds phase,
for the out machine). The register-length tapes (**`regB`**) are tape `0`, S4's registers and both rooms.

* **`cellP`**, **`cell_step`**: one action writing S4's result cell `false` on its blank tape (the front leaves it
  blank);
* **`σIn`**: S4's entry state read off the bank; **`pc`**, **`pad_entry`**: after the cell step, S4's tapes of the
  bank are S4's entry encoding with the registers zero-padded from S4's capacity `c` to the bank's `c' ≥ c`
  (`regTape c 0` padded to `c' + 1` is `regTape c' 0`); **`wenc_H0`**.

Paper quantity of the main types: none (the machine layout; the consumers' types carry the paper's words). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Bridge
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other install_existing)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_inj rTape_inj sTape_ne_c sTape_ne_r cTape_ne_r
  wenc_A_c wenc_H_c)

section Lay
variable (ns nr mT mC mI : ℕ)

/-- **The bank's tape count**: the input tape, S4's tapes, the THR room, the core room, the idle room. -/
def tB : ℕ := 1 + (ns + 2 + nr) + mT + mC + mI

/-- S4's tapes in the bank. -/
def e4 (j : Fin (ns + 2 + nr)) : Fin (tB ns nr mT mC mI) := ⟨1 + j.val, by have := j.isLt; unfold tB; omega⟩

theorem e4_val (j : Fin (ns + 2 + nr)) : (e4 ns nr mT mC mI j).val = 1 + j.val := rfl

theorem e4_inj : Function.Injective (e4 ns nr mT mC mI) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp only [e4_val] at this; omega)

/-- The THR room. -/
def thrT (i : Fin mT) : Fin (tB ns nr mT mC mI) := ⟨1 + (ns + 2 + nr) + i.val, by have := i.isLt; unfold tB; omega⟩

/-- The core room. -/
def coreT (i : Fin mC) : Fin (tB ns nr mT mC mI) :=
  ⟨1 + (ns + 2 + nr) + mT + i.val, by have := i.isLt; unfold tB; omega⟩

/-- The idle room. -/
def idleT (i : Fin mI) : Fin (tB ns nr mT mC mI) :=
  ⟨1 + (ns + 2 + nr) + mT + mC + i.val, by have := i.isLt; unfold tB; omega⟩

/-- **The register-length tapes**: tape `0`, S4's registers, both rooms. -/
def regB (j : Fin (tB ns nr mT mC mI)) : Bool :=
  decide (j.val = 0 ∨ (ns + 3 ≤ j.val ∧ j.val < 1 + (ns + 2 + nr) + mT + mC))

/-- The THR room's tapes. -/
def thrB (j : Fin (tB ns nr mT mC mI)) : Bool :=
  decide (1 + (ns + 2 + nr) ≤ j.val ∧ j.val < 1 + (ns + 2 + nr) + mT)

/-- The core room's tapes. -/
def coreB (j : Fin (tB ns nr mT mC mI)) : Bool :=
  decide (1 + (ns + 2 + nr) + mT ≤ j.val ∧ j.val < 1 + (ns + 2 + nr) + mT + mC)

/-- The idle room's tapes. -/
def idleB (j : Fin (tB ns nr mT mC mI)) : Bool := decide (1 + (ns + 2 + nr) + mT + mC ≤ j.val)

/-- S4's result cell in the bank. -/
def cellB : Fin (tB ns nr mT mC mI) := e4 ns nr mT mC mI cTape

theorem cellB_val : (cellB ns nr mT mC mI).val = 2 := rfl

theorem e4_s_val (i : Fin (ns + 1)) :
    (e4 ns nr mT mC mI (sTape (nr := nr) i)).val = 1 + (if i.val = 0 then 0 else i.val + 1) := rfl

theorem e4_r_val (q : Fin nr) : (e4 ns nr mT mC mI (rTape (ns := ns) q)).val = 1 + (ns + 2 + q.val) := rfl

theorem regB_s (i : Fin (ns + 1)) : regB ns nr mT mC mI (e4 ns nr mT mC mI (sTape (nr := nr) i)) = false := by
  unfold regB; rw [e4_s_val]; have := i.isLt; split_ifs <;> simp <;> omega

theorem regB_c : regB ns nr mT mC mI (cellB ns nr mT mC mI) = false := by
  unfold regB; rw [cellB_val]; simp

theorem regB_r (q : Fin nr) : regB ns nr mT mC mI (e4 ns nr mT mC mI (rTape (ns := ns) q)) = true := by
  unfold regB; rw [e4_r_val]; have := q.isLt; simp; omega

/-! ## The cell step -/

/-- Write S4's result cell `false`. -/
def cellP : Prog (tB ns nr mT mC mI) :=
  .act (fun j => if j = cellB ns nr mT mC mI then some false else none) (fun _ => HeadMove.stay)

theorem cell_step (Ab : Fin (tB ns nr mT mC mI) → List Bool) (h : Ab (cellB ns nr mT mC mI) = []) :
    Step (cellP ns nr mT mC mI).compile 1 (fun _ => 0) Ab (fun _ => 0)
      (Function.update Ab (cellB ns nr mT mC mI) [false]) := by
  refine (Exec.step (Exec.act ⟨fun _ => 0, Ab⟩ (fun j => if j = cellB ns nr mT mC mI then some false else none)
    (fun _ => HeadMove.stay))).congr rfl (funext fun i => ?_)
  by_cases hi : i = cellB ns nr mT mC mI
  · subst hi; simp [Bank.act, h, writeTapeBit]
  · simp [Bank.act, hi, Function.update_of_ne hi]

/-! ## S4's entry -/

/-- S4's entry state read off the bank. -/
def σIn (Ab : Fin (tB ns nr mT mC mI) → List Bool) : WState ns nr :=
  ⟨fun _ => 0, fun i => Ab (e4 ns nr mT mC mI (sTape i)), fun _ => 0, false⟩

/-- The zero-padding capacities: `c' + 1` on S4's registers, none elsewhere. -/
def pc (c' : ℕ) (j : Fin (ns + 2 + nr)) : ℕ := if ns + 2 ≤ j.val then c' + 1 else 0

theorem pad_replicate (c c' : ℕ) (h : c ≤ c') :
    ZeroPadding.pad (c' + 1) (List.replicate (c + 1) false) = List.replicate (c' + 1) false := by
  unfold ZeroPadding.pad
  rw [List.length_replicate, ← List.replicate_add]
  congr 1
  omega

theorem wenc_H0 (cap : ℕ) (σ : WState ns nr) (hs : ∀ i, σ.sh i = 0) (hv : ∀ q, σ.val q = 0) :
    (wenc cap σ).H = fun _ => 0 := by
  funext j
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
  · rw [wenc_H_s, hs]
  · rw [wenc_H_c]
  · rw [wenc_H_r, hv]

/-- **After the cell step, S4's tapes of the bank are its entry encoding, the registers padded.** -/
theorem pad_entry (c c' : ℕ) (hcc : c ≤ c') (Ab : Fin (tB ns nr mT mC mI) → List Bool)
    (hreg : ∀ q : Fin nr, Ab (e4 ns nr mT mC mI (rTape q)) = List.replicate (c' + 1) false) :
    (fun j => ZeroPadding.pad (pc ns nr c' j) ((wenc c (σIn ns nr mT mC mI Ab)).A j)) =
      fun j => Function.update Ab (cellB ns nr mT mC mI) [false] (e4 ns nr mT mC mI j) := by
  funext j
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
  · have hne : e4 ns nr mT mC mI (sTape (nr := nr) i) ≠ cellB ns nr mT mC mI := fun e =>
      sTape_ne_c i (e4_inj ns nr mT mC mI e)
    rw [Function.update_of_ne hne, wenc_A_s]
    have h0 : pc ns nr c' (sTape (nr := nr) i) = 0 := by
      unfold pc; rw [if_neg (by rw [PrimAsm.DockW.sTape_val]; have := i.isLt; split_ifs <;> omega)]
    rw [h0, ZeroPadding.pad_zero]
    rfl
  · rw [wenc_A_c]
    have h0 : pc ns nr c' (cTape (ns := ns) (nr := nr)) = 0 := by
      unfold pc; rw [if_neg (by rw [PrimAsm.DockW.cTape_val]; omega)]
    rw [h0, ZeroPadding.pad_zero]
    show [false] = Function.update Ab (cellB ns nr mT mC mI) [false] (cellB ns nr mT mC mI)
    rw [Function.update_self]
  · have hne : e4 ns nr mT mC mI (rTape (ns := ns) q) ≠ cellB ns nr mT mC mI := fun e =>
      cTape_ne_r q (e4_inj ns nr mT mC mI e).symm
    rw [Function.update_of_ne hne, wenc_A_r, hreg]
    have h1 : pc ns nr c' (rTape (ns := ns) q) = c' + 1 := by
      unfold pc; rw [if_pos (by rw [PrimAsm.DockW.rTape_val]; omega)]
    rw [h1]
    show ZeroPadding.pad (c' + 1) (regTape c 0) = _
    rw [regTape_zero, pad_replicate c c' hcc]

end Lay

end NearCubicWires.WireExponent3_5.FinalPass.Bridge
