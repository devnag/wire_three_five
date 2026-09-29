import Proof.Wire_3_5.FinalPass.Core10
import Proof.Wire_3_5.FinalPass.CoreIfaceM

/-! # S5Core, part 11: the core half's layout and machine (P3:3170-3181)

* **`CoreWriters l`** (the four writers: S4's words part A and part B, the numbers, the SYM words, machine forms of
  `CoreIfaceM`), their blocks' sizes and offsets, **`mCoreOf W`** (the core's room at `l`: the count `5`, the mode `5`,
  then the writers' layouts);
* on a bank `L` with the core's room: the reference `Tc` (the count's output tape), the count's template `cTt`, the
  mode tape `Mb`, the writers' output maps `outA`, `outB`, `outN`, `outS` and their injectivity, `regList` (every
  register tape off the words, the numbers and the reference);
* **`coreM`**: the count ; the mode ; part A ; part B ; the numbers ; if SYM then the SYM words ; every register tape
  padded against `Tc` ; `Tc` erased.

Paper quantity: none (the front's machine assembly, P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.Finish

/-- **The core half's writers** at `l` (the machine forms). -/
structure CoreWriters (l : Literals) where
  SA : S4WordsMA l
  SB : S4WordsMB l
  NW : NumsM l
  SW : SymWordsM l

section Lay
variable {l : Literals} (W : CoreWriters l)

def szA : ℕ := W.SA.ns + 2 + W.SA.nr
def szB : ℕ := W.SB.ns + 2 + W.SB.nr
def szN : ℕ := W.NW.ns + 2 + W.NW.nr
def szS : ℕ := W.SW.ns + 2 + W.SW.nr
def oB : ℕ := 10 + szA W
def oN : ℕ := oB W + szB W
def oS : ℕ := oN W + szN W

/-- **The core's room** at `l`: the count, the mode, the four writers' blocks. -/
def mCoreOf : ℕ := oS W + szS W


end Lay

section Tapes
variable {l : Literals} (W : CoreWriters l) {mTh : ℕ} (L : S5Lay Sw0.nw) (hR : Bank.HalfRoom2 L mTh (mCoreOf W))

/-- Part A's outputs: S4's slots `0 … 3`. -/
def outA (k : Fin 4) : Fin L.t := L.wd (s4SlotA k)
/-- Part B's outputs: S4's slots `4 … 7`. -/
def outB (k : Fin 4) : Fin L.t := L.wd (s4SlotB k)
/-- The numbers' outputs. -/
def outN : Fin 2 → Fin L.t := ![L.tN, L.tD]
/-- The SYM words' outputs: the SYM slots. -/
def outS (k : Fin 17) : Fin L.t := L.wd (symSlot k)

theorem outA_inj : Function.Injective (outA L) := fun a b h => by
  have := congrArg Fin.val (L.wdInj h); simp [s4SlotA] at this; exact Fin.ext this
theorem outB_inj : Function.Injective (outB L) := fun a b h => by
  have := congrArg Fin.val (L.wdInj h); simp [s4SlotB] at this; exact Fin.ext this
theorem outS_inj : Function.Injective (outS L) := fun a b h => by
  have := congrArg Fin.val (L.wdInj h); simp [symSlot] at this; exact Fin.ext this
theorem outN_inj : Function.Injective (outN L) := fun a b h => by
  fin_cases a <;> fin_cases b <;> simp [outN] at h ⊢ <;> first | exact absurd h L.hND | exact absurd h.symm L.hND

theorem wd_ne0 (k : Fin (17 + Sw0.nw)) : L.wd k ≠ i0 L := fun e => L.in0 k (by rw [e]; rfl)

theorem outN_ne0 (k : Fin 2) : outN L k ≠ i0 L := by
  fin_cases k
  · exact fun e => L.inN (by simp [outN] at e; rw [e]; rfl)
  · exact fun e => L.inD (by simp [outN] at e; rw [e]; rfl)

/-- **Every register tape off the words, the numbers and the reference.** -/
noncomputable def regList (T : Fin L.t) : List (Fin L.t) := by
  classical
  exact (List.finRange L.t).filter (fun y => L.reg y = true ∧ (∀ k, y ≠ L.wd k) ∧ y ≠ L.tN ∧ y ≠ L.tD ∧ y ≠ T)

theorem mem_regList (T y : Fin L.t) :
    y ∈ regList L T ↔ L.reg y = true ∧ (∀ k, y ≠ L.wd k) ∧ y ≠ L.tN ∧ y ≠ L.tD ∧ y ≠ T := by
  classical
  unfold regList; simp

theorem regList_nodup (T : Fin L.t) : (regList L T).Nodup := by
  classical
  unfold regList; exact (List.nodup_finRange _).filter _

theorem regList_length (T : Fin L.t) : (regList L T).length ≤ L.t := by
  classical
  unfold regList
  exact (List.length_filter_le _ _).trans (by simp)

end Tapes

section Mach

end Mach

end NearCubicWires.WireExponent3_5.FinalPass.Core
