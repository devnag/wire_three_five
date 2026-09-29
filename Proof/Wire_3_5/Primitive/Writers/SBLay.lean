import Proof.Wire_3_5.Primitive.Writers.Dock0
import Proof.Wire_3_5.Primitive.Writers.SBInv
import Proof.Wire_3_5.Primitive.Writers.SBP1R
import Proof.Wire_3_5.Primitive.Writers.SymFam

/-! # SB, part (3a): SB's layout, machine and capacity split

* the layout: the streams (`fsX`) and registers (`frX`) first, the field phase's `23` streams `FsB`, the
  output streams `o6`, `o7`; the field registers `RbB = 96 …`; `sInB`, the count streams, `sOutB`;
* **`sbMach`**: the carrier pipeline docked (`wslot fsX frX`), then P1, the field phase, and the register clears;
* **`need_parts`**: every capacity hypothesis of the parts from `sbNeed ≤ cap`.

Paper quantities of the main types: S4's words `4 … 7` at a star call (`s4Core2`, P3:3170-3181) and SB's budget
(`prim:runtime`, P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.WireExponent3_5.FinalPass.Out.Car
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarL NearCubicWires.WireExponent3_5.FinalPass.Out.CarS
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarPipe NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound
open NearCubicWires.WireExponent3_5.PrimAsm.SBNums NearCubicWires.WireExponent3_5.PrimAsm.SBTypes
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.DockW

/-! ## Layout -/

/-- SB's stream count: `NS + 1` streams, the field phase's `23`, the two output streams. -/
abbrev nsB : ℕ := NS + 25

/-- The streams, first. -/
def fsX (i : Fin (NS + 1)) : Fin (nsB + 1) := Fin.castLE (by unfold nsB; omega) i

/-- The registers, first. -/
def frX (r : Fin NR) : Fin NRB := Fin.castLE (by decide) r

theorem fsX_val (i : Fin (NS + 1)) : (fsX i).val = i.val := rfl
theorem fsX_inj : Function.Injective fsX := fun a b h => Fin.ext (by have := congrArg Fin.val h; exact this)
theorem frX_inj : Function.Injective frX := fun a b h => Fin.ext (by have := congrArg Fin.val h; exact this)

/-- The field phase's streams `NS + 1 … NS + 23`. -/
def FsB : Fin 23 ↪ Fin (nsB + 1) := ⟨fun k => ⟨NS + 1 + k.val, by have := k.isLt; unfold nsB; omega⟩,
  fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; exact this)⟩

theorem FsB_val (k : Fin 23) : (FsB k).val = NS + 1 + k.val := rfl

/-- The field registers `96 … 111`. -/
def RbB : Fin 16 ↪ Fin NRB := ⟨fun k => ⟨96 + k.val, by have := k.isLt; unfold NRB; omega⟩,
  fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; exact this)⟩

theorem RbB_val (k : Fin 16) : (RbB k).val = 96 + k.val := rfl

/-- The output streams of words `6`, `7`. -/
def o6 : Fin (nsB + 1) := ⟨NS + 24, by unfold nsB; omega⟩
def o7 : Fin (nsB + 1) := ⟨NS + 25, by unfold nsB; omega⟩

theorem o6_val : o6.val = NS + 24 := rfl
theorem o7_val : o7.val = NS + 25 := rfl

/-- The request stream and the three count streams. -/
def sInB : Fin (nsB + 1) := fsX (oS sIN)
def cS0 : Fin (nsB + 1) := fsX (oS (sCar 0 5))
def cS1 : Fin (nsB + 1) := fsX (oS (sCar 1 5))
def cS6 : Fin (nsB + 1) := fsX (oS Out.CarM2.s6)

theorem fsX_ne_FsB (i : Fin (NS + 1)) (k : Fin 23) : fsX i ≠ FsB k := fun h => by
  have := congrArg Fin.val h; rw [fsX_val, FsB_val] at this; have := i.isLt; omega
theorem fsX_ne_o6 (i : Fin (NS + 1)) : fsX i ≠ o6 := fun h => by
  have := congrArg Fin.val h; rw [fsX_val, o6_val] at this; have := i.isLt; omega
theorem fsX_ne_o7 (i : Fin (NS + 1)) : fsX i ≠ o7 := fun h => by
  have := congrArg Fin.val h; rw [fsX_val, o7_val] at this; have := i.isLt; omega
theorem FsB_ne_o6 (k : Fin 23) : FsB k ≠ o6 := fun h => by
  have := congrArg Fin.val h; rw [FsB_val, o6_val] at this; have := k.isLt; omega
theorem FsB_ne_o7 (k : Fin 23) : FsB k ≠ o7 := fun h => by
  have := congrArg Fin.val h; rw [FsB_val, o7_val] at this; have := k.isLt; omega
theorem o6_ne_o7 : o6 ≠ o7 := fun h => by have := congrArg Fin.val h; rw [o6_val, o7_val] at this; omega

/-- SB's four output streams. -/
def sOutB : Fin 4 ↪ Fin (nsB + 1) := ⟨fun k => ⟨NS + 1 + ![0, 1, 23, 24] k, by fin_cases k <;> simp⟩, by
  intro a b h
  have e := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp at e ⊢⟩

theorem sOutB_0 : sOutB 0 = FsB 0 := Fin.ext rfl
theorem sOutB_1 : sOutB 1 = FsB 1 := Fin.ext rfl
theorem sOutB_2 : sOutB 2 = o6 := Fin.ext rfl
theorem sOutB_3 : sOutB 3 = o7 := Fin.ext rfl

theorem sOutB_ne (k : Fin 4) : sOutB k ≠ sInB := by
  fin_cases k
  · exact sOutB_0 ▸ (fsX_ne_FsB _ 0).symm
  · exact sOutB_1 ▸ (fsX_ne_FsB _ 1).symm
  · exact sOutB_2 ▸ (fsX_ne_o6 _).symm
  · exact sOutB_3 ▸ (fsX_ne_o7 _).symm

/-! ## The machine -/

/-- **SB's machine at a gate**: the carrier pipeline (counts only) docked, P1, the field phase, the register clears. -/
noncomputable def sbMach (l : Literals) (F : GateFree l) : (s : ℕ) × Machine (nsB + 2 + NRB) s :=
  ⟨_, Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine (wslot fsX frX) (carM DtC (eraseOf keepLS)))
    (p1W sInB cS0 cS1 cS6 o6 o7 F.cr F.filterErrDeg (gateCParams1 l).ζ (gateCδ1 l) (gateCap l)).toProg.compile)
    (SBField.fieldM FsB RbB)) (SBInv.clearAllW (List.finRange NRB)).toProg.compile⟩

/-! ## The capacity split -/

/-- **Every capacity hypothesis of SB's parts** from `sbNeed ≤ cap`. -/
theorem need_parts (l : Literals) (cr fe : ℕ) (P : Shared.StarParams) (m : Mode) (wl c0 c1 nc cap : ℕ)
    (h : sbNeed l cr fe P m wl c0 c1 nc ≤ cap) :
    tB1 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 ≤ cap ∧
    tB2a P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 ≤ cap ∧
    tB2b P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 ≤ cap ∧
    tB2c P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 ≤ cap ∧
    tC1 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 ≤ cap ∧
    tC2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 ≤ cap ∧
    tC3 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 ≤ cap ∧
    (P.n + 1) ^ 26 ≤ cap ∧ (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap ∧
    SparseNum.sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Ledger.Lq P.n)
      (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) P.n - 1) ≤ cap ∧
    2 ^ 40 * (CallIndexR.capK cr * (P.n + 2) ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)) +
      CapNum.cMain (gateCap l) m ≤ cap ∧
    Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 P.n ≤ cap ∧
    2 * wl ≤ cap ∧ 2 ^ (natBitLength P.n + 1) ≤ cap ∧ c0 + 1 ≤ cap ∧ c1 + 1 ≤ cap ∧ nc + 1 ≤ cap ∧
    fe * Nat.clog 2 (P.n + 2) / 4 + 2 ≤ cap ∧
    (Data.unaryList (sbList P (Ledger.rowBCap (gateCap l) m P.r (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2
      (gateCδ1 l) P.n) P.n) (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc)).length ≤ cap ∧
    4 * ellOf P.n + 6 ≤ cap ∧ 2 ^ DtC * (wl + 1) ^ DtC ≤ cap := by
  unfold sbNeed at h
  generalize 2 ^ (natBitLength P.n + 1) = X at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- `CapNeed` at either mode from `capNeed_of`'s bound. -/
theorem capNeed_mode (l : Literals) (cr : ℕ) (m : Mode) (n cap : ℕ)
    (h : 2 ^ 40 * (CallIndexR.capK cr * (n + 2) ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)) +
      CapNum.cMain (gateCap l) m ≤ cap) :
    SymDec.CapNeed (gateCap l) m n (Ledger.rowBr cr n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) cap := by
  cases m
  · exact PrimT.TS4.capNeed_ofT l cr n cap h
  · exact SymFam.capNeed_of l cr n cap h

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
