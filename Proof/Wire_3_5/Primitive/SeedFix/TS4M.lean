import Proof.Wire_3_5.Primitive.SeedFix.TS4Q
import Proof.Wire_3_5.Primitive.SeedFix.TS4H
import Proof.Wire_3_5.Primitive.SeedFix.TS4C
import Proof.Wire_3_5.Primitive.SeedFix.ThrRoom

/-! # thrStage4U, part 6: the v4 data stage's tapes and slots

P3:2543-2558, 3068-3084 (the THR call's numbers, once per call): the v4 stage runs on v3's
`DS + 2 + DR` tapes plus `x3 = thrStageRoom alg` extra tapes (`w6x alg + 21 + 4096`). The extra tapes hold, from
`0`: W6's out-ports `3 … 19` (`17` tapes), W6's scratch (`w6x alg` tapes), then the prep's tapes (`676`) from
`base = 17 + w6x alg`; W6's ports `1`, `2`, `20` are the prep's output streams `3`, `4`, `5` (extra `base + 4, 5, 6`),
W6's port `0` and the prep's request are the stage's `sIN`, the prep's fill count is the stage's `sCT`:

* `TS`, `t4X`, `t4b`, `TI_w6x`, `t4X_ge`; `adc_lt`, `adc_ge`;
* the slot maps **`t4P`** (the prep), **`t4W`** (W6), **`t4Q`** (the hash writer: `sOUT`, the cell, the sixteen value
  ports, the stage's registers), **`t4E`** (the stage's own tapes), each injective; **`t4perm`** (the reset's junk tape
  to position `DS + 2 + DR`);
* **`coreM`**, **`m3M`** (the v4 machine on `DS + 2 + DR + 1 + x3` tapes).

Paper quantities of the main type: the tapes of the machine computing the data word `hashNums ++ thrCounts`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.ThrData

/-- The stage's own tapes. -/
abbrev TS : ℕ := DS + 2 + DR

theorem TS_val : TS = 9901 := rfl
theorem LNS0_val : LNS 0 = 160 := rfl
theorem LNR_val : LNR = 512 := rfl
theorem DS_val : DS = 9883 := rfl
theorem DR_val : DR = 16 := rfl

variable (alg : RepairRepresentation.DecompositionAlgorithm)

/-- The extra tapes. -/
def t4X : ℕ := W6.thrStageRoom alg

/-- The prep's first extra tape. -/
def t4b : ℕ := 17 + W6.w6x alg

theorem TI_w6x : W6.TI alg + 1 = W6.w6x alg := by
  have h := W6.numsW6_x alg 0
  rw [← h]; rfl

theorem t4X_ge : t4b alg + 676 ≤ t4X alg := by
  unfold t4b t4X W6.thrStageRoom; omega

theorem adc_lt {m n : ℕ} {α : Type} (f : Fin m → α) (g : Fin n → α) (v : ℕ) (hv : v < m + n) (h : v < m) :
    Fin.addCases (motive := fun _ => α) f g ⟨v, hv⟩ = f ⟨v, h⟩ := by
  have e : (⟨v, hv⟩ : Fin (m + n)) = Fin.castAdd n ⟨v, h⟩ := rfl
  rw [e, Fin.addCases_left]

theorem adc_ge {m n : ℕ} {α : Type} (f : Fin m → α) (g : Fin n → α) (v : ℕ) (hv : v < m + n) (h : m ≤ v) :
    Fin.addCases (motive := fun _ => α) f g ⟨v, hv⟩ = g ⟨v - m, by omega⟩ := by
  have e : (⟨v, hv⟩ : Fin (m + n)) = Fin.natAdd m ⟨v - m, by omega⟩ := by ext; simp; omega
  rw [e, Fin.addCases_right]

/-- **The prep's slots**: its request stream on `sIN`, its fill count on `sCT`, every other tape `j` on extra `base + j`. -/
def t4P (j : Fin (LNS 0 + 2 + LNR + 1)) : Fin (TS + t4X alg) :=
  ⟨if j.val = 0 then 0 else if j.val = 2 then 4 else TS + (t4b alg + j.val), by
    have := t4X_ge alg; have := j.isLt; have := TS_val; have := LNS0_val; have := LNR_val; have := DS_val; have := DR_val; split_ifs <;> omega⟩

theorem t4P_inj : Function.Injective (t4P alg) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [t4P] at hv
  have := a.isLt; have := b.isLt; have := TS_val; have := LNS0_val; have := LNR_val
  apply Fin.ext
  split_ifs at hv <;> omega

/-- **W6's slots**: port `0` on `sIN`, ports `1`, `2`, `20` on the prep's outputs, ports `3 … 19` on extra `0 … 16`,
the scratch after them. -/
def t4W (j : Fin (21 + (W6.TI alg + 1))) : Fin (TS + t4X alg) :=
  ⟨if j.val = 0 then 0 else if j.val = 1 then TS + (t4b alg + 4) else if j.val = 2 then TS + (t4b alg + 5)
    else if j.val = 20 then TS + (t4b alg + 6) else if j.val < 20 then TS + (j.val - 3)
    else TS + (17 + (j.val - 21)), by
    have := t4X_ge alg; have := j.isLt; have := TI_w6x alg; have := TS_val; unfold t4b at *; split_ifs <;> omega⟩

theorem t4W_inj : Function.Injective (t4W alg) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [t4W] at hv
  have := a.isLt; have := b.isLt; have := TI_w6x alg; have := TS_val
  apply Fin.ext
  unfold t4b at hv
  split_ifs at hv <;> omega

/-- **The hash writer's slots**: its output stream on `sOUT`, its cell on the stage's cell, its sixteen unary streams
on W6's ports `1 … 16`, its registers on the stage's registers. -/
def t4Q (j : Fin (16 + 2 + 16)) : Fin (TS + t4X alg) :=
  ⟨if j.val = 0 then 6 else if j.val = 1 then 1 else if j.val = 2 then TS + (t4b alg + 4)
    else if j.val = 3 then TS + (t4b alg + 5) else if j.val < 18 then TS + (j.val - 4) else DS + 2 + (j.val - 18), by
    have := t4X_ge alg; have := j.isLt; have := TS_val; have := LNS0_val; have := LNR_val; have := DS_val; have := DR_val; split_ifs <;> omega⟩

theorem t4Q_inj : Function.Injective (t4Q alg) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [t4Q] at hv
  have := a.isLt; have := b.isLt; have := t4X_ge alg; have := TS_val; have := DS_val
  apply Fin.ext
  unfold t4b at hv
  split_ifs at hv <;> omega

/-- The stage's own tapes. -/
def t4E (i : Fin TS) : Fin (TS + t4X alg) := ⟨i.val, by omega⟩

theorem t4E_inj : Function.Injective (t4E alg) := by
  intro a b h
  have hv := congrArg Fin.val h
  exact Fin.ext hv

/-- The reset's junk tape to position `DS + 2 + DR`, the extra tapes after it. -/
def t4perm (i : Fin (TS + t4X alg + 1)) : Fin (TS + 1 + t4X alg) :=
  ⟨if i.val < TS then i.val else if i.val < TS + t4X alg then i.val + 1 else TS, by
    have := i.isLt; have := TS_val; split_ifs <;> omega⟩

theorem t4perm_inj : Function.Injective (t4perm alg) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [t4perm] at hv
  have := a.isLt; have := b.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

variable (Dexp cr : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams)

/-- **The v4 stage before its teardown**: the prep, W6, the fill-inputs-tables, the hash writer, the collection. -/
noncomputable def coreM :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine (t4P alg) (p0M cr ζ Cδ C))
    (RecoveryFocus.machine (t4W alg) (W6.numsM6 alg Dexp)))
    (RecoveryFocus.machine (t4E alg) preT2))
    (RecoveryFocus.machine (t4Q alg) qhW.toProg.compile))
    (RecoveryFocus.machine (t4E alg) collectTail.toProg.compile)

/-- **The v4 machine** on `DS + 2 + DR + 1 + x3` tapes (every head back at `0`). -/
noncomputable def m3M := RecoveryFocus.machine (t4perm alg) (MaskedReset.machine (coreM alg Dexp cr ζ Cδ C) (fun _ => true))

end NearCubicWires.WireExponent3_5.PrimT.TS4
