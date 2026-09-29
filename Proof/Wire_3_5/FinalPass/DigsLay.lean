import Proof.Wire_3_5.FinalPass.ThrLoop
import Proof.Wire_3_5.FinalPass.DigsIface

/-! # `DigsW`'s body, part 1: the register layout (W17)

`DigsW`'s 48 registers `R : Fin digsK ↪ Fin nr` (`Digs.digsK = 48`): inputs `R 0 = a'`, `R 1 = g`, `R 2 = p`,
`R 3 = τ₀`, `R 4 = oOff`; the residue core `Rg` (`Rg 0 = R 2 = p`, `Rg i = R (4 + i)`); the payload position
`R 14`; the child header `R 15 = |supp|`, `R 16 = |children|`; the selection `R 17 = g / Π m_j`, `R 18 = g_i`; skip
counts `R 19`, `R 20`; division `R 21`, `R 22`; the base `R 23`, `R 24 = p − base`; the power `R 25 = base^i`; the
product `R 26`, `R 27`, `R 28`; the digit `R 29 … R 32`; the output `R 33`, `R 34 = Lw`; the digit loop `R 35`,
`R 36 = d`; the occurrence `R 37`; the circuit countdown `R 38`; copies `R 39`, `R 40`. Main declarations: `cIdx`,
`Rg`, the routines' embeddings `dmE`, `mlW`, `mlB`, `btE`, `ecE`, and `Zs` (a list of registers holding `0`). Paper
quantity: none (the layout of the program computing the digit populations `v_{i,d}`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore
open NearCubicWires.WireExponent3_5.FinalPass.ThrRead NearCubicWires.WireExponent3_5.FinalPass.ThrArith
open NearCubicWires.WireExponent3_5.FinalPass.Digs

def cIdx : Fin 10 → Fin digsK := ![2, 5, 6, 7, 8, 9, 10, 11, 12, 13]
theorem cIdx_inj : Function.Injective cIdx := by decide
def dmIdx : Fin 6 → Fin digsK := ![17, 16, 21, 18, 22, 39]
theorem dmIdx_inj : Function.Injective dmIdx := by decide
def mlWIdx : Fin 6 → Fin digsK := ![26, 27, 5, 25, 39, 40]
theorem mlWIdx_inj : Function.Injective mlWIdx := by decide
def mlBIdx : Fin 6 → Fin digsK := ![26, 27, 28, 25, 39, 40]
theorem mlBIdx_inj : Function.Injective mlBIdx := by decide
def btIdx : Fin 7 → Fin digsK := ![26, 36, 29, 30, 31, 32, 39]
theorem btIdx_inj : Function.Injective btIdx := by decide
def ecIdx : Fin 6 → Fin digsK := ![4, 37, 33, 39, 40, 34]
theorem ecIdx_inj : Function.Injective ecIdx := by decide

variable {ns nr : ℕ} (R : Fin digsK ↪ Fin nr)

/-- The residue core's registers. -/
def Rg : Fin 10 ↪ Fin nr := ⟨fun i => R (cIdx i), R.injective.comp cIdx_inj⟩
/-- Division: `X = R 17`, `M = R 16`, `Q = R 21`, `Rm = R 18`, `RmD = R 22`, `T = R 39`. -/
def dmE : Fin 6 ↪ Fin nr := ⟨fun i => R (dmIdx i), R.injective.comp dmIdx_inj⟩
/-- A weight's product: `A = R 26`, `AD = R 27`, `Y = R 5` (the residue), `S = R 25`, `T = R 39`, `U = R 40`. -/
def mlW : Fin 6 ↪ Fin nr := ⟨fun i => R (mlWIdx i), R.injective.comp mlWIdx_inj⟩
/-- The power's product: `A = R 26`, `AD = R 27`, `Y = R 28`, `S = R 25`, `T = R 39`, `U = R 40`. -/
def mlB : Fin 6 ↪ Fin nr := ⟨fun i => R (mlBIdx i), R.injective.comp mlBIdx_inj⟩
/-- The digit: `A = R 26`, `D = R 36`, `Hq = R 29`, `H2 = R 30`, `Rb = R 31`, `Dc = R 32`, `T = R 39`. -/
def btE : Fin 7 ↪ Fin nr := ⟨fun i => R (btIdx i), R.injective.comp btIdx_inj⟩
/-- The output: `Off = R 4`, `Oc = R 37`, `X = R 33`, `T = R 39`, `U = R 40`, `Lw = R 34`. -/
def ecE : Fin 6 ↪ Fin nr := ⟨fun i => R (ecIdx i), R.injective.comp ecIdx_inj⟩

@[simp] theorem Rg0 : Rg R 0 = R 2 := rfl
@[simp] theorem Rg1 : Rg R 1 = R 5 := rfl
@[simp] theorem Rg2 : Rg R 2 = R 6 := rfl
@[simp] theorem Rg3 : Rg R 3 = R 7 := rfl
@[simp] theorem Rg4 : Rg R 4 = R 8 := rfl
@[simp] theorem Rg5 : Rg R 5 = R 9 := rfl
@[simp] theorem Rg6 : Rg R 6 = R 10 := rfl
@[simp] theorem Rg7 : Rg R 7 = R 11 := rfl
@[simp] theorem Rg8 : Rg R 8 = R 12 := rfl
@[simp] theorem Rg9 : Rg R 9 = R 13 := rfl

theorem Rg_ne_Pc : ∀ i, Rg R i ≠ R 14 := by
  intro i; fin_cases i <;> exact R.injective.ne (by decide)

/-- The registers of `l` hold `0`. -/
def Zs (τ : WState ns nr) (l : List (Fin digsK)) : Prop := ∀ k ∈ l, τ.val (R k) = 0

/-- The core registers other than `P`. -/
def coreL : List (Fin digsK) := [5, 6, 7, 8, 9, 10, 11, 12, 13]

theorem core_zero (τ : WState ns nr) (h : Zs R τ coreL) : ∀ i : Fin 10, i ≠ 0 → τ.val (Rg R i) = 0 := by
  intro i hi
  fin_cases i
  · exact absurd rfl hi
  all_goals exact h _ (by decide)

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
