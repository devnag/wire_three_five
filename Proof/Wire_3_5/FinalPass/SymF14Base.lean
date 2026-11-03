import Proof.Wire_3_5.FinalPass.SymF13Base
import Proof.Wire_3_5.FinalPass.SdI7

/-! # SWf (the SYM words writer's flat tables), part 14: the flat tables' writer `SWfT l`

The flat part `swfM l W F` (part 13) is a SYM-guarded word writer: **`swf W l : SWParts.SWfT l`**, with
the register capacity `KcW F·(|fpIn|+1)^{DkW fe}` and the step and residue bound `CsW F·(|fpIn|+1)^{DsW fe}` (degrees
on `l` and the filter degree `fe` only, coefficients on `l` and the gate).

* `cXP`, `BCP`, `BDP`; **`bud_symP`**: each of the four writers' budgets `budP ≤ BCP·(|fpIn|+1)^{BDP}` at a SYM request
  (`Sd.bud_poly` at the writer's dimension `2^m ≤ Q²(n+2)²`, `Q ≤ |fpIn|`, `n ≤ |fpIn|`);
* `KcW`, `DkW`, `CsW`, `DsW`; `cap_arith` (the front's and the requests' needs below the capacity), `swf_cost` (the
  steps and the residues below the bound);
* **`swf_runG`** (the run at a SYM request, words `SWParts.swWs l 8 4`), **`swf`**.

Paper quantity of the main type: the SYM call words `4·2 + c` (circuit `c`'s list seeds' flat tables, list:flatten
P3:1508-1520, P3:3170-3178) at every SYM request, on the writer's output streams, in time polynomial in the input. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimT.WalkBank NearCubicWires.SupplierPipeline NearCubicWires.BlockPlatform

/-! ## Arithmetic -/

/-- The front's and the requests' needs below `(K_F + C_F + 64c_X + 20)·X^{D_F + D_Fs + E₀}`. -/
theorem cap_arith (KF CF cX X DF DFs E0 n lw : ℕ) (hn : n + 1 ≤ X) (hE0 : 1 ≤ E0)
    (hlw : lw ≤ 16 * (cX * X ^ E0)) :
    KF * X ^ DF ≤ (KF + CF + 64 * cX + 20) * X ^ (DF + DFs + E0) ∧
    CF * X ^ DFs ≤ (KF + CF + 64 * cX + 20) * X ^ (DF + DFs + E0) ∧
    n + 4 * lw + 10 ≤ (KF + CF + 64 * cX + 20) * X ^ (DF + DFs + E0) := by
  have hX : 1 ≤ X := by omega
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X ^ (DF + DFs + E0) := ⟨_, rfl⟩
  rw [← hY]
  have pw : ∀ d, d ≤ DF + DFs + E0 → X ^ d ≤ Y := fun d hd => by rw [hY]; exact Nat.pow_le_pow_right hX hd
  have p1 := pw DF (by omega)
  have p2 := pw DFs (by omega)
  have p3 := pw E0 (by omega)
  have p4 : X ≤ Y := by
    have := pw 1 (by omega)
    rwa [pow_one] at this
  have q1 : KF * X ^ DF ≤ KF * Y := Nat.mul_le_mul_left _ p1
  have q2 : CF * X ^ DFs ≤ CF * Y := Nat.mul_le_mul_left _ p2
  have q3 : cX * X ^ E0 ≤ cX * Y := Nat.mul_le_mul_left _ p3
  have e : (KF + CF + 64 * cX + 20) * Y = KF * Y + CF * Y + 64 * (cX * Y) + 20 * Y := by ring
  rw [e]
  exact ⟨by omega, by omega, by omega⟩

/-- The flat part's steps and residues below `(C_F + 1566K_c + 3200c_X + 4B_C + 20000)·X^{D_k + B_D + 2}`. -/
theorem swf_cost (CF Kc cX BC X DFs Dk BD E0 n lw : ℕ) (B : Fin 4 → ℕ) (hn : n + 1 ≤ X) (h1 : DFs ≤ Dk)
    (h2 : E0 ≤ Dk) (hlw : lw ≤ 16 * (cX * X ^ E0)) (hB : ∀ c, B c ≤ BC * X ^ BD) :
    CF * X ^ DFs + 1 + tailCost (Kc * X ^ Dk) B n lw ≤
      (CF + 1566 * Kc + 3200 * cX + 4 * BC + 20000) * X ^ (Dk + BD + 2) ∧
    CF * X ^ DFs + 2 * lw + 1 + (B 0 + B 1 + B 2 + B 3) ≤
      (CF + 1566 * Kc + 3200 * cX + 4 * BC + 20000) * X ^ (Dk + BD + 2) := by
  have hX : 1 ≤ X := by omega
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X ^ (Dk + BD + 2) := ⟨_, rfl⟩
  rw [← hY]
  have pw : ∀ d, d ≤ Dk + BD + 2 → X ^ d ≤ Y := fun d hd => by rw [hY]; exact Nat.pow_le_pow_right hX hd
  have p1 := pw DFs (by omega)
  have p2 := pw Dk (by omega)
  have p3 := pw E0 (by omega)
  have p4 := pw BD (by omega)
  have p5 : X * X ≤ Y := by
    have := pw 2 (by omega)
    rwa [sq] at this
  have hY1 : 1 ≤ Y := by
    have := pw 0 (by omega)
    rwa [pow_zero] at this
  have q1 : CF * X ^ DFs ≤ CF * Y := Nat.mul_le_mul_left _ p1
  have q2 : Kc * X ^ Dk ≤ Kc * Y := Nat.mul_le_mul_left _ p2
  have q3 : cX * X ^ E0 ≤ cX * Y := Nat.mul_le_mul_left _ p3
  have q4 : ∀ c, B c ≤ BC * Y := fun c => (hB c).trans (Nat.mul_le_mul_left _ p4)
  have b0 := q4 0
  have b1 := q4 1
  have b2 := q4 2
  have b3 := q4 3
  have hbl : natBitLength n ≤ n + 1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have rc : Sd.reqCost n lw ≤ 2200 * (X * X) + 50 * lw + 200 := by
    unfold Sd.reqCost
    have h : (natBitLength n + 10) * (100 * n + 200) ≤ (11 * X) * (200 * X) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (11 * X) * (200 * X) = 2200 * (X * X) := by ring
    omega
  have e : (CF + 1566 * Kc + 3200 * cX + 4 * BC + 20000) * Y =
      CF * Y + 1566 * (Kc * Y) + 3200 * (cX * Y) + 4 * (BC * Y) + 20000 * Y := by ring
  rw [e]
  unfold tailCost
  exact ⟨by omega, by omega⟩

/-! ## The constants -/

section Consts

end Consts

/-! ## The run -/

section Gate

end Gate

/-! ## The writer -/

section Inst

end Inst

end NearCubicWires.WireExponent3_5.FinalPass.SymF
