import Proof.Wire_3_5.UnionMachine.NumsN4
import Proof.Wire_3_5.UnionMachine.NumsN2Base

/-! # SWn, part 5: the numbers' writer `swN x hx Kt Et tp htp l : SWParts.SWnT l` (x ≥ DT + 8)

P3:3170-3178 (the `symNums`: the SYM call's eighteen numbers, as a unary list, the SYM slot `32`): at a SYM request,
from the core's blank entry, on NW's bank `x ≥ DT + 8`:

1. The SYM front (`SymFront.frontM`, `front_runB`: the flat list's numbers, `J`, the walk length, the population
   lengths and the gate tables);
2. The post program `postN x hx tp` (`postRun`: the gate tables' widths, the tables' lengths, the templates'
   lengths `tp` (with `TplIface Kt Et tp`), the unary list on the output stream `oOut`, every register cleared).

The capacity `Kn5 F·(|fpIn|+1)^{Dn5 fe}` (above the front's need and the post program's `capP Kt Et (C_F·X^{D_Fs})`),
the steps and the residues `Cs5 F·(|fpIn|+1)^{Ds5 fe}` (degrees on `l`, `Et` and `fe` only; coefficients on `l`, `Kt`,
`Et` and the gate).

* `cap5_arith`, `cost5_arith` (pure bounds); `Kn5`, `Dn5`, `Cs5`, `Ds5`; `sO5`; `swnM`; **`swnRun`**, **`swN`**.

Paper quantity of the main type: the SYM call numbers `symNums k` (the unary list of the eighteen numbers, P3:3170-3178)
at every SYM request, on the writer's output stream, in time polynomial in the input. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline

/-! ## Arithmetic -/

/-- The front's need and the post program's capacity below `(K + 100(Kt+8)(3(C+2))^{Et+3})·X^{D + S(Et+3)}`. -/
theorem cap5_arith (Kt Et K C X D S : ℕ) (hX : 1 ≤ X) :
    K * X ^ D ≤ (K + 100 * (Kt + 8) * (3 * (C + 2)) ^ (Et + 3)) * X ^ (D + S * (Et + 3)) ∧
    capP Kt Et (C * X ^ S) ≤ (K + 100 * (Kt + 8) * (3 * (C + 2)) ^ (Et + 3)) * X ^ (D + S * (Et + 3)) := by
  have hS : 1 ≤ X ^ S := Nat.one_le_pow _ _ hX
  have hD : 1 ≤ X ^ D := Nat.one_le_pow _ _ hX
  have e1 : X ^ (D + S * (Et + 3)) = X ^ D * (X ^ S) ^ (Et + 3) := by rw [pow_add, pow_mul]
  have hb : 3 * (C * X ^ S + 2) ≤ 3 * (C + 2) * X ^ S := by
    have e : 3 * (C + 2) * X ^ S = 3 * (C * X ^ S) + 6 * X ^ S := by ring
    omega
  have hp : (3 * (C * X ^ S + 2)) ^ (Et + 3) ≤ (3 * (C + 2)) ^ (Et + 3) * (X ^ S) ^ (Et + 3) := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left hb _
  have hY : 1 ≤ (X ^ S) ^ (Et + 3) := Nat.one_le_pow _ _ hS
  rw [e1]
  unfold capP
  generalize (3 * (C * X ^ S + 2)) ^ (Et + 3) = Aw at hp ⊢
  generalize (3 * (C + 2)) ^ (Et + 3) = P at hp ⊢
  generalize (X ^ S) ^ (Et + 3) = Y at hp hY ⊢
  generalize X ^ D = Z at hD ⊢
  constructor
  · have h1 : K * Z ≤ K * (Z * Y) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hY)
    have e : (K + 100 * (Kt + 8) * P) * (Z * Y) = K * (Z * Y) + 100 * (Kt + 8) * P * Z * Y := by ring
    omega
  · have h2 : 100 * (Kt + 8) * Aw ≤ 100 * (Kt + 8) * (P * Y) := Nat.mul_le_mul_left _ hp
    have h3 : P * Y ≤ P * Y * Z := Nat.le_mul_of_pos_right _ hD
    have h4 : 100 * (Kt + 8) * (P * Y) ≤ 100 * (Kt + 8) * (P * Y * Z) := Nat.mul_le_mul_left _ h3
    have e : (K + 100 * (Kt + 8) * P) * (Z * Y) = K * (Z * Y) + 100 * (Kt + 8) * (P * Y * Z) := by ring
    omega

/-- The steps (the front's `≤ C·X^S`, one seam, the post program's `≤ 4000·cap + 4000`) and the capacity below
`(C + 4000K + 4001)·X^{D + S}` at `cap = K·X^D`. -/
theorem cost5_arith (C K X S D m c : ℕ) (hX : 1 ≤ X) (hm : m ≤ C * X ^ S) (hc : c ≤ 4000 * (K * X ^ D) + 4000) :
    m + 1 + c ≤ (C + 4000 * K + 4001) * X ^ (D + S) ∧ K * X ^ D ≤ (C + 4000 * K + 4001) * X ^ (D + S) := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X ^ (D + S) := ⟨_, rfl⟩
  rw [← hY]
  have p1 : X ^ S ≤ Y := by rw [hY]; exact Nat.pow_le_pow_right hX (by omega)
  have p2 : X ^ D ≤ Y := by rw [hY]; exact Nat.pow_le_pow_right hX (by omega)
  have hY1 : 1 ≤ Y := by rw [hY]; exact Nat.one_le_pow _ _ hX
  have q1 : C * X ^ S ≤ C * Y := Nat.mul_le_mul_left _ p1
  have q2 : K * X ^ D ≤ K * Y := Nat.mul_le_mul_left _ p2
  have e : (C + 4000 * K + 4001) * Y = C * Y + 4000 * (K * Y) + 4001 * Y := by ring
  rw [e]
  exact ⟨by omega, by omega⟩

/-! ## The constants -/

section Consts

end Consts

/-! ## The machine and its run -/

section Gate
variable (x : ℕ) (hx : DataDock.DT + 8 ≤ x) (l : Literals) (Kt Et : ℕ)
  (tp : ∀ {ns nr : ℕ}, Fin (ns + 1) → (Fin 30 ↪ Fin nr) → Fin nr → Fin nr → Fin nr → Fin nr → Fin nr → WM ns nr)

/-- The output stream, as `SWnT`'s one slot. -/
def sO5 : Fin 1 ↪ Fin (LNS x + 1) := ⟨fun _ => oOut x hx, fun a b _ => Subsingleton.elim a b⟩

theorem sO5_ne (k : Fin 1) : sO5 x hx k ≠ sIn x := fun e => by
  have h1 := congrArg Fin.val e
  have h2 : (sO5 x hx k).val = 161 + (DataDock.DT + 7) := oOut_val x hx
  have h3 : (sIn x).val = 150 := rfl
  omega

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
