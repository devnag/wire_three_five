import Proof.Wire_3_5.FinalPass.FreeGen3

/-! # The free numbers' program, part 3: the run (`freeW_run`)

From the call's numbers in their registers (`FreeRegs`), the block `FB` and the scratch `177 … 199` at `0`, at any
capacity above `need κ x`, the program `freeW κ` leaves `freeVal κ x` in `FB` within `200` units, every other register
(off `130 … 136`, `177 … 199`), every stream, head and the cell as they were: C4.K's `FreeProg.run` at `freeW κ`.

Paper quantity of the main type: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of a call. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.SymQM NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimT.C4Set

theorem Gall_range (k : Fin 35) (hk : k.val < 30) :
    (130 ≤ (Gall k).val ∧ (Gall k).val < 137) ∨ (177 ≤ (Gall k).val ∧ (Gall k).val < 200) := by
  fin_cases k <;> first | exact absurd hk (by decide) | decide

theorem W_eq (x : FreeIn) : 2 * ((β x + 5) / 2 / 2) + 1 = W x := by
  unfold W; rw [Nat.div_div_eq_div_mul]

/-- **The state the program leaves.** -/
noncomputable def freeOut (κ : FreeK) (x : FreeIn) (σ : WState (LNS 0) LNR) :
    WState (LNS 0) LNR :=
  (((((((((((((((((σ).setv (Gall 8) (β x)).setv (Gall 17) (β x * β x)).setv (Gall 18) (β x * β x * (β x * β x))).setv (Gall 19) (β x * β x * (β x * β x) * (β x * β x))).setv (Gall 0) (κ.dT * (β x * β x))).setv (Gall 2) (κ.dQ * (β x * β x))).setv (Gall 3) (κ.dH * (β x * β x))).setv (Gall 5) (κ.dP * (β x * β x * (β x * β x) * (β x * β x)))).setv (Gall 20) (κ.dC * (β x * β x))).setv (Gall 1) (2 ^ (κ.dC * (β x * β x)))).setv (Gall 21) (2 * ((β x + 5) / 2 / 2) + 1)).setv (Gall 22) (x.kh)).setv (Gall 23) (x.nc)).setv (Gall 24) (x.a)).setv (Gall 25) (x.M)).setv (Gall 4) (κ.mA * x.nc + κ.mB * (x.a * (2 * ((β x + 5) / 2 / 2) + 1)) + κ.mC * (2 * ((β x + 5) / 2 / 2) + 1) + κ.mD * x.a + κ.mF * x.M + κ.mE)).setv (Gall 6) (max (x.n - x.kh - x.kh + κ.dA * β x) (κ.dR * (β x * β x)))

end NearCubicWires.WireExponent3_5.FinalPass.FreeGen

