import Proof.Wire_3_5.UnionMachine.NumsW1Base
import Proof.Wire_3_5.UnionMachine.NumsPh4Base
import Proof.Wire_3_5.UnionMachine.NumsA12Base
import Proof.Wire_3_5.UnionMachine.NumsC6Base
import Proof.Wire_3_5.UnionMachine.NumsPh3Base
import Proof.Wire_3_5.FinalPass.Core7

/-! # NW assembly: `numsOfPhases' x l : NumsPh4.NumsOfPhases' x l`, and `nwOf`

P3:3044-3048, 3170-3181: the numbers S4 starts from, `frame (binary T_f 0)` and `frame (binary T_f Den)`, from the four
phases on NW's bank (`WState (LNS x) LNR`):

1. (c): `n`, the mode bit, `e`, `T_f` (`AfterC`);
2. the branch on the mode bit `rM` (`iteMachine (rTape rM)`): (b) at THR, (a) at SYM (`AfterV`: `V` in `rV`);
3. `clrW`: `rN := 0`, `rM := 0` ((d) needs every register but `rT`, `rE`, `rV` zero);
4. (d) v4 (`PhD'`): `Final` at `T = T_f`, `max(2^e·V, 1) = Den` (`denSplit`), fitting `T_f` bits (`fpDen_ltR`),
   below the capacity `T + e + V + 2` (`vOf_le`: `V ≤ K_V·X^{D_V}`).

The capacity `K_c·X^{D_k}` dominates every phase's; steps and residue `C_s·X^{D_s}`; the exponents are functions of
`fe` alone. **The bank width**: (a) needs `x ≥ DT + 3` (`phA3`), the (b) needs `x ≥ dX(TW l, NW l)`; the assembly is
generic in `x`, and `nwOf` takes `x` with `DT + 3 ≤ x` (the chosen `x = max(DT + 3, dX(TW l, NW l))` is a function of
`l`, `xNW`).

* `nwIteT`, `nwIteF`, `clrW`, `clr_run`, `nwM`, `KTZ`, `nwKc`, `nwDk`, `nwE`, `nwCs`, `nwDs`, `nw_bound`, **`nwRun`**,
  **`numsOfPhases'`**, `xNW`, **`nwOf`**.

Paper quantity of the main type: the final pass's denominator `Den` in `T_f`-bit binary. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- The taken branch of `iteMachine` (bit set). -/
theorem nwIteT {t : ℕ} (i : Fin t) {a b' : ℕ} (p : Machine t a) (q : Machine t b') (bk c : Bank t) (n : ℕ)
    (hb : bk.bit i = true) (h : Step p n bk.H bk.A c.H c.A) : Step (iteMachine i p q) (n + 1) bk.H bk.A c.H c.A :=
  ite_branch_step i p q bk c n (iteL b') p (by simp [hb]) (ite_halted_L i p q) (ite_step_L i p q) h

/-- The taken branch of `iteMachine` (bit clear). -/
theorem nwIteF {t : ℕ} (i : Fin t) {a b' : ℕ} (p : Machine t a) (q : Machine t b') (bk c : Bank t) (n : ℕ)
    (hb : bk.bit i = false) (h : Step q n bk.H bk.A c.H c.A) : Step (iteMachine i p q) (n + 1) bk.H bk.A c.H c.A :=
  ite_branch_step i p q bk c n (iteR a) q (by simp [hb]) (ite_halted_R i p q) (ite_step_R i p q) h

/-- `rN := 0`, `rM := 0`. -/
def clrW (x : ℕ) : WM (LNS x) LNR := .seq (WM.clear rN) (WM.clear rM)

theorem clr_run (x cap : ℕ) (σ : St x) (n m : ℕ) (hn : σ.val rN = n) (hm : σ.val rM = m) (hnc : n ≤ cap)
    (hmc : m ≤ cap) :
    WExec cap (clrW x) σ ((σ.setv rN 0).setv rM 0) (3 * n + 1 + 1 + (3 * m + 1)) := by
  have e1 := wclear_spec cap rN n σ hn (by omega)
  have e2 := wclear_spec cap rM m (σ.setv rN 0)
    (by rw [WState.setv_val, Function.update_of_ne (show rM ≠ rN by decide)]; exact hm)
    (by rw [WState.setv_val, Function.update_of_ne (show rM ≠ rN by decide)]; omega)
  exact WExec.seq e1 e2

/-- The steps' sum. -/
theorem nw_bound (nc na ncl nd P Cc Ca Cb Cd : ℕ) (hP : 1 ≤ P) (hc : nc ≤ Cc * P) (ha : na ≤ (Ca + Cb) * P)
    (hcl : ncl ≤ 9 * P) (hd : nd ≤ Cd * P) :
    nc + 1 + (na + 1) + 1 + ncl + 1 + nd ≤ (Cc + Ca + Cb + Cd + 20) * P := by
  have e1 : (Cc + Ca + Cb + Cd + 20) * P = Cc * P + Ca * P + Cb * P + Cd * P + 20 * P := by ring
  have e2 : (Ca + Cb) * P = Ca * P + Cb * P := by ring
  rw [e1]; rw [e2] at ha; omega

section Asm



end Asm

section Run

end Run


end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
