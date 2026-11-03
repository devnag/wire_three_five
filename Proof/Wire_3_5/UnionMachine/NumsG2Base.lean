import Proof.Wire_3_5.UnionMachine.NumsG1Base
import Proof.Wire_3_5.UnionMachine.NumsW2Base
import Proof.Wire_3_5.UnionMachine.NumsC6Base
import Proof.Wire_3_5.UnionMachine.NumsPh3Base
import Proof.Wire_3_5.Foundations.OutMachineJoinGBase

/-! # SWg, part 2: the gate tables' writer `swG x hx l : SWParts.SWgT l` (x ≥ DT + 3)

P3:3049-3050, 3170-3178 (the `symWords`, kind `0`: the SYM slots `16 … 19`, `Corner.gatesW (tabH G_j) G_j`): at a SYM
request, from the core's blank entry, on NW's bank:

1. phase (c)'s program `cProg` (`cRun`: `n`, the mode, `e`, `T_f`), NW (a)'s `prepW` (`width_run`, `tapes_run`);
2. PA's data stage docked (`dockG`): the tables on the slot tapes `tmapA (iSym j)` (blank past the tuple);
3. `fixW`: each blank slot tape to `[false]` (`fix1_spec`), the slot tapes ARE the outputs.

Every register ends `0` (the stash consumed the roles); the other streams are the data stage's residue, the stash
and stream `1`. The capacity `K_g·X^{D_g}`, steps and residue `C_g·X^{D_g'}`, the exponents functions of `fe`.

* `swg_word` (the slots are `gatesW (tabH (gatesJ k j)) (gatesJ k j)`: `symWords_idx`), `sOutG`, `fixW`, `fix_run`,
  constants, **`gRun`**, **`swG`**.

Paper quantities of the main type: the SYM call's bottom gates' tables (`symWords`, kind `0`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.FinalPass.Finish (symSlot sw0_nw)
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g)

section Link

end Link

/-- The slot tapes are the outputs. -/
def oG (x : ℕ) (hx : DataDock.DT + 3 ≤ x) (j : Fin 4) : Fin (LNS x + 1) := tmapA x hx (DataDock.iSym j)

theorem oG_val (x : ℕ) (hx : DataDock.DT + 3 ≤ x) (j : Fin 4) : (oG x hx j).val = 179 + 1789 * j.val := by
  unfold oG
  rw [tmapA_val x hx _ (by intro e; have := congrArg Fin.val e; revert this; fin_cases j <;> decide)]
  fin_cases j <;> rfl

theorem oG_inj (x : ℕ) (hx : DataDock.DT + 3 ≤ x) : Function.Injective (oG x hx) := by
  intro i j h
  have := congrArg Fin.val h
  rw [oG_val, oG_val] at this
  exact Fin.ext (by omega)

/-- **The gate tables' output streams.** -/
def sOutG (x : ℕ) (hx : DataDock.DT + 3 ≤ x) : Fin 4 ↪ Fin (LNS x + 1) := ⟨oG x hx, oG_inj x hx⟩

/-- **The fix-up**: each slot tape, blank to `[false]`. -/
def fixW (x : ℕ) (hx : DataDock.DT + 3 ≤ x) : WM (LNS x) LNR :=
  .seq (fix1 (oG x hx 0)) (.seq (fix1 (oG x hx 1)) (.seq (fix1 (oG x hx 2)) (fix1 (oG x hx 3))))

theorem fix_run (x : ℕ) (hx : DataDock.DT + 3 ≤ x) (cap : ℕ) (ρ : St x) (hh : ∀ j, ρ.sh (oG x hx j) = 0) {n : ℕ}
    (h : Fin 4 → ℕ) (G : Fin 4 → List (NormalizedThresholdGate n))
    (hO : ∀ j, ρ.st (oG x hx j) = FinalPass.Corner.gatesW (h j) (G j) ∨ (ρ.st (oG x hx j) = [] ∧ G j = [])) :
    WExec cap (fixW x hx) ρ ((((ρ.sets (oG x hx 0) (FinalPass.Corner.gatesW (h 0) (G 0))).sets (oG x hx 1)
      (FinalPass.Corner.gatesW (h 1) (G 1))).sets (oG x hx 2) (FinalPass.Corner.gatesW (h 2) (G 2))).sets (oG x hx 3)
      (FinalPass.Corner.gatesW (h 3) (G 3))) (2 + 1 + (2 + 1 + (2 + 1 + 2))) := by
  have ne : ∀ i j : Fin 4, i ≠ j → oG x hx i ≠ oG x hx j := fun i j hij e => hij (oG_inj x hx e)
  have e0 := fix1_spec cap (oG x hx 0) ρ (hh 0) (h 0) (G 0) (hO 0)
  have e1 := fix1_spec cap (oG x hx 1) (ρ.sets (oG x hx 0) (FinalPass.Corner.gatesW (h 0) (G 0)))
    (by rw [WState.sets_sh]; exact hh 1) (h 1) (G 1)
    (by rw [WState.sets_st, Function.update_of_ne (ne 1 0 (by decide))]; exact hO 1)
  have e2 := fix1_spec cap (oG x hx 2) ((ρ.sets (oG x hx 0) (FinalPass.Corner.gatesW (h 0) (G 0))).sets (oG x hx 1)
      (FinalPass.Corner.gatesW (h 1) (G 1)))
    (by rw [WState.sets_sh, WState.sets_sh]; exact hh 2) (h 2) (G 2)
    (by rw [WState.sets_st, Function.update_of_ne (ne 2 1 (by decide)), WState.sets_st,
      Function.update_of_ne (ne 2 0 (by decide))]; exact hO 2)
  have e3 := fix1_spec cap (oG x hx 3) (((ρ.sets (oG x hx 0) (FinalPass.Corner.gatesW (h 0) (G 0))).sets (oG x hx 1)
      (FinalPass.Corner.gatesW (h 1) (G 1))).sets (oG x hx 2) (FinalPass.Corner.gatesW (h 2) (G 2)))
    (by rw [WState.sets_sh, WState.sets_sh, WState.sets_sh]; exact hh 3) (h 3) (G 3)
    (by rw [WState.sets_st, Function.update_of_ne (ne 3 2 (by decide)), WState.sets_st,
      Function.update_of_ne (ne 3 1 (by decide)), WState.sets_st, Function.update_of_ne (ne 3 0 (by decide))]
        exact hO 3)
  exact WExec.seq e0 (WExec.seq e1 (WExec.seq e2 e3))

section Consts


end Consts

theorem costG (c1 c2 c3 fd P C1 C2 C3 S : ℕ) (hP : 1 ≤ P) (h1 : c1 ≤ C1 * P) (h2 : c2 ≤ C2 * P) (h3 : c3 ≤ C3 * P)
    (hd : fd ≤ S * P) :
    c1 + 1 + (c2 + 1 + c3) + 1 + fd + 1 + (2 + 1 + (2 + 1 + (2 + 1 + 2))) ≤ (C1 + C2 + C3 + S + 100) * P := by
  have e1 : (C1 + C2 + C3 + S + 100) * P = C1 * P + C2 * P + C3 * P + S * P + 100 * P := by ring
  rw [e1]; omega

section Gate

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
