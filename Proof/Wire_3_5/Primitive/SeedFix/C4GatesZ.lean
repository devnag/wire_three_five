import Proof.Wire_3_5.Primitive.SeedFix.C4GatesX
import Proof.Wire_3_5.Primitive.SeedFix.C4Arm

/-! # G1, the gate converter: the slots' tables to C3a's gate field (P3:1645-1650, 1655-1664)

"For a common pool over all `2^k` rows and polynomially many original atoms, it gives `P_ex ≤ 2^k n^{O(1)}`"
(P3:1661-1663): C3a reads the call's pool as one native stream, `C4Geo.gateField G` (the count `natWord |G|`, the
framed arity, each gate's framed native word). The data stage leaves each slot's gates as the table `gatesW h G`.
**`convAll js`** (one word program on `CS = WState 11 20`): the arity `n` from `1^n` (C4Arm's `ucount`), its word
`marks (natWord n)` (PA's `writeNatM`), the listed slots' tables in order (`tabsW_spec`: every gate's native word
framed twice on the scratch `S`), then on the output: the count field `marks (natWord |pool|)` (PA's `writeNatM`),
the framed arity twice framed, `S`, the end.

**`convAll_spec`**: from the arity ruler `1^n`, the listed slots' tables (each `gatesW (tabH G) G`, or blank for an
unfilled slot), every other stream blank and every register `0`, the output stream ends as
`C4Geo.gateField (js.flatMap Gs)` (`gateField_eq`).

Paper quantity of the main type: C3a's gate field of the call's pool, `gateField (js.flatMap Gs)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Gates
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.PrimT

/-- `writeNatM`'s registers for the arity's word: the value `rN`, scratch, the counter `rOq`. -/
def RQ : Fin 8 ↪ Fin 20 := ⟨![rN, rL, rL2, rZ, rF, rH, rX, rOq], by decide⟩

/-- `writeNatM`'s registers for the count field: the value `rCNT`, scratch, the counter `rOo`. -/
def RO : Fin 8 ↪ Fin 20 := ⟨![rCNT, rL, rL2, rZ, rF, rH, rX, rOo], by decide⟩

/-- **The gate converter** over the listed slots. -/
def convAll (js : List (Fin 6)) : CW :=
  .seq (C4Arm.ucount sNS rN) (.seq (PrimAsm.WriteNat.writeNatM sNQ RQ)
  (.seq (FinalPass.Hash4.wcopyR rOq rX rT) (.seq (rewW sNQ rX) (.seq (tabsW js)
  (.seq (PrimAsm.WriteNat.writeNatM sO RO) (.seq (FinalPass.Hash4.wcopyR rN rK rT)
  (.seq (.whr rK (.seq (.dec rK) (.seq (.inc rX) (PrimAsm.Emit.emitW sO rOo [true, true, true, true]))))
  (.seq (WM.clear rX) (.seq (PrimAsm.Emit.emitW sO rOo [true, false])
  (.seq (FinalPass.Hash4.wcopyR rOs rX rT) (.seq (rewW sS rX)
  (.seq (copyL sS sO rOo rOs (fun b => [b])) (PrimAsm.Emit.emitW sO rOo [false])))))))))))))

theorem RQ0 : RQ 0 = rN := rfl
theorem RQ1 : RQ 1 = rL := rfl
theorem RQ2 : RQ 2 = rL2 := rfl
theorem RQ3 : RQ 3 = rZ := rfl
theorem RQ4 : RQ 4 = rF := rfl
theorem RQ5 : RQ 5 = rH := rfl
theorem RQ6 : RQ 6 = rX := rfl
theorem RO0 : RO 0 = rCNT := rfl
theorem RO1 : RO 1 = rL := rfl
theorem RO2 : RO 2 = rL2 := rfl
theorem RO3 : RO 3 = rZ := rfl
theorem RO4 : RO 4 = rF := rfl
theorem RO5 : RO 5 = rH := rfl
theorem RO6 : RO 6 = rX := rfl
theorem RO7 : RO 7 = rOo := rfl

/-- State component simplification without normalizing word lengths. -/
macro "wv" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp +decide only [$ts,*, WState.setv_val, WState.seth_val,
  WState.sets_val, PrimAsm.WriteNat.appendO_val, WState.setv_sh, WState.seth_sh, WState.sets_sh,
  PrimAsm.WriteNat.appendO_sh, WState.setv_st, WState.seth_st, WState.sets_st, PrimAsm.WriteNat.appendO_st,
  Function.update_apply, ite_true, ite_false, if_true, if_false])

/-- The converter's step bound (`P` pool gates, `H` the largest table width). -/
def convCost (n P H : ℕ) : ℕ :=
  n * 7 + 1 + (natBitLength n + 10) * (100 * n + 200) + (23 * (4 * natBitLength n + 2) + 4) +
    ((P + 6) * (gateCost H n + 4) + 12) + (natBitLength P + 10) * (100 * P + 200) + (61 * n + 5) + 16 +
    (46 * (P * ((8 * H + 8) * (n + 2) + 8 * natBitLength n + 8)) + 5) + 8 + 20

end NearCubicWires.WireExponent3_5.PrimT.C4Gates
