import Proof.Wire_3_5.Primitive.SeedFix.S3Term
import Proof.Wire_3_5.FinalPass.FiltEval

/-! # S3, part 4: stage 7 with the mask bit in a register (P3:2019-2025, 3170-3178)

"The regular filter" (filt:gap, P3:2019-2025): the SYM value's numerator carries the mask, over the call's carriers,
of stage 7's regular filter at stage 3's population of the doubled corner word. A word program cannot branch on the
result cell, so the filter bit lands in a register: `main7K` is C5's stage 7 (`Filt`, verified) with the output step
replaced by an increment of `B`:
**`main7K_spec`**: `B = [tabEval thr tbl Z]`, every other register `0`, the heads back, the cell unchanged.

Paper quantity of the main type: stage 7's regular filter `tabEval thr tbl Z` (= `filterBits`, the mask's bit). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Filt

/-! ## Stage 7 -/

/-- The answer into `B` instead of the cell. -/
def out7K : FProg := .ifr fX .skip (.inc fB)

/-- **Stage 7 with the filter bit in `B`.** -/
def main7K : FProg := .seq visits7 (.seq cmp7 (.seq out7K cleanup7))

/-- **The regular filter at a point, in a register**: `B = [tabEval thr tbl Z]`, every other register `0`, the heads
back, the cell unchanged. -/
theorem main7K_spec (cap : ℕ) (Z : List Bool) (tbl : List (List (List Bool))) (thr : ℕ) (b : Bool)
    (hlen : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ Z.length) (hcap : capOf7 Z.length tbl thr ≤ cap) :
    RExec (streams7 Z tbl thr) cap main7K (S7 0 0 0 0 0 0 0 b) (S7 0 0 0 0 (tabEval thr tbl Z).toNat 0 0 b)
      (cost7 (tableWord tbl).length thr) := by
  have hW : (tableWord tbl).length = (tbl.flatMap visitWord).length + 1 := by simp [tableWord]
  have hvl := visits_le_word tbl
  unfold capOf7 at hcap
  have hZ : (streams7 Z tbl thr 0).drop 0 = frameP Z ++ [false] := by simp [streams7, frame_eq_frameP]
  have hT : (streams7 Z tbl thr 1).drop 0 = tbl.flatMap visitWord ++ false :: [] := by simp [streams7, tableWord]
  have hU : (streams7 Z tbl thr 2).drop 0 = List.replicate thr true ++ false :: [] := by
    simp [streams7, ListEval.unary]
  have s1 := visits7_spec (streams7 Z tbl thr) cap [] [false] (by omega) Z hZ (by omega) tbl 0 0 0 0 b hlen hT
    (by omega) (by omega)
  simp only [Nat.zero_add] at s1
  generalize hA : (tbl.filter fun vs => visitOk vs Z).length = A at s1
  have hAl : A ≤ tbl.length := by rw [← hA]; exact List.length_filter_le _ _
  have s2 := cmp7_spec (streams7 Z tbl thr) cap [] (tbl.flatMap visitWord).length b (by omega) thr 0 A false hU
    (by omega) (by omega)
  simp only [Nat.zero_add, Bool.false_or] at s2
  have hres : tabEval thr tbl Z = !decide (A < thr) := by
    unfold tabEval; rw [hA]; simp only [← Nat.not_lt, decide_not]
  -- the output
  have s3 : RExec (streams7 Z tbl thr) cap out7K
      (S7 0 (tbl.flatMap visitWord).length thr 0 0 (A - thr) (decide (A < thr)).toNat b)
      (S7 0 (tbl.flatMap visitWord).length thr 0 (tabEval thr tbl Z).toNat (A - thr) (decide (A < thr)).toNat b)
      4 := by
    rw [hres]
    by_cases h : A < thr
    · have e : (decide (A < thr)).toNat = 1 := by simp [h]
      rw [e]
      exact RExec.cast _ cap (RExec.ifrT (by show (1 : ℕ) ≠ 0; omega) (RExec.skip _)) (by simp [h]) (by omega)
    · have e : (decide (A < thr)).toNat = 0 := by simp [h]
      rw [e]
      exact RExec.cast _ cap (RExec.ifrF (by rfl) (RExec.inc (inp := streams7 Z tbl thr) (cap := cap) fB _
        (show 0 < cap by omega))) (by simp [h]; s7_eq) le_rfl
  -- the cleanup
  have c1 := clear_spec (streams7 Z tbl thr) cap fA (A - thr)
    (S7 0 (tbl.flatMap visitWord).length thr 0 (tabEval thr tbl Z).toNat (A - thr) (decide (A < thr)).toNat b) rfl
    (by show A - thr ≤ cap; omega)
  have hx : (decide (A < thr)).toNat ≤ 1 := by cases decide (A < thr) <;> simp
  have c2 := clear_spec (streams7 Z tbl thr) cap fX (decide (A < thr)).toNat
    (S7 0 (tbl.flatMap visitWord).length thr 0 (tabEval thr tbl Z).toNat 0 (decide (A < thr)).toNat b) rfl
    (by show (decide (A < thr)).toNat ≤ cap; omega)
  have c3 := rewind_spec (streams7 Z tbl thr) cap 2 fU thr
    (S7 0 (tbl.flatMap visitWord).length thr 0 (tabEval thr tbl Z).toNat 0 0 b) rfl (by show thr ≤ cap; omega)
  have c4 := rewind_spec (streams7 Z tbl thr) cap 1 fT (tbl.flatMap visitWord).length
    (S7 0 (tbl.flatMap visitWord).length 0 0 (tabEval thr tbl Z).toNat 0 0 b) rfl
    (by show (tbl.flatMap visitWord).length ≤ cap; omega)
  refine RExec.cast _ cap (RExec.seq s1 (RExec.seq s2 (RExec.seq s3 (RExec.seq
    (RExec.cast _ cap c1 (by s7_eq) le_rfl) (RExec.seq (RExec.cast _ cap c2 (by s7_eq) le_rfl)
      (RExec.seq (RExec.cast _ cap c3 (by s7_eq) le_rfl) c4)))))) (by s7_eq) ?_
  unfold cost7
  rw [hW]
  omega

end NearCubicWires.WireExponent3_5.PrimT.S3
