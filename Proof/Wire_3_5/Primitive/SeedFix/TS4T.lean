import Proof.Wire_3_5.Primitive.SeedFix.TS4S

/-! # thrStage4U, part 9: the v4 data stage's run

P3:2543-2558, 2596-2604, 2150-2157, 2220-2231, 3068-3084 (the THR call's numbers once per call, then the tables and the
slice lengths): from the stage's entry bank (`frame (reqW …)`, `1^n`, `1^L`, `1^W`, blank extra tapes), the
v4 machine `m3M` leaves the data word `dataWord (hashNums … ++ thrCounts Cs carriers)` on `sOUT`, the request on `sIN`,
the tables on `sSym 0 3` and `sCar k 3`, every head at `0`:

* `hs_get`, `nums3Out_hs` (W6's value ports are the hash numbers in unary);
* **`m3_run`** (under the prep's needs, W6's `TF2Ok` and `need`), with the extra tapes' contents bounded by the fuel.

Paper quantities of the main type: the data word `hashNums ++ thrCounts` (the THR numbers, then the slice lengths). -/

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
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.Streaming (marks)

theorem hs_get (ncar capT : ℕ) (v : PrimThrW.Joins.ThrNumVals) (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 16) :
    (ncar :: capT :: thrNumList v).getD (k - 1) 0 = v.get ⟨k - 3, by omega⟩ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have e : j + 3 - 1 = j + 2 := by omega
  rw [e]
  show (thrNumList v).getD j 0 = _
  have hl : j < (thrNumList v).length := by unfold thrNumList; rw [List.length_ofFn]; omega
  rw [List.getD_eq_getElem _ _ hl]
  unfold thrNumList
  rw [List.getElem_ofFn]
  congr 1

/-- **W6's value ports are the hash numbers in unary.** -/
theorem nums3Out_hs (w : List Bool) (ncar capT V : ℕ) (v : PrimThrW.Joins.ThrNumVals) (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 16) :
    PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨k, by omega⟩ =
      List.replicate ((ncar :: capT :: thrNumList v).getD (k - 1) 0) true := by
  unfold PrimThrW.Nums3.nums3OutPorts
  rw [dif_pos (show k < 20 by omega)]
  unfold PrimThrW.NumsP.numsOutPorts
  by_cases h1 : k = 1
  · subst h1; simp
  by_cases h2 : k = 2
  · subst h2; simp
  · simp only [show ¬ (k = 0) by omega, h1, h2, if_false]
    rw [dif_pos (show k < 17 by omega), hs_get ncar capT v k (by omega) hk']

end NearCubicWires.WireExponent3_5.PrimT.TS4
