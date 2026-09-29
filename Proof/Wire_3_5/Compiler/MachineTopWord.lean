import Proof.Wire_3_5.Compiler.MachineTopRun

/-! # C3 v2 top level, T6 (part 2): the word function of the whole machine (P3:1874-1906, 1728-1737)

Paper: alg:compiler (P3:1886-1906) through the printer's request (P3:1728-1737), as one deterministic machine run
from its input word. The word function's entry bank has the framed input on tape 0 and every other tape empty; the
machine's log tapes are blank tapes of fixed capacities (`capOf`, …, `capLOf`: the largest cost each log records), so
base's `ZeroPadding.run_unpad` runs the same machine from the empty tapes. The final masked reset returns every head
to cell 0 (the `RewoundWordFunction` shape of `Machine.Implements`). **`c3_run`**: on every request satisfying
`C3Req.Pre`, the machine `c3M` runs in `c3Cost` steps from the word function's entry bank to a bank with every head
at cell 0 whose tape 1 is exactly `reqWord dRow (p+1) width cols (c3v2Ref a R)`, the encoding of C3 v2's (and C3 v3's)
reference. The paper quantity is the printer request's word. Main declarations: the capacities, `subCaps_of`, `c3M`,
`c3Cost`, `c3Cap`, **`c3_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Top
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires.WireExponent3_5.CompilerMachine.Req NearCubicWires.WireExponent3_5.CompilerMachine.Poly
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform

variable (a : DecompositionAlgorithm)

/-! ## The log capacities -/

/-- The first register log (the compiler stages' `cap`, the emit loop's register log). -/
def capOf (R : C3Req) : ℕ :=
  listMax [2 * (R.P.Q + (shapeOf (R.D a)).flatten.length + 1) + 1, 2 * sCBW R + 1, 2 * R.m + 2, 2 * (R.p + 1) + 1, 2 * (R.P.h * R.P.Q * R.d) + 1 + 1 + (1 + 1 + 1),
    2 * (R.P.Q + (poolChildren a R.P.gates R.P.flips).length + 1) + 1, appendCost 0 (2 * (R.P.width + R.P.width + 1)) 1]

/-- The second log (`cap2`, the emit loop's stack log). -/
def cap2Of (R : C3Req) : ℕ :=
  listMax [((shapeOf (R.D a)).flatten.length + 1) * (Masks.innerCost (R.P.Q + (shapeOf (R.D a)).flatten.length + 1) + 2) + 1, filterLoopCost (sB a R) (R.P.Q + (shapeOf (R.D a)).flatten.length + 1),
    copyLoopCost (sB a R + 1) (R.P.Q + (shapeOf (R.D a)).flatten.length + 1), pass1Cost (sNU a R) (R.P.Q + (shapeOf (R.D a)).flatten.length + 1),
    appendCost (sNU a R) (sNU a R + 1) (R.P.Q + (shapeOf (R.D a)).flatten.length + 1),
    mergeAllCost (2 * (R.P.width + R.P.width + 1)) (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h) R.P.h,
    skipCost (2 * (R.P.width + R.P.width + 1)) (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h) R.P.h]

/-- The third log (`cap3`, the emit loop's copy log). -/
def cap3Of (R : C3Req) : ℕ :=
  listMax [max (lookupCost (shapeOf (R.D a)).length ((shapeOf (R.D a)).flatten.length + 1) (R.P.Q + (shapeOf (R.D a)).flatten.length + 1))
      (max (expandLoopCost (((shapeOf (R.D a)).flatten.length + 1) ^ R.d) ((shapeOf (R.D a)).flatten.length + 1) (R.P.Q + (shapeOf (R.D a)).flatten.length + 1))
        (copyLoopCost (((shapeOf (R.D a)).flatten.length + 1) ^ R.d) (R.P.Q + (shapeOf (R.D a)).flatten.length + 1))),
    2 * (2 * (R.P.Q + (shapeOf (R.D a)).flatten.length + 1) + 1) + 2 + 1 + 1, sB a R * (allCost (sB a R) (R.P.Q + (shapeOf (R.D a)).flatten.length + 1) + 2) + 1,
    sNG a R * (aCost (sNU a R) (R.P.Q + (shapeOf (R.D a)).flatten.length + 1) + 2) + 1, sNU a R * (2 * (R.P.Q + (shapeOf (R.D a)).flatten.length + 1) + 1 + 1 + 1 + 2) + 1,
    appendCost 0 (2 * (R.P.width + R.P.width + 1)) (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h + R.P.h)]

/-- The fourth log (`cap4`, the emit loop's cut log). -/
def cap4Of (R : C3Req) : ℕ :=
  listMax [1 + 1 + (R.m * (factorCost (sNF R) (sCB R) R.d (shapeOf (R.D a)).length R.P.Q (shapeOf (R.D a)).flatten.length (sB a R) + 2) + 1),
    cut0Cost (R.p + 1) (R.P.h * R.P.Q * R.d) (R.P.width + R.P.width), cut1Cost (R.p + 1) (R.P.h * R.P.Q * R.d) (R.P.width + R.P.width)]

/-- The fifth log (`cap5`, the emit loop's coefficient log). -/
def cap5Of (R : C3Req) : ℕ :=
  listMax [R.V.length * (termCost (sCBW R) R.m (sNF R) (sCB R) R.d (shapeOf (R.D a)).length R.P.Q (shapeOf (R.D a)).flatten.length (sB a R) (sNG a R)
    (sNU a R) + 2) + 1, coefRawCost R.P.Q (R.p + 1) R.p]

/-- The emit loop's entry log. -/
def capEntOf (R : C3Req) : ℕ :=
  entryCost R.P.Q (R.p + 1) (poolChildren a R.P.gates R.P.flips).length R.P.h R.P.width (R.P.h * R.P.Q * R.d) R.p

/-- The shared stage log. -/
def capLOf (R : C3Req) : ℕ :=
  listMax [2 * (c3Input a R).length + 1, loadChainCost (List.replicate R.P.Q true) (List.replicate (shapeOf (R.D a)).flatten.length true) (List.replicate R.m true) (List.replicate R.P.h true) (List.replicate (R.p + 1) true) (List.replicate R.P.width true) ((poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame) (Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) []) (R.V.flatMap Poly.termRec ++ [false]) (frame (natWord R.dRow ++ natWord (R.p + 1))) (frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols)),
    initCost (R.P.Q - 1) (shapeOf (R.D a)).flatten.length R.m (R.p + 1) R.P.width, subsetsCost a R + 1 + 1, emitCostR a R + 1 + 1,
    w2Cost [true, true] [] (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length]

theorem subCaps_of (R : C3Req) : SubCaps a R (capOf a R) (cap2Of a R) (cap3Of a R) (cap4Of a R) (cap5Of a R) := by
  exact ⟨⟨le_listMax _ _ (List.mem_cons_self), le_listMax _ _ (List.mem_cons_self), ⟨le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_self)), le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))⟩, le_listMax _ _ (List.mem_cons_self), le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_self)), le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))⟩,
    le_listMax _ _ (List.mem_cons_self), le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_self)), ⟨le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))), le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))⟩,
    le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))), le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))), le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))), le_listMax _ _ (List.mem_cons_self)⟩

/-! ## The whole machine and its word function -/

/-- **The C3 v2 machine**: the five stages, then every head back at cell 0. -/
noncomputable def c3M := MaskedReset.machine topM (fun _ => true)

/-- Its cost on a request. -/
def c3Cost (R : C3Req) : ℕ := 2 * topCost a R + 2

/-- The capacities of the machine's tapes (the logs; `0` elsewhere). -/
def c3Cap (R : C3Req) : Fin (74 + 1) → ℕ :=
  Fin.addCases (topCapv (capOf a R) (cap2Of a R) (cap3Of a R) (cap4Of a R) (cap5Of a R) (capEntOf a R) (capLOf a R))
    (fun _ : Fin 1 => topCost a R)

/-- The five stages at the capacities. -/
theorem top_run_caps (R : C3Req) (hR : R.Pre a) :
    ∃ Hf Af, Step topM (topCost a R) topZ (topA0 a R (capOf a R) (cap2Of a R) (cap3Of a R) (cap4Of a R) (cap5Of a R) (capEntOf a R) (capLOf a R)) Hf Af ∧
      Af 1 = reqWord R.dRow (R.p + 1) R.P.width R.cols (c3v2Ref a R) := by
  exact top_run a R hR (capOf a R) (cap2Of a R) (cap3Of a R) (cap4Of a R) (cap5Of a R) (capEntOf a R) (capLOf a R)
    (subCaps_of a R)
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
    le_rfl
    (le_listMax _ _ (List.mem_cons_self))
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
    (le_listMax _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))

theorem pad_nil (c : ℕ) : ZeroPadding.pad c [] = List.replicate c false := by simp [ZeroPadding.pad]

/-- The word function's entry bank, padded to the capacities, is the stages' entry bank. -/
theorem c3_entry (R : C3Req) :
    ZeroPadding.config (c3Cap a R)
      (⟨c3M.start, fun _ => 0, fun i => if i.val = 0 then frame (c3Input a R) else []⟩ : Configuration (74 + 1) _) =
      ⟨c3M.start, Fin.addCases topZ (fun _ : Fin 1 => 0),
        Fin.addCases (topA0 a R (capOf a R) (cap2Of a R) (cap3Of a R) (cap4Of a R) (cap5Of a R) (capEntOf a R) (capLOf a R)) (fun _ : Fin 1 => List.replicate (topCost a R) false)⟩ := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · show (0 : ℕ) = Fin.addCases topZ (fun _ : Fin 1 => 0) (Fin.castAdd 1 j)
      rw [Fin.addCases_left]
      fin_cases j <;> rfl
    · show (0 : ℕ) = Fin.addCases topZ (fun _ : Fin 1 => 0) (Fin.natAdd 74 j)
      rw [Fin.addCases_right]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · show ZeroPadding.pad (c3Cap a R (Fin.castAdd 1 j)) (if (Fin.castAdd 1 j : Fin (74 + 1)).val = 0 then
          frame (c3Input a R) else []) = Fin.addCases (topA0 a R (capOf a R) (cap2Of a R) (cap3Of a R) (cap4Of a R)
          (cap5Of a R) (capEntOf a R) (capLOf a R)) (fun _ : Fin 1 => List.replicate (topCost a R) false) (Fin.castAdd 1 j)
      rw [Fin.addCases_left, Fin.val_castAdd]
      unfold c3Cap topA0
      rw [Fin.addCases_left]
      by_cases hj : j.val = 0
      · rw [if_pos hj, if_pos hj]
        have : j = 0 := Fin.ext hj
        subst this
        rw [show topCapv (capOf a R) (cap2Of a R) (cap3Of a R) (cap4Of a R) (cap5Of a R) (capEntOf a R) (capLOf a R) 0 = 0
          from rfl, ZeroPadding.pad_zero]
      · rw [if_neg hj, if_neg hj]
    · show ZeroPadding.pad (c3Cap a R (Fin.natAdd 74 j)) (if (Fin.natAdd 74 j : Fin (74 + 1)).val = 0 then
          frame (c3Input a R) else []) = Fin.addCases (topA0 a R (capOf a R) (cap2Of a R) (cap3Of a R) (cap4Of a R) (cap5Of a R) (capEntOf a R) (capLOf a R))
          (fun _ : Fin 1 => List.replicate (topCost a R) false) (Fin.natAdd 74 j)
      rw [Fin.addCases_right, if_neg (by simp), pad_nil]
      rw [show c3Cap a R (Fin.natAdd 74 j) = topCost a R by simp [c3Cap]]

/-- **The C3 v2 machine on one request** (T6): from the word function's entry bank, every head ends at cell 0 and
tape 1 holds exactly the printer request's word of the reference. -/
theorem c3_run (R : C3Req) (hR : R.Pre a) :
    ∃ A' : Fin (74 + 1) → List Bool, Step c3M (c3Cost a R) (fun _ => 0)
      (fun i => if i.val = 0 then frame (c3Input a R) else []) (fun _ => 0) A' ∧
      A' 1 = reqWord R.dRow (R.p + 1) R.P.width R.cols (c3v2Ref a R) := by
  obtain ⟨Hf, Af, t, hAf⟩ := top_run_caps a R hR
  have m := t.mask (fun _ => true) (by intro i _; fin_cases i <;> rfl) (le_refl (topCost a R))
  obtain ⟨src, hsrc, hh, ht, hs⟩ := m
  have hsrc' : runFrom c3M (2 * topCost a R + 2) (ZeroPadding.config (c3Cap a R)
      (⟨c3M.start, fun _ => 0, fun i => if i.val = 0 then frame (c3Input a R) else []⟩ : Configuration (74 + 1) _)) =
      some src := by
    rw [c3_entry]; exact hsrc
  obtain ⟨r, hr, hcf, hst, _⟩ := ZeroPadding.run_unpad c3M (c3Cap a R) _ _ src hsrc'
  refine ⟨r.final.tapes, ⟨r, hr, ?_, rfl, by unfold c3Cost; omega⟩, ?_⟩
  · have e := congrArg Configuration.heads hcf
    change r.final.heads = src.final.heads at e
    rw [e, hh]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · have e := congrFun (congrArg Configuration.tapes hcf) 1
    change ZeroPadding.pad (c3Cap a R 1) (r.final.tapes 1) = src.final.tapes 1 at e
    rw [ht] at e
    have h0 : c3Cap a R 1 = 0 := rfl
    rw [h0, ZeroPadding.pad_zero] at e
    rw [e]
    exact hAf


end NearCubicWires.WireExponent3_5.CompilerMachine.Top
