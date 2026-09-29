import Proof.Wire_3_5.Compiler.MachineC3aChain

/-! # C3a′'s machine as a word function: from the input word to the pool and its children table (P3:1596-1664)

Paper: alg:disjoint (P3:1602-1615) for every carrier gate, then alg:pullback over every flip pattern (P3:1636-1664),
as one deterministic machine run from the input word. The word function's entry bank has the framed input on tape 0
and every other tape empty; the machine's log tapes are blank tapes of fixed capacities (`c3aCapL`: each covers the
largest cost its stage records), so base's `ZeroPadding.run_unpad` runs the same machine from the empty tapes.
**`c3a_run`**: on every request satisfying C3a′'s pre (`R.Pre`, `CoefFit`, `1 ≤ n`, `1 ≤ h`), the machine `c3aM`
runs in `c3aCost` steps from the word function's entry bank to a bank with every head at cell `0` whose output tape
(the left part's tape 70) is exactly C3a's encoding of the reference. The paper quantity is the contract's output
word. Main declarations: the capacity lemmas, `c3aCap_entry`, **`c3a_run`**, `c3aOut`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Word
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Kit NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Lay
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Run NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Chain
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound

variable (a : DecompositionAlgorithm)

/-! ## The capacities cover the stages -/

theorem cL1 (R : PoolReq) : 2 * (Top.loadRec (List.replicate R.n true) (frame (segR R)) (frame R.side)
    (List.replicate R.width true) (Kit.streamTape R.flips []) (List.replicate R.h true) (List.replicate R.Q true)
    [] [] [] []).length + 1 ≤ capSR a R := by
  show 2 * (recR R).length + 1 ≤ capSR a R; unfold capSR; omega
theorem cL2 (R : PoolReq) : Top.loadChainCost (List.replicate R.n true) (frame (segR R)) (frame R.side)
    (List.replicate R.width true) (Kit.streamTape R.flips []) (List.replicate R.h true) (List.replicate R.Q true)
    [] [] [] [] ≤ capSR a R := by unfold capSR; omega
theorem cDec (R : PoolReq) : C3a.Dec.innerCost a R.n R.gates ≤ capSR a R := by unfold capSR; omega
theorem cNF (R : PoolReq) : C3a.Count.nfLoopCost R.flips.length R.n ≤ capSR a R := by
  show C3a.Count.nfLoopCost (FR R) R.n ≤ capSR a R; unfold capSR; omega
theorem cSC (R : PoolReq) : C3a.Count.scLoopCost R.side.length ≤ capSR a R := by unfold capSR; omega
theorem cK (R : PoolReq) : C3a.Const.kRawCost R.h (BR a R) ≤ capSR a R := by unfold capSR; omega
theorem cZH (R : PoolReq) : Top.wRunCost R.h ≤ capSR a R := by unfold capSR; omega
theorem cW2 (R : PoolReq) : Top.w2Cost [true, false] [true, false, false] (BR a R) ≤ capSR a R := by unfold capSR; omega
theorem cENT (R : PoolReq) : C3a.Const.entRawCost R.Q (PexR a R) ≤ capSR a R := by unfold capSR; omega
theorem cW4 (R : PoolReq) : Top.w4Cost [true, false] [true, false] [true, true] [false] R.Q (PexR a R) ≤ capSR a R := by
  unfold capSR; omega
theorem cZL (R : PoolReq) : C3a.Const.zpRawCost R.h (kLR R) ≤ capSR a R := by unfold capSR; omega
theorem cZR (R : PoolReq) : C3a.Const.zpRawCost R.h (kRR R) ≤ capSR a R := by unfold capSR; omega
theorem cPO (R : PoolReq) : poInR a R ≤ capSR a R := by unfold capSR; omega

/-! ## The padded entry bank -/

theorem pad_nil' (c : ℕ) : ZeroPadding.pad c [] = List.replicate c false := by simp [ZeroPadding.pad]

/-- The word function's entry bank, padded to the capacities, is the stages' entry bank. -/
theorem c3aCap_entry (R : PoolReq) :
    ZeroPadding.config (c3aCap a R)
      (⟨(c3aM a).start, fun _ => 0, fun i => if i.val = 0 then frame (C3a.c3aInput R) else []⟩ : Configuration (U a) _) =
      ⟨(c3aM a).start, fun _ => 0, Fin.addCases (motive := fun _ => List Bool) (L0v R (c3aCapL a R))
        (fun _ : Fin (MR a) => [])⟩ := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change ZeroPadding.pad (c3aCap a R (Fin.castAdd (MR a) j))
          (if (Fin.castAdd (MR a) j : Fin (U a)).val = 0 then frame (C3a.c3aInput R) else []) =
        Fin.addCases (motive := fun _ => List Bool) (L0v R (c3aCapL a R)) (fun _ : Fin (MR a) => [])
          (Fin.castAdd (MR a) j)
      rw [Fin.addCases_left (motive := fun _ => List Bool)]
      unfold c3aCap
      rw [Fin.addCases_left (motive := fun _ => ℕ), Fin.val_castAdd]
      unfold L0v
      by_cases hj : j = 0
      · subst hj
        simp only [Fin.val_zero, if_true]
        rw [show c3aCapL a R 0 = 0 from rfl, ZeroPadding.pad_zero]
      · have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
        rw [if_neg hv, if_neg hj, pad_nil']
    · change ZeroPadding.pad (c3aCap a R (Fin.natAdd 81 j))
          (if (Fin.natAdd 81 j : Fin (U a)).val = 0 then frame (C3a.c3aInput R) else []) =
        Fin.addCases (motive := fun _ => List Bool) (L0v R (c3aCapL a R)) (fun _ : Fin (MR a) => [])
          (Fin.natAdd 81 j)
      rw [Fin.addCases_right (motive := fun _ => List Bool)]
      unfold c3aCap
      rw [Fin.addCases_right (motive := fun _ => ℕ), if_neg (by simp), ZeroPadding.pad_zero]

/-- The output tape: the left part's tape 70. -/
def c3aOut : Fin (U a) := Fin.castAdd (MR a) 70

/-- **C3a′'s machine on one request** (P3:1596-1664): from the word function's entry bank, every head ends at cell
`0` and the output tape holds exactly C3a's encoding of the reference. -/
theorem c3a_run (R : PoolReq) (hR : R.Pre) (hfit : CoefFit a R) (hn : 1 ≤ R.n) (hh : 1 ≤ R.h) :
    ∃ A : Fin (U a) → List Bool, Step (c3aM a) (c3aCost a R) (fun _ => 0)
      (fun i => if i.val = 0 then frame (C3a.c3aInput R) else []) (fun _ => 0) A ∧
      A (c3aOut a) = (poolRecs a R.h R.gates R.side R.width R.flips).flatMap frame ++
        false :: (childTable R.Q (shapeOf (densePool a R.gates R.side R.width R.flips))).flatMap atomStream := by
  obtain ⟨Lf, Rf, st, hf⟩ := top_run_gen a R hR hfit hn hh (capSR a R) (C3a.Const.recRawCost R.h) (SR R) (CsR R)
    (capR a R) (capN2R R) (capN7R a R) (capC2R R) (capC3R R) (capC4R a R) (capF8R a R) (cap5R a R) (capPR a R)
    (cL1 a R) (cL2 a R) (cDec a R) (cNF a R) (cSC a R) (cK a R) (cZH a R) (cW2 a R) le_rfl le_rfl (cENT a R)
    (cW4 a R) (cZL a R) (cZR a R) (cPO a R) le_rfl
    (by unfold capR; omega) (by unfold capR; omega) (by unfold capR FR; omega) (by unfold capR; omega)
    (by unfold capR; omega) (by unfold capR convSum; omega) le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
  obtain ⟨src, hsrc, hh', ht', hs'⟩ := st
  have hsrc' : runFrom (c3aM a) (c3aCost a R) (ZeroPadding.config (c3aCap a R)
      (⟨(c3aM a).start, fun _ => 0, fun i => if i.val = 0 then frame (C3a.c3aInput R) else []⟩ :
        Configuration (U a) _)) = some src := by
    rw [c3aCap_entry]; exact hsrc
  obtain ⟨r, hr, hcf, hst, _⟩ := ZeroPadding.run_unpad (c3aM a) (c3aCap a R) _ _ src hsrc'
  refine ⟨r.final.tapes, ⟨r, hr, ?_, rfl, by omega⟩, ?_⟩
  · have e := congrArg Configuration.heads hcf
    change r.final.heads = src.final.heads at e
    rw [e, hh']
  · have e := congrFun (congrArg Configuration.tapes hcf) (c3aOut a)
    change ZeroPadding.pad (c3aCap a R (c3aOut a)) (r.final.tapes (c3aOut a)) = src.final.tapes (c3aOut a) at e
    rw [ht'] at e
    have h0 : c3aCap a R (c3aOut a) = 0 := rfl
    rw [h0, ZeroPadding.pad_zero] at e
    rw [e]
    show Fin.addCases (motive := fun _ => List Bool) Lf Rf (Fin.castAdd (MR a) 70) = _
    rw [Fin.addCases_left]
    exact hf

end NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Word
