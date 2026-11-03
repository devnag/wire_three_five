import Proof.Wire_3_5.FinalPass.S5TPre7

/-! # S5-THR, part 27: the THR half's stage (P3:3083-3086, 3170-3181)

The stage the scrub runs: the parse (`parseW`: `n`, `a`, the mode flag), then the mode branch
(`iteMachine` on the flag's register): the THR path at a THR call, nothing at a SYM call.

* `ite_stepT`, `ite_stepF` (a branch machine runs the taken branch, one test step);
* `stageM`, **`stage_thr`** (all eight THR slots written), **`stage_sym`** (the THR slots kept blank).

Paper quantities of the main types: THR slots `8 … 15` at a THR call (S2's words and numbers); at a SYM call the
THR slots stay empty (`frontWordsOfW` at a SYM request, slots `8 … 15`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.HashSeed NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimThrW.TopFront2 (tf2InPorts tf2OutPorts TF2Ok)
open NearCubicWires.SupplierPipeline

section Ite
variable {t : ℕ}

theorem ite_stepT (i : Fin t) {a b : ℕ} (p : Machine t a) (q : Machine t b) (bk c : Bank t) (n : ℕ)
    (hb : bk.bit i = true) (h : Step p n bk.H bk.A c.H c.A) : Step (iteMachine i p q) (n + 1) bk.H bk.A c.H c.A :=
  ite_branch_step i p q bk c n (iteL b) p (by simp [hb]) (ite_halted_L i p q) (ite_step_L i p q) h

theorem ite_stepF (i : Fin t) {a b : ℕ} (p : Machine t a) (q : Machine t b) (bk c : Bank t) (n : ℕ)
    (hb : bk.bit i = false) (h : Step q n bk.H bk.A c.H c.A) : Step (iteMachine i p q) (n + 1) bk.H bk.A c.H c.A :=
  ite_branch_step i p q bk c n (iteR a) q (by simp [hb]) (ite_halted_R i p q) (ite_step_R i p q) h

end Ite

section Stage
variable (D : ℕ) (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ) (cap : ℕ)

theorem sIn_ne_sTm : sIn D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ≠
    sTm D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x := fun h => by
  have := congrArg Fin.val h; simp [sIn, sTm] at this

end Stage


end NearCubicWires.WireExponent3_5.FinalPass.S5T
