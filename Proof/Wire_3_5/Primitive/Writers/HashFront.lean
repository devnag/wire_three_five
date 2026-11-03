import Proof.Wire_3_5.Primitive.Writers.HashB1Base
import Proof.Wire_3_5.Primitive.Writers.ThrB7Base
import Proof.Wire_3_5.Primitive.Writers.ThrBud2Base
import Proof.Wire_3_5.Primitive.Writers.ThrDataH
import Proof.Wire_3_5.Primitive.Writers.ThrK7Base
import Proof.Wire_3_5.Primitive.Writers.ThrStrip7
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfCBase
import Proof.Wire_3_5.Primitive.SeedFix.TS4WBase

/-! # HASH setup (C), P1: the front's copy on a fresh block

The HASH stage's tail needs the THR call's counts in unary on the bank after the setup
(`HashSet.hash_setup_run`): `1^n` (P3:3071-3091, the circuits' width), `1^{C_L(n+1)^D}` and `1^{C_d(n+1)^D}` (the data
stage's word bound and capacity count, P3:2543-2558), and `1^{2^m}`, `m = ⌊n/8⌋ + C` (the numbers cell's capacity).
The front at capacity v2 (`C4Cap.frontM3`, verified) writes exactly these; it runs again on a fresh block of the bank
`[oF, oF + L.N)`, its request tape the bank's request tape `g0`:

* `fcExt`, **`frontCopyM`**, `fcT`; **`front_copy`**: from a bank with `frame w` on `g0` and blank from `oF` up, within
  `frontCost3`, every head at `0`, the request kept, the four counts on the block's tapes `gN1`, `gUL`, `gUD`, `gUW`,
  every tape below `oF` other than `g0` unchanged, the bank blank above the block.

Paper quantities of the main type: the call's width `n` and the counts `C_L(n+1)^D`, `C_d(n+1)^D`, `2^m` in unary. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set

variable (L : Lay)

/-- The copy's inputs: the front's request tape onto the bank's request tape `g0`, every other tape onto the block. -/
def fcExt {u : ℕ} (g0 : Fin u) (j : Fin L.N) : Option (Fin u) := if j = L.gP0 then some g0 else none

/-- **The front's copy**: the front at capacity v2 on the block `[oF, oF + L.N)`, its request tape the bank's `g0`. -/
noncomputable def frontCopyM (CL Cd C : ℕ) {u : ℕ} (oF : ℕ) (hoF : oF + L.N ≤ u) (g0 : Fin u) :=
  RecoveryFocus.machine (slx oF hoF (fcExt L g0)) (C4Cap.frontM3 L CL Cd C)

/-- The block's tape `j`. -/
def fcT {u : ℕ} (oF : ℕ) (hoF : oF + L.N ≤ u) (j : Fin L.N) : Fin u := ⟨oF + j.val, by have := j.isLt; omega⟩

theorem fcExt_none {u : ℕ} (g0 : Fin u) (j : Fin L.N) (h : j ≠ L.gP0) : fcExt L g0 j = none := by
  unfold fcExt; rw [if_neg h]

/-- **The front's copy, run.** -/
theorem front_copy (hD : 16 ≤ L.D) (CL Cd C n : ℕ) (w sfx : List Bool)
    (hw : w = RepairRepresentation.natWord n ++ sfx) {u : ℕ} (oF : ℕ) (hoF : oF + L.N ≤ u) (g0 : Fin u)
    (hg0 : g0.val < oF) (B : Fin u → List Bool) (hB0 : B g0 = frame w) (hbl : ∀ i : Fin u, oF ≤ i.val → B i = []) :
    ∃ B' : Fin u → List Bool,
      Step (frontCopyM L CL Cd C oF hoF g0) (C4Cap.frontCost3 L w n CL Cd C) (fun _ => 0) B (fun _ => 0) B' ∧
      B' g0 = frame w ∧ B' (fcT L oF hoF L.gN1) = List.replicate n true ∧
      B' (fcT L oF hoF L.gUL) = List.replicate (UnaryCalc.value L.D CL n) true ∧
      B' (fcT L oF hoF L.gUD) = List.replicate (UnaryCalc.value L.D Cd n) true ∧
      B' (fcT L oF hoF L.gUW) = List.replicate (2 ^ C4Cap.capExp2 C n) true ∧
      (∀ i : Fin u, i.val < oF → i ≠ g0 → B' i = B i) ∧ (∀ i : Fin u, oF + L.N ≤ i.val → B' i = []) := by
  set tin : Fin L.N → List Bool := fun j => if j = L.gP0 then frame w else [] with htin
  obtain ⟨T, hT, t0, tN, tL, tD, tW, -, -⟩ := C4Cap.front_run3 L hD CL Cd C n w sfx hw tin (by simp [htin])
    (fun i hi => by
      have hne : i ≠ L.gP0 := fun e => by rw [e] at hi; revert hi; lv
      simp [htin, hne])
  have hinj : ∀ i j g, fcExt L g0 i = some g → fcExt L g0 j = some g → i = j := by
    intro i j g hi hj
    unfold fcExt at hi hj
    split_ifs at hi hj with a b
    rw [a, b]
  have hlt : ∀ i g, fcExt L g0 i = some g → g.val < oF := by
    intro i g hi
    unfold fcExt at hi
    split_ifs at hi
    cases hi
    exact hg0
  obtain ⟨st, bl, un, sl, ex⟩ := stageP hT oF hoF (fcExt L g0) hinj hlt B
    (fun j g hj => by
      unfold fcExt at hj
      split_ifs at hj with h
      cases hj
      rw [htin]
      simp [h, hB0])
    hbl
    (fun j hj => by
      unfold fcExt at hj
      split_ifs at hj with h
      simp [htin, h])
  refine ⟨_, st, ?_, ?_, ?_, ?_, ?_, ?_, bl⟩
  · rw [ex L.gP0 g0 (by simp [fcExt]), t0]
  · rw [sl L.gN1 _ (fcExt_none L g0 _ (by lv)) rfl, tN]
  · rw [sl L.gUL _ (fcExt_none L g0 _ (by lv)) rfl, tL]
  · rw [sl L.gUD _ (fcExt_none L g0 _ (by lv)) rfl, tD]
  · rw [sl L.gUW _ (fcExt_none L g0 _ (by lv)) rfl, tW]
  · intro i hi hne
    refine un i hi (fun j hj => ?_)
    unfold fcExt at hj
    split_ifs at hj
    cases hj
    exact hne rfl

end NearCubicWires.WireExponent3_5.PrimAsm.HashSet
