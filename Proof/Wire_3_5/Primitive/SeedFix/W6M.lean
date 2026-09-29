import Proof.Wire_3_5.Primitive.SeedFix.W6L
import Proof.Wire_3_5.Primitive.ThresholdWriter.W6Dock
import Proof.Wire_3_5.UnionMachine.EwStage

/-! # W6, part 13: the aux filter's `e` and the level windows `W_j` (the EW stage docked)

P3:2220-2231 (the auxiliary filter's error exponent `e`) and P3:2150-2157 (filt:majorant: "`W_j = 16t + 20(⌊√(t·B_*)⌋ +
1)/2^{⌊j/2⌋} + 20`", the fixed hash's level records, port `18`), computed by C6b's verified stage `EwStage.run` on its own
layout `WState 8 48`, run inside the numbers machine's layout (`W6Dock.dockL`, **`ewL`**: EW stream `0` on `sWin`, its
streams `1 … 8` on `152 … 159`, its cell on stream `160`, its registers on `0 … 47`):
* `ewI_rr` (the inputs `M, A, B_*, K, J, t` into `0 … 5`), `ewO_rr` (`rEe := e`, `0 … 6` cleared);
* **`ew_phase`**: `rEe = Primitive.listE A B_* M K`, `sWin = Joins.winRecs (thrMP M A B_* K)` (head `0`), the streams
  `152 … 160` bounded residues, everything else as found.

Paper quantities of the main type: `e` and the level records `W_j`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)

variable (cap : ℕ)

/-- The EW stage's inputs `M, A, B_*, K, J, t` into registers `0 … 5`. -/
def ewIW : WP :=
  .seq (wcopyR 50 0 76) (.seq (wcopyR 60 1 76) (.seq (wcopyR 61 2 76) (.seq (wcopyR 55 3 76) (.seq (wcopyR 62 4 76) (wcopyR 63 5 76)))))

theorem ewI_c0 (f : Fin 80 → ℕ) (M : ℕ) (A : ℕ) (B : ℕ) (K : ℕ) (J : ℕ) (t : ℕ) (h50 : f 50 = M) (h0 : f 0 = 0) (h76 : f 76 = 0) (h60 : f 60 = A) (h1 : f 1 = 0) (h61 : f 61 = B) (h2 : f 2 = 0) (h55 : f 55 = K) (h3 : f 3 = 0) (h62 : f 62 = J) (h4 : f 4 = 0) (h63 : f 63 = t) (h5 : f 5 = 0)
    (hb0 : M ≤ cap) (hb1 : A ≤ cap) (hb2 : B ≤ cap) (hb3 : K ≤ cap) (hb4 : J ≤ cap) (hb5 : t ≤ cap) :
    RegRun cap (.seq (wcopyR 50 0 76) (.seq (wcopyR 60 1 76) (.seq (wcopyR 61 2 76) (.seq (wcopyR 55 3 76) (.seq (wcopyR 62 4 76) (wcopyR 63 5 76)))))) f
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update f 0 (M)) 1 (A)) 2 (B)) 3 (K)) 4 (J)) 5 (t)) (6 * (opU cap + 1)) :=
  RegRun.mono cap ((wcopy_rr cap 50 0 76 (by decide) (by decide) (by decide) f (M) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5])
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]; omega)).seq cap
    ((wcopy_rr cap 60 1 76 (by decide) (by decide) (by decide) _ (A) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5])
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]; omega)).seq cap
    ((wcopy_rr cap 61 2 76 (by decide) (by decide) (by decide) _ (B) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5])
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]; omega)).seq cap
    ((wcopy_rr cap 55 3 76 (by decide) (by decide) (by decide) _ (K) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5])
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]; omega)).seq cap
    ((wcopy_rr cap 62 4 76 (by decide) (by decide) (by decide) _ (J) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5])
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]; omega)).seq cap
    ((wcopy_rr cap 63 5 76 (by decide) (by decide) (by decide) _ (t) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5])
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50, h0, h76, h60, h1, h61, h2, h55, h3, h62, h4, h63, h5]; omega)))))))) (by omega)

theorem ewI_regs (f : Fin 80 → ℕ) (M : ℕ) (A : ℕ) (B : ℕ) (K : ℕ) (J : ℕ) (t : ℕ) (z0 : f 0 = 0) (z1 : f 1 = 0) (z2 : f 2 = 0) (z3 : f 3 = 0) (z4 : f 4 = 0) (z5 : f 5 = 0) (z76 : f 76 = 0) (i50 : f 50 = M) (i60 : f 60 = A) (i61 : f 61 = B) (i55 : f 55 = K) (i62 : f 62 = J) (i63 : f 63 = t) :
    Function.update (Function.update (Function.update (Function.update (Function.update (Function.update f 0 (M)) 1 (A)) 2 (B)) 3 (K)) 4 (J)) 5 (t) =
      Function.update (Function.update (Function.update (Function.update (Function.update (Function.update f 0 (M)) 1 (A)) 2 (B)) 3 (K)) 4 (J)) 5 (t) := rfl

/-- **`ewIW`** as a register run. -/
theorem ewI_rr (f : Fin 80 → ℕ) (M : ℕ) (A : ℕ) (B : ℕ) (K : ℕ) (J : ℕ) (t : ℕ) (z0 : f 0 = 0) (z1 : f 1 = 0) (z2 : f 2 = 0) (z3 : f 3 = 0) (z4 : f 4 = 0) (z5 : f 5 = 0) (z76 : f 76 = 0) (i50 : f 50 = M) (i60 : f 60 = A) (i61 : f 61 = B) (i55 : f 55 = K) (i62 : f 62 = J) (i63 : f 63 = t)
    (hb0 : M ≤ cap) (hb1 : A ≤ cap) (hb2 : B ≤ cap) (hb3 : K ≤ cap) (hb4 : J ≤ cap) (hb5 : t ≤ cap) :
    RegRun cap ewIW f (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update f 0 (M)) 1 (A)) 2 (B)) 3 (K)) 4 (J)) 5 (t)) (7 * (opU cap + 1)) :=
  (((ewI_c0 cap f M A B K J t (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z0, z1, z2, z3, z4, z5, z76, i50, i60, i61, i55, i62, i63]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z0, z1, z2, z3, z4, z5, z76, i50, i60, i61, i55, i62, i63]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z0, z1, z2, z3, z4, z5, z76, i50, i60, i61, i55, i62, i63]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z0, z1, z2, z3, z4, z5, z76, i50, i60, i61, i55, i62, i63]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z0, z1, z2, z3, z4, z5, z76, i50, i60, i61, i55, i62, i63]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z0, z1, z2, z3, z4, z5, z76, i50, i60, i61, i55, i62, i63]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z0, z1, z2, z3, z4, z5, z76, i50, i60, i61, i55, i62, i63]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z0, z1, z2, z3, z4, z5, z76, i50, i60, i61, i55, i62, i63]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z0, z1, z2, z3, z4, z5, z76, i50, i60, i61, i55, i62, i63]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z0, z1, z2, z3, z4, z5, z76, i50, i60, i61, i55, i62, i63]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z0, z1, z2, z3, z4, z5, z76, i50, i60, i61, i55, i62, i63]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z0, z1, z2, z3, z4, z5, z76, i50, i60, i61, i55, i62, i63]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z0, z1, z2, z3, z4, z5, z76, i50, i60, i61, i55, i62, i63]) hb0 hb1 hb2 hb3 hb4 hb5)).congr cap (ewI_regs f M A B K J t z0 z1 z2 z3 z4 z5 z76 i50 i60 i61 i55 i62 i63)).mono cap (by omega)

/-- `rEe := e` (register `6`), the EW registers `0 … 6` cleared. -/
def ewOW : WP :=
  .seq (wcopyR 6 64 76) (.seq (WM.clear 0) (.seq (WM.clear 1) (.seq (WM.clear 2) (.seq (WM.clear 3) (.seq (WM.clear 4) (.seq (WM.clear 5) (WM.clear 6)))))))

theorem ewO_c0 (f : Fin 80 → ℕ) (M : ℕ) (A : ℕ) (B : ℕ) (K : ℕ) (J : ℕ) (t : ℕ) (e : ℕ) (h6 : f 6 = e) (h64 : f 64 = 0) (h76 : f 76 = 0) (h0 : f 0 = M) (h1 : f 1 = A) (h2 : f 2 = B) (h3 : f 3 = K) (h4 : f 4 = J) (h5 : f 5 = t)
    (hb0 : e ≤ cap) (hb1 : M ≤ cap) (hb2 : A ≤ cap) (hb3 : B ≤ cap) (hb4 : K ≤ cap) (hb5 : J ≤ cap) (hb6 : t ≤ cap) :
    RegRun cap (.seq (wcopyR 6 64 76) (.seq (WM.clear 0) (.seq (WM.clear 1) (.seq (WM.clear 2) (.seq (WM.clear 3) (.seq (WM.clear 4) (.seq (WM.clear 5) (WM.clear 6)))))))) f
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update f 64 (e)) 0 (0)) 1 (0)) 2 (0)) 3 (0)) 4 (0)) 5 (0)) 6 (0)) (8 * (opU cap + 1)) :=
  RegRun.mono cap ((wcopy_rr cap 6 64 76 (by decide) (by decide) (by decide) f (e) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h6, h64, h76, h0, h1, h2, h3, h4, h5])
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h6, h64, h76, h0, h1, h2, h3, h4, h5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h6, h64, h76, h0, h1, h2, h3, h4, h5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h6, h64, h76, h0, h1, h2, h3, h4, h5]; omega)).seq cap
    ((clear_rr cap 0 _ (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h6, h64, h76, h0, h1, h2, h3, h4, h5]; omega)).seq cap
    ((clear_rr cap 1 _ (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h6, h64, h76, h0, h1, h2, h3, h4, h5]; omega)).seq cap
    ((clear_rr cap 2 _ (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h6, h64, h76, h0, h1, h2, h3, h4, h5]; omega)).seq cap
    ((clear_rr cap 3 _ (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h6, h64, h76, h0, h1, h2, h3, h4, h5]; omega)).seq cap
    ((clear_rr cap 4 _ (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h6, h64, h76, h0, h1, h2, h3, h4, h5]; omega)).seq cap
    ((clear_rr cap 5 _ (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h6, h64, h76, h0, h1, h2, h3, h4, h5]; omega)).seq cap
    ((clear_rr cap 6 _ (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h6, h64, h76, h0, h1, h2, h3, h4, h5]; omega)))))))))) (by omega)

theorem ewO_regs (f : Fin 80 → ℕ) (M : ℕ) (A : ℕ) (B : ℕ) (K : ℕ) (J : ℕ) (t : ℕ) (e : ℕ) (z64 : f 64 = 0) (z76 : f 76 = 0) (i0 : f 0 = M) (i1 : f 1 = A) (i2 : f 2 = B) (i3 : f 3 = K) (i4 : f 4 = J) (i5 : f 5 = t) (i6 : f 6 = e) :
    Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update f 64 (e)) 0 (0)) 1 (0)) 2 (0)) 3 (0)) 4 (0)) 5 (0)) 6 (0) =
      Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update f 64 (e)) 0 (0)) 1 (0)) 2 (0)) 3 (0)) 4 (0)) 5 (0)) 6 (0) := rfl

/-- **`ewOW`** as a register run. -/
theorem ewO_rr (f : Fin 80 → ℕ) (M : ℕ) (A : ℕ) (B : ℕ) (K : ℕ) (J : ℕ) (t : ℕ) (e : ℕ) (z64 : f 64 = 0) (z76 : f 76 = 0) (i0 : f 0 = M) (i1 : f 1 = A) (i2 : f 2 = B) (i3 : f 3 = K) (i4 : f 4 = J) (i5 : f 5 = t) (i6 : f 6 = e)
    (hb0 : e ≤ cap) (hb1 : M ≤ cap) (hb2 : A ≤ cap) (hb3 : B ≤ cap) (hb4 : K ≤ cap) (hb5 : J ≤ cap) (hb6 : t ≤ cap) :
    RegRun cap ewOW f (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update f 64 (e)) 0 (0)) 1 (0)) 2 (0)) 3 (0)) 4 (0)) 5 (0)) 6 (0)) (9 * (opU cap + 1)) :=
  (((ewO_c0 cap f M A B K J t e (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z64, z76, i0, i1, i2, i3, i4, i5, i6]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z64, z76, i0, i1, i2, i3, i4, i5, i6]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z64, z76, i0, i1, i2, i3, i4, i5, i6]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z64, z76, i0, i1, i2, i3, i4, i5, i6]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z64, z76, i0, i1, i2, i3, i4, i5, i6]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z64, z76, i0, i1, i2, i3, i4, i5, i6]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z64, z76, i0, i1, i2, i3, i4, i5, i6]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z64, z76, i0, i1, i2, i3, i4, i5, i6]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z64, z76, i0, i1, i2, i3, i4, i5, i6]) hb0 hb1 hb2 hb3 hb4 hb5 hb6)).congr cap (ewO_regs f M A B K J t e z64 z76 i0 i1 i2 i3 i4 i5 i6)).mono cap (by omega)

/-! ## The EW stage inside the numbers machine -/

/-- **The EW layout inside W6's**: stream `0` on `sWin`, streams `1 … 8` on `152 … 159`, the cell on `160`, the
registers on `0 … 47`. -/
def ewL : PrimThrW.W6Dock.SubL 8 48 191 80 where
  sm := ![20, 152, 153, 154, 155, 156, 157, 158, 159]
  rm := fun r => ⟨r.val, by omega⟩
  cs := 160
  sm_inj := by decide
  rm_inj := fun a b h => Fin.ext (by simpa using congrArg Fin.val h)
  cs_ne := by decide

def ewPreW : WP := .seq ewIW (.wr 160 false)

/-- **The EW phase**: the inputs, the docked stage, `e` kept. -/
noncomputable def ewM :=
  Composition.machine (Composition.machine ewPreW.toProg.compile
    (RecoveryFocus.machine ewL.tm UnionMachine.EwStage.ewProg.toProg.compile)) ewOW.toProg.compile

theorem ew_phase (σ : WL) (M A B K : ℕ) (hM : σ.val 50 = M) (hA : σ.val 60 = A) (hB : σ.val 61 = B)
    (hK : σ.val 55 = K) (hJ : σ.val 62 = Primitive.listJ A B K) (hT : σ.val 63 = Primitive.listT A B K)
    (hz : ∀ r : Fin 80, r.val < 48 → σ.val r = 0) (z64 : σ.val 64 = 0) (z76 : σ.val 76 = 0)
    (hs : ∀ i : Fin 9, σ.st (ewL.sm i) = [] ∧ σ.sh (ewL.sm i) = 0) (hcs : σ.st 160 = [] ∧ σ.sh 160 = 0)
    (bM : M ≤ cap) (bA : A ≤ cap) (bB : B ≤ cap) (bK : K ≤ cap) (bJ : Primitive.listJ A B K ≤ cap)
    (bT : Primitive.listT A B K ≤ cap) (bE : Primitive.listE A B M K ≤ cap)
    (hneed : UnionMachine.EwSize.ewNeed (M + A + B + K) ≤ cap) :
    ∃ (τ : WL) (m : ℕ), Step ewM m (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      m ≤ 20 * (opU cap + 1) + UnionMachine.EwSize.ewBound (M + A + B + K) ∧
      τ.val = Function.update σ.val 64 (Primitive.listE A B M K) ∧
      τ.st 20 = PrimThrW.Joins.winRecs (PrimThrW.Joins.thrMP M A B K) ∧ τ.sh 20 = 0 ∧
      (∀ i : Fin 9, i ≠ 0 → (τ.st (ewL.sm i)).length ≤ UnionMachine.EwSize.ewBound (M + A + B + K) ∧
        τ.sh (ewL.sm i) = 0) ∧ τ.st 160 = [false] ∧ τ.sh 160 = 0 ∧
      (∀ s, (∀ i, ewL.sm i ≠ s) → s ≠ 160 → τ.st s = σ.st s ∧ τ.sh s = σ.sh s) ∧ τ.cell = σ.cell := by
  have z0 : σ.val 0 = 0 := hz 0 (by decide)
  have z1 : σ.val 1 = 0 := hz 1 (by decide)
  have z2 : σ.val 2 = 0 := hz 2 (by decide)
  have z3 : σ.val 3 = 0 := hz 3 (by decide)
  have z4 : σ.val 4 = 0 := hz 4 (by decide)
  have z5 : σ.val 5 = 0 := hz 5 (by decide)
  have h1 := ewI_rr cap σ.val M A B K (Primitive.listJ A B K) (Primitive.listT A B K) z0 z1 z2 z3 z4 z5 z76 hM hA hB hK hJ hT
    bM bA bB bK bJ bT σ rfl
  set g1 : Fin 80 → ℕ := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update σ.val 0 M) 1 A) 2 B) 3 K) 4 (Primitive.listJ A B K)) 5 (Primitive.listT A B K) with hg1
  have h2 := WExec.wr (cap := cap) 160 false (⟨σ.sh, σ.st, g1, σ.cell⟩ : WL)
  have s1 := (WExec.exec cap (WExec.seq h1 h2)).step
  set σ1 : WL := (⟨σ.sh, σ.st, g1, σ.cell⟩ : WL).sets 160 (writeTapeBit ((⟨σ.sh, σ.st, g1, σ.cell⟩ : WL).st 160)
    ((⟨σ.sh, σ.st, g1, σ.cell⟩ : WL).sh 160) false) with hσ1
  have hσ1st : σ1.st 160 = [false] := by
    show Function.update σ.st 160 (writeTapeBit (σ.st 160) (σ.sh 160) false) 160 = [false]
    rw [Function.update_self, hcs.1, hcs.2]
    rfl
  let σs : WState 8 48 := ⟨fun _ => 0, fun _ => [], fun r => g1 (ewL.rm r), false⟩
  have hag : ewL.Agree σs σ1 := by
    refine ⟨fun i => ⟨?_, ?_⟩, fun r => rfl, hσ1st, hcs.2⟩
    · show Function.update σ.st 160 _ (ewL.sm i) = []
      rw [Function.update_of_ne (show ewL.sm i ≠ 160 from ewL.cs_ne i)]
      exact (hs i).1
    · exact (hs i).2
  have hg1lo : ∀ r : Fin 80, 6 ≤ r.val → g1 r = σ.val r := fun r hr => by
    have n0 : r ≠ 0 := fun h => by rw [h] at hr; exact absurd hr (by decide)
    have n1 : r ≠ 1 := fun h => by rw [h] at hr; exact absurd hr (by decide)
    have n2 : r ≠ 2 := fun h => by rw [h] at hr; exact absurd hr (by decide)
    have n3 : r ≠ 3 := fun h => by rw [h] at hr; exact absurd hr (by decide)
    have n4 : r ≠ 4 := fun h => by rw [h] at hr; exact absurd hr (by decide)
    have n5 : r ≠ 5 := fun h => by rw [h] at hr; exact absurd hr (by decide)
    rw [hg1]
    simp only [Function.update_apply, n0, n1, n2, n3, n4, n5, if_false]
  have hrun := UnionMachine.EwStage.run cap M A B K σs (by show g1 0 = M; rw [hg1]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add])
    (by show g1 1 = A; rw [hg1]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by show g1 2 = B; rw [hg1]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by show g1 3 = K; rw [hg1]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add])
    (by show g1 4 = _; rw [hg1]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by show g1 5 = _; rw [hg1]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add])
    (fun r hr => by
      have h6 : 6 ≤ r.val := by
        by_contra hlt
        have hlt' : r.val < 6 := by omega
        apply hr ⟨r.val, hlt'⟩
        apply Fin.ext
        show (UnionMachine.EwStage.inpR ⟨r.val, hlt'⟩).val = r.val
        generalize hv : r.val = v at hlt'
        interval_cases v <;> rfl
      show g1 ⟨r.val, by omega⟩ = 0
      rw [hg1lo _ h6]
      exact hz _ (by show r.val < 48; omega))
    (fun i => ⟨rfl, rfl⟩) rfl hneed
  obtain ⟨τs, m1, hst1, hm1, hkeep, h6, hzero, hwin, hwin0, hres, hcell⟩ := hrun
  obtain ⟨τ2, hst2, hag2, hout_s, hout_r, hcell2⟩ := PrimThrW.W6Dock.dockL ewL cap hst1 σ1 hag
  have hv_lo : ∀ r : Fin 48, τ2.val (ewL.rm r) = τs.val r := hag2.2.1
  have hv_hi : ∀ r : Fin 80, 48 ≤ r.val → τ2.val r = σ1.val r := fun r hr =>
    hout_r r (fun r1 h => by
      have := congrArg Fin.val h
      have h48 := r1.isLt
      simp only [ewL] at this
      omega)
  have t0 : τ2.val 0 = M := (hv_lo 0).trans ((hkeep 0).trans (by show g1 0 = M; rw [hg1]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]))
  have t1 : τ2.val 1 = A := (hv_lo 1).trans ((hkeep 1).trans (by show g1 1 = A; rw [hg1]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]))
  have t2 : τ2.val 2 = B := (hv_lo 2).trans ((hkeep 2).trans (by show g1 2 = B; rw [hg1]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]))
  have t3 : τ2.val 3 = K := (hv_lo 3).trans ((hkeep 3).trans (by show g1 3 = K; rw [hg1]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]))
  have t4 : τ2.val 4 = Primitive.listJ A B K := (hv_lo 4).trans ((hkeep 4).trans (by show g1 4 = _; rw [hg1]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]))
  have t5 : τ2.val 5 = Primitive.listT A B K := (hv_lo 5).trans ((hkeep 5).trans (by show g1 5 = _; rw [hg1]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]))
  have t6 : τ2.val 6 = Primitive.listE A B M K := (hv_lo 6).trans h6
  have t64 : τ2.val 64 = 0 := (hv_hi 64 (by decide)).trans (by show g1 64 = 0; rw [hg1lo 64 (by decide)]; exact z64)
  have t76 : τ2.val 76 = 0 := (hv_hi 76 (by decide)).trans (by show g1 76 = 0; rw [hg1lo 76 (by decide)]; exact z76)
  have h3 := ewO_rr cap τ2.val M A B K (Primitive.listJ A B K) (Primitive.listT A B K) (Primitive.listE A B M K) t64 t76 t0 t1 t2 t3 t4 t5 t6
    bE bM bA bB bK bJ bT τ2 rfl
  have hF : Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update τ2.val 64 (Primitive.listE A B M K)) 0 (0)) 1 (0)) 2 (0)) 3 (0)) 4 (0)) 5 (0)) 6 (0) =
      Function.update σ.val 64 (Primitive.listE A B M K) := by
    funext r
    by_cases h64 : r = 64
    · subst h64
      simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]
    · by_cases hlo : r.val < 7
      · have key : ∀ k : Fin 7, Function.update (Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update τ2.val 64 (Primitive.listE A B M K)) 0 (0)) 1 (0)) 2 (0)) 3 (0)) 4 (0)) 5 (0))
            6 (0) ⟨k.val, by omega⟩ = 0 := by
          intro k
          fin_cases k <;> simp [Function.update_apply]
        rw [Function.update_of_ne h64, hz r (by omega)]
        exact key ⟨r.val, hlo⟩
      · have n0 : r ≠ 0 := fun h => hlo (by rw [h]; decide)
        have n1 : r ≠ 1 := fun h => hlo (by rw [h]; decide)
        have n2 : r ≠ 2 := fun h => hlo (by rw [h]; decide)
        have n3 : r ≠ 3 := fun h => hlo (by rw [h]; decide)
        have n4 : r ≠ 4 := fun h => hlo (by rw [h]; decide)
        have n5 : r ≠ 5 := fun h => hlo (by rw [h]; decide)
        have n6 : r ≠ 6 := fun h => hlo (by rw [h]; decide)
        simp only [Function.update_apply, n0, n1, n2, n3, n4, n5, n6, h64, if_false]
        by_cases hr : r.val < 48
        · rw [hz r hr]
          have e1 : τ2.val r = τs.val ⟨r.val, hr⟩ := hv_lo ⟨r.val, hr⟩
          rw [e1]
          refine hzero ⟨r.val, hr⟩ (fun k hk => ?_) (fun h => ?_)
          · have := congrArg Fin.val hk
            fin_cases k <;> simp [UnionMachine.EwStage.inpR] at this <;> omega
          · have := congrArg Fin.val h
            simp at this
            omega
        · rw [hv_hi r (by omega)]
          exact hg1lo r (by omega)
  rw [hF] at h3
  have s3 := (WExec.exec cap h3).step
  refine ⟨⟨τ2.sh, τ2.st, Function.update σ.val 64 (Primitive.listE A B M K), τ2.cell⟩, _, (s1.seq hst2).seq s3, ?_, rfl,
    (hag2.1 0).1.trans hwin, (hag2.1 0).2.trans hwin0, fun i hi => ⟨?_, (hag2.1 i).2.trans (hres i hi).2⟩, ?_, hag2.2.2.2,
    fun s h1s h2s => ?_, hcell2⟩
  · omega
  · show (τ2.st (ewL.sm i)).length ≤ _
    rw [(hag2.1 i).1]
    exact (hres i hi).1
  · show τ2.st ewL.cs = [false]
    rw [hag2.2.2.1, hcell]
  · obtain ⟨e1, e2⟩ := hout_s s h1s h2s
    refine ⟨e1.trans ?_, e2⟩
    show Function.update σ.st 160 _ s = σ.st s
    rw [Function.update_of_ne h2s]

end NearCubicWires.WireExponent3_5.PrimT.W6
