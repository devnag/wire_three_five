import Proof.Wire_3_5.UnionMachine.FsKit
import Proof.Wire_3_5.UnionMachine.RegRatMul

/-! # C6, e/W_j, part 4: the auxiliary exponent `e` in binary

"`H_h(x) ≤ H_max := A(M + J M^{2t}) = 2^{O_D(L^2)}`" (filt:H-bounds, P3:2143): `M^{2t}` is quasi-polynomial, so the
THR primitive's auxiliary exponent `e = ⌈log₂(8K·A(M + J·M^{2t}) + 1)⌉ + 1` (`Primitive.listE`) is computed on
fixed-width BINARY words (C1's `NumOn`, C1.2's `RegRat` passes) of width
`wd = 2tM + M + J + K + A + 8` (`wdOf`), in the stage's own layout `WState 8 48`:
registers `0 … 5` = `M, A, B_*, K, J, t` (kept), `6` = `e`, `36` width, `37` `8KA`, `38` counter, `39 40 41` the
passes' flag/counter registers, `42 … 47` the binary writer's scratch, `7 … 10` temporaries; streams `1 … 8` the words
`Mw, Jw, Cw, P, C, S, X, Q`.
* **`e1_spec`**: the width and `8KA` in unary registers; **`e2_spec`**: the eight words (X1's `binW`).

Paper quantity: the auxiliary filter's error exponent `e` (`Primitive.listE`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.EwBin
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.BinW (dupR)

variable (cap : ℕ)

/-- **The words' width** `2tM + M + J + K + A + 8`. -/
def wdOf (M A K J t : ℕ) : ℕ := t * M + t * M + M + J + K + A + 8

/-- The size measure of the unary stage. -/
def zOf (M A K J t : ℕ) : ℕ := wdOf M A K J t + 8 * (K * A) + t

/-- The unary numbers: `36 := wd`, `37 := 8KA` (temporaries `8`, `9`, `10` back at `0`). -/
def e1W : WM 8 48 :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq
    (FsKit.mulR 0 5 36 8 9) (FsKit.mulR 0 5 36 8 9)) (dupR 0 36 8)) (dupR 4 36 8)) (dupR 3 36 8)) (dupR 1 36 8))
    (FsKit.incK 36 8)) (FsKit.mulR 1 3 10 8 9)) (FsKit.mulK 10 37 8 8)) (WM.clear 10)

theorem e1_spec (σ : WState 8 48) (M A K J t : ℕ) (hM : σ.val 0 = M) (hA : σ.val 1 = A) (hK : σ.val 3 = K)
    (hJ : σ.val 4 = J) (ht : σ.val 5 = t) (z8 : σ.val 8 = 0) (z9 : σ.val 9 = 0) (z10 : σ.val 10 = 0)
    (z36 : σ.val 36 = 0) (z37 : σ.val 37 = 0) (hcap : zOf M A K J t + 10 ≤ cap) :
    WExec cap e1W σ ((σ.setv 36 (wdOf M A K J t)).setv 37 (8 * (K * A)))
      (500 * (zOf M A K J t + 1) * (zOf M A K J t + 1)) := by
  unfold zOf wdOf at hcap
  have c1 := FsKit.mulR_spec cap 0 5 36 8 9 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) σ M t hM ht z8 z9 (by rw [z36]; omega) (by omega) (by omega)
  have c2 := WExec.seq c1 (FsKit.mulR_spec cap 0 5 36 8 9 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) _ M t (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]) (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]) (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]) (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37])
    (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]; omega) (by omega) (by omega))
  have c3 := WExec.seq c2 (FsKit.addR_spec cap 0 36 8 (by decide) (by decide) (by decide) _ M (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37])
    (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]) (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]; omega) (by omega))
  have c4 := WExec.seq c3 (FsKit.addR_spec cap 4 36 8 (by decide) (by decide) (by decide) _ J (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37])
    (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]) (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]; omega) (by omega))
  have c5 := WExec.seq c4 (FsKit.addR_spec cap 3 36 8 (by decide) (by decide) (by decide) _ K (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37])
    (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]) (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]; omega) (by omega))
  have c6 := WExec.seq c5 (FsKit.addR_spec cap 1 36 8 (by decide) (by decide) (by decide) _ A (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37])
    (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]) (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]; omega) (by omega))
  have c7 := WExec.seq c6 (FsKit.incK_spec cap 36 8 _ (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]; omega))
  have c8 := WExec.seq c7 (FsKit.mulR_spec cap 1 3 10 8 9 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) _ A K (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]) (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]) (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]) (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37])
    (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]; omega) (by omega) (by omega))
  have c9 := WExec.seq c8 (FsKit.mulK_spec cap 10 37 8 (by decide) (by decide) (by decide) (K * A) 8 _
    (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]) (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]) (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]; omega) (by omega))
  have c10 := WExec.seq c9 (wclear_spec cap 10 (K * A) _ (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]) (by simp [Function.update_apply, hM, hA, hK, hJ, ht, z8, z9, z10, z36, z37]; omega))
  refine WExec.cast cap c10 ?_ ?_
  · clear c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
    apply WState.eq
    · simp
    · simp
    · funext r
      simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [wdOf] <;> omega
    · simp
  · obtain ⟨Z, hZ⟩ : ∃ Z, Z = t * M + t * M + M + J + K + A + 8 + 8 * (K * A) + t := ⟨_, rfl⟩
    have hZ' : zOf M A K J t = Z := by unfold zOf wdOf; omega
    rw [hZ']
    have ht' : t ≤ Z := by omega
    have hKA : K * A ≤ Z := by omega
    have hA' : A ≤ Z := by omega
    have hK' : K ≤ Z := by omega
    have hM' : M ≤ Z := by omega
    have hJ' : J ≤ Z := by omega
    have p1 : t * (18 * M + 7) ≤ Z * (18 * Z + 7) := Nat.mul_le_mul ht' (by omega)
    have p2 : K * (18 * A + 7) ≤ Z * (18 * Z + 7) := Nat.mul_le_mul hK' (by omega)
    nlinarith

end NearCubicWires.WireExponent3_5.UnionMachine.EwBin
