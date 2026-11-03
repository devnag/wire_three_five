import Proof.Wire_3_5.UnionMachine.EwWords
import Proof.Wire_3_5.UnionMachine.RegRatMul
import Proof.Wire_3_5.Primitive.Writers.UnaryPow

/-! # C6, e/W_j, part 6: the power `M^{2t}` and the product `8KA(M + J·M^{2t}) + 1`

On the eight words (`EwWords.e2_spec`): the counter `38 := 2t`, then `2t` rounds of `C := P·M` (C1.2's `mulB`,
scratch `S`), `P := C` (`copyB`) give `P = C = M^{2t}` (**`pow_spec`**); then `X := J·P`, `X := X + M`,
`C := Cw·X`, `C := C + 1` (**`prod_spec`**). Exact final states; every value below `2^{wd}` by hypothesis.

Paper quantity: `H_max = A(M + J M^{2t})` (filt:H-bounds, P3:2143) scaled by `8K`, plus one. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.EwPow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.BinW (dupR)
open NearCubicWires.WireExponent3_5.UnionMachine.EwWords (fw)

variable (cap : ℕ)

/-- One round: `38 := 38 − 1`, `C := P·M`, `P := C`. -/
def powBody : WM 8 48 := .seq (.seq (.dec 38) (RegRat.mulB 4 1 5 6 39 40 41)) (RegRat.copyB 4 5 39 40)

/-- The state after `i` rounds. -/
def powSt (σ : WState 8 48) (wd M t i : ℕ) : WState 8 48 :=
  ((σ.sets 4 (fw wd (M ^ i))).sets 5 (fw wd (M ^ i))).setv 38 (2 * t - i)

section Pow
variable (σ : WState 8 48) (wd M t : ℕ) (h1 : σ.st 1 = fw wd M) (h1h : σ.sh 1 = 0) (h4h : σ.sh 4 = 0)
  (h5h : σ.sh 5 = 0) (h6 : σ.st 6 = fw wd 0) (h6h : σ.sh 6 = 0) (z39 : σ.val 39 = 0) (z40 : σ.val 40 = 0)
  (z41 : σ.val 41 = 0)
include h1 h1h h4h h5h h6 h6h z39 z40 z41

theorem powBody_spec (i : ℕ) (hi : i < 2 * t) (hMi : M ^ i * M < 2 ^ wd) (hM : M < 2 ^ wd)
    (hcap : 2 * wd + 2 * t + 1 ≤ cap) :
    WExec cap powBody (powSt σ wd M t i) (powSt σ wd M t (i + 1)) (RegRat.mulCost wd + 41 * wd + 10) := by
  have c1 := WExec.dec (cap := cap) 38 (powSt σ wd M t i) (by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41]; omega)
  have c2 := WExec.seq c1 (RegRat.mulB_spec cap wd (ns := 8) (nr := 48) (A := 4) (B := 1) (C := 5) (S := 6) (F := 39) (R := 40) (G := 41)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ (M ^ i) M (M ^ i) 0 ⟨by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41], by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41]⟩ ⟨by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41], by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41]⟩ ⟨by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41], by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41]⟩ ⟨by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41], by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41]⟩
    (by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41]) (by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41]) (by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41]) hMi hM (by omega))
  have c3 := WExec.seq c2 (RegRat.copyB_spec cap wd (ns := 8) (nr := 48) (A := 4) (B := 5) (F := 39) (R := 40) (by decide) (by decide) _ (M ^ i)
    (M ^ i * M) ⟨by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41], by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41]⟩ ⟨by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41], by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41]⟩ (by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41]) (by simp [Function.update_apply, fw, powSt, h1, h1h, h4h, h5h, h6, h6h, z39, z40, z41]) (by omega))
  refine WExec.cast cap c3 ?_ (by omega)
  clear c1 c2 c3
  unfold powSt
  apply WState.eq
  · simp
  · funext x
    simp only [WState.setv_st, WState.sets_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [fw, pow_succ]
  · funext r
    simp only [WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all <;> omega
  · simp

/-- **The power**: from `P = C = 1`, `2t` rounds leave `P = C = M^{2t}`, the counter back at `0`. -/
def powW : WM 8 48 := .seq (.seq (dupR 5 38 8) (dupR 5 38 8)) (.whr 38 powBody)

theorem pow_spec (h4 : σ.st 4 = fw wd 1) (h5 : σ.st 5 = fw wd 1) (ht : σ.val 5 = t) (z8 : σ.val 8 = 0)
    (z38 : σ.val 38 = 0) (hP : M ^ (2 * t) < 2 ^ wd) (hM : M < 2 ^ wd) (hcap : 2 * wd + 2 * t + 1 ≤ cap) :
    WExec cap powW σ ((σ.sets 4 (fw wd (M ^ (2 * t)))).sets 5 (fw wd (M ^ (2 * t))))
      (2 * t * (RegRat.mulCost wd + 41 * wd + 12) + 40 * t + 10) := by
  have c1 := BinW.dupR_spec cap 5 38 8 (by decide) (by decide) (by decide) σ t ht z38 z8 (by omega)
  have c2 := FsKit.addR_spec cap 5 38 8 (by decide) (by decide) (by decide) (σ.setv 38 t) t (by simp [ht])
    (by simp [z8]) (by simp; omega) (by omega)
  have e0 : (σ.setv 38 t).setv 38 ((σ.setv 38 t).val 38 + t) = powSt σ wd M t 0 := by
    unfold powSt
    apply WState.eq
    · simp
    · funext x
      simp only [WState.setv_st, WState.sets_st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [fw]
    · funext r
      simp only [WState.setv_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega
    · simp
  rw [e0] at c2
  have lp := PrimAsm.UnaryPow.flagLoop cap 38 powBody (RegRat.mulCost wd + 41 * wd + 10) (2 * t) (powSt σ wd M t)
    (fun k hk => by simp [powSt]; omega) (by simp [powSt])
    (fun k hk => powBody_spec cap σ wd M t h1 h1h h4h h5h h6 h6h z39 z40 z41 k hk
      (by
        rcases Nat.eq_zero_or_pos M with hM0 | hM0
        · subst hM0; simp
        · rw [← pow_succ]
          exact lt_of_le_of_lt (Nat.pow_le_pow_right hM0 (by omega)) hP)
      hM hcap)
  refine WExec.cast cap (WExec.seq (WExec.seq c1 c2) lp) ?_ ?_
  · unfold powSt
    apply WState.eq
    · simp
    · simp
    · funext r
      simp only [WState.setv_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · simp
  · nlinarith

end Pow

/-- **The product**: `X := J·P`, `X := X + M`, `C := Cw·X`, `C := C + 1`. -/
def prodW : WM 8 48 :=
  .seq (.seq (.seq (RegRat.mulB 2 4 7 6 39 40 41) (RegRat.addB 7 1 39 40)) (RegRat.mulB 3 7 5 6 39 40 41))
    (RegRat.incB 5 1 39 40)

theorem prod_spec (σ : WState 8 48) (wd M J c8 p c : ℕ) (h1 : σ.st 1 = fw wd M) (h1h : σ.sh 1 = 0)
    (h2 : σ.st 2 = fw wd J) (h2h : σ.sh 2 = 0) (h3 : σ.st 3 = fw wd c8) (h3h : σ.sh 3 = 0)
    (h4 : σ.st 4 = fw wd p) (h4h : σ.sh 4 = 0) (h5 : σ.st 5 = fw wd c) (h5h : σ.sh 5 = 0)
    (h6 : σ.st 6 = fw wd 0) (h6h : σ.sh 6 = 0) (h7 : σ.st 7 = fw wd 0) (h7h : σ.sh 7 = 0)
    (z39 : σ.val 39 = 0) (z40 : σ.val 40 = 0) (z41 : σ.val 41 = 0)
    (hb : c8 * (J * p + M) + 1 < 2 ^ wd) (hJ : J * p + M < 2 ^ wd) (hp : p < 2 ^ wd) (hM : M < 2 ^ wd)
    (hcap : 2 * wd + 1 ≤ cap) :
    WExec cap prodW σ ((σ.sets 7 (fw wd (J * p + M))).sets 5 (fw wd (c8 * (J * p + M) + 1)))
      (2 * RegRat.mulCost wd + 100 * wd + 20) := by
  have hJp : J * p < 2 ^ wd := lt_of_le_of_lt (Nat.le_add_right _ _) hJ
  have c1 := RegRat.mulB_spec cap wd (ns := 8) (nr := 48) (A := 2) (B := 4) (C := 7) (S := 6) (F := 39) (R := 40) (G := 41)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    σ J p 0 0 ⟨by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41], by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]⟩ ⟨by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41], by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]⟩ ⟨by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41], by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]⟩ ⟨by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41], by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]⟩
    (by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]) (by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]) (by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]) hJp hp (by omega)
  have c2 := WExec.seq c1 (RegRat.addB_spec cap wd (ns := 8) (nr := 48) (A := 7) (B := 1) (F := 39) (R := 40) (by decide) (by decide) _ (J * p) M
    ⟨by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41], by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]⟩ ⟨by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41], by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]⟩ (by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]) (by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]) hJ (by omega))
  have c3 := WExec.seq c2 (RegRat.mulB_spec cap wd (ns := 8) (nr := 48) (A := 3) (B := 7) (C := 5) (S := 6) (F := 39) (R := 40) (G := 41)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ c8 (J * p + M) c 0 ⟨by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41], by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]⟩ ⟨by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41], by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]⟩ ⟨by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41], by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]⟩ ⟨by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41], by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]⟩
    (by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]) (by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]) (by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]) (by omega) hJ (by omega))
  have c4 := WExec.seq c3 (RegRat.incB_spec cap wd (ns := 8) (nr := 48) (A := 5) (B := 1) (F := 39) (R := 40) (by decide) (by decide) _
    (c8 * (J * p + M)) M ⟨by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41], by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]⟩ ⟨by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41], by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]⟩ (by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]) (by simp [Function.update_apply, fw, h1, h1h, h2, h2h, h3, h3h, h4, h4h, h5, h5h, h6, h6h, h7, h7h, z39, z40, z41]) hb (by omega))
  refine WExec.cast cap c4 ?_ (by omega)
  clear c1 c2 c3 c4
  apply WState.eq
  · simp
  · funext x
    simp only [WState.setv_st, WState.sets_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [fw]
  · simp
  · simp

end NearCubicWires.WireExponent3_5.UnionMachine.EwPow
