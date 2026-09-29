import Proof.Wire_3_5.UnionMachine.EwPow

/-! # C6, e/W_j, part 7: `⌈log₂ V⌉` of a binary word, and the width bounds

From `C = V` (stream `5`) and `Q = 1` (stream `8`): `F := [Q < C]` (C1.2's `ltB`), then while `F`: `Q := 2Q` (`shlB`),
`e += 1`, `F := [Q < C]`; finally `e += 1`. The loop runs `⌈log₂ V⌉` rounds (`Nat.pow_lt_of_lt_clog`,
`Nat.le_pow_clog`), so register `6` ends at `⌈log₂ V⌉ + 1` (**`cl_spec`**). The width `wd = 2tM + M + J + K + A + 8`
bounds every word (**`e_bounds`**: `M, M^{2t}, J·M^{2t} + M < 2^{wd}`, `2(8KA(J·M^{2t} + M) + 1) ≤ 2^{wd}`).

Paper quantity: `e = ⌈log₂(8K·A(M + J·M^{2t}) + 1)⌉ + 1` (`Primitive.listE`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.EwClog
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.EwWords (fw)

variable (cap : ℕ)

/-! ## The width bounds -/

theorem powM_le (M t : ℕ) : M ^ (2 * t) ≤ 2 ^ (t * M) * 2 ^ (t * M) := by
  have h := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := M)).le (2 * t)
  calc M ^ (2 * t) ≤ (2 ^ M) ^ (2 * t) := h
    _ = 2 ^ (t * M) * 2 ^ (t * M) := by rw [← pow_mul, ← pow_add]; congr 1; ring

theorem wd_pow (M A K J t : ℕ) : 2 ^ EwBin.wdOf M A K J t =
    256 * (2 ^ (t * M) * 2 ^ (t * M) * 2 ^ M * 2 ^ J * 2 ^ K * 2 ^ A) := by
  unfold EwBin.wdOf
  simp only [pow_add]
  ring

/-- **The width bounds**: every word of the `e` computation fits in `wd` bits. -/
theorem e_bounds (M A K J t : ℕ) :
    M < 2 ^ EwBin.wdOf M A K J t ∧ M ^ (2 * t) < 2 ^ EwBin.wdOf M A K J t ∧
      J * M ^ (2 * t) + M < 2 ^ EwBin.wdOf M A K J t ∧
      2 * (8 * (K * A) * (J * M ^ (2 * t) + M) + 1) ≤ 2 ^ EwBin.wdOf M A K J t := by
  rw [wd_pow]
  have hP := powM_le M t
  have hM : M < 2 ^ M := Nat.lt_two_pow_self
  have hJ : J < 2 ^ J := Nat.lt_two_pow_self
  have hK : K < 2 ^ K := Nat.lt_two_pow_self
  have hA : A < 2 ^ A := Nat.lt_two_pow_self
  have ha1 : 1 ≤ 2 ^ (t * M) := Nat.one_le_two_pow
  generalize 2 ^ (t * M) = a at hP ha1 ⊢
  generalize 2 ^ M = bM at hM ⊢
  generalize 2 ^ J = bJ at hJ ⊢
  generalize 2 ^ K = bK at hK ⊢
  generalize 2 ^ A = bA at hA ⊢
  generalize M ^ (2 * t) = X at hP ⊢
  have haa : 1 ≤ a * a := Nat.mul_pos ha1 ha1
  have hU1 : 1 ≤ a * a * bJ := Nat.mul_pos haa (by omega)
  have hJX : J * X + a * a ≤ a * a * bJ := by
    have h1 : J * X ≤ J * (a * a) := Nat.mul_le_mul_left J hP
    have h2 : (J + 1) * (a * a) ≤ bJ * (a * a) := Nat.mul_le_mul_right (a * a) hJ
    have r1 : (J + 1) * (a * a) = J * (a * a) + a * a := by ring
    have r2 : bJ * (a * a) = a * a * bJ := by ring
    omega
  have hXU : X ≤ a * a * bJ := by
    have : a * a ≤ a * a * bJ := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hKA : K * A + 1 ≤ bK * bA := by
    have h1 : (K + 1) * (A + 1) ≤ bK * bA := Nat.mul_le_mul hK hA
    have r3 : (K + 1) * (A + 1) = K * A + K + A + 1 := by ring
    omega
  have e : a * a * bM * bJ * bK * bA = bM * (a * a * bJ) * (bK * bA) := by ring
  rw [e]
  generalize a * a * bJ = U at hU1 hJX hXU ⊢
  generalize bK * bA = V at hKA ⊢
  generalize K * A = KA at hKA ⊢
  have hbM1 : 1 ≤ bM := by omega
  have hV1 : 1 ≤ V := by omega
  have r4 : U + bM ≤ bM * U + 1 := by nlinarith
  have hY : J * X + M + 1 ≤ bM * U := by omega
  generalize J * X + M = Y at hY ⊢
  have hm : KA * Y ≤ V * (bM * U) := Nat.mul_le_mul (by omega) (by omega)
  have p1 : bM ≤ bM * U * V := by
    calc bM = bM * 1 * 1 := by ring
      _ ≤ bM * U * V := by gcongr
  have p2 : bM * U ≤ bM * U * V := by
    calc bM * U = bM * U * 1 := by ring
      _ ≤ bM * U * V := by gcongr
  have p3 : U ≤ bM * U := by
    calc U = 1 * U := by ring
      _ ≤ bM * U := by gcongr
  have r5 : V * (bM * U) = bM * U * V := by ring
  have r6 : 8 * KA * Y = 8 * (KA * Y) := by ring
  rw [r6]
  generalize bM * U * V = P at p1 p2 r5 ⊢
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem clog_le_wd (wd V : ℕ) (hV : 2 * V ≤ 2 ^ wd) : Nat.clog 2 V ≤ wd :=
  Nat.clog_le_of_le_pow (by omega)

/-! ## The loop -/

/-- One round: `F := 0`, `Q := 2Q`, `e += 1`, `F := [Q < C]`. -/
def clBody : WM 8 48 := .seq (.seq (.seq (.dec 39) (RegRat.shlB 8 1 39 40)) (.inc 6)) (RegRat.ltB 8 5 39 40)

/-- The state after `i` rounds. -/
def clSt (σ : WState 8 48) (wd V i : ℕ) : WState 8 48 :=
  ((σ.sets 8 (fw wd (2 ^ i))).setv 6 i).setv 39 (decide (2 ^ i < V)).toNat

section Cl
variable (σ : WState 8 48) (wd m V : ℕ) (h1 : σ.st 1 = fw wd m) (h1h : σ.sh 1 = 0) (h5 : σ.st 5 = fw wd V)
  (h5h : σ.sh 5 = 0) (h8h : σ.sh 8 = 0) (z40 : σ.val 40 = 0)
include h1 h1h h5 h5h h8h z40

theorem clBody_spec (i : ℕ) (hi : 2 ^ i < V) (hV : 2 * V ≤ 2 ^ wd) (hcap : 2 * wd + 1 ≤ cap) (hic : i + 1 < cap) :
    WExec cap clBody (clSt σ wd V i) (clSt σ wd V (i + 1)) (100 * wd + 20) := by
  have hp0 : 0 < 2 ^ i := Nat.two_pow_pos i
  have hw0 : 0 < 2 ^ wd := Nat.two_pow_pos wd
  have c1 := WExec.dec (cap := cap) 39 (clSt σ wd V i) (by simp [Function.update_apply, fw, clSt, h1, h1h, h5, h5h, h8h, z40, hi]; omega)
  have c2 := WExec.seq c1 (RegRat.shlB_spec cap wd (ns := 8) (nr := 48) (A := 8) (B := 1) (F := 39) (R := 40)
    (by decide) (by decide) _ (2 ^ i) m ⟨by simp [Function.update_apply, fw, clSt, h1, h1h, h5, h5h, h8h, z40, hi], by simp [Function.update_apply, fw, clSt, h1, h1h, h5, h5h, h8h, z40, hi]⟩ ⟨by simp [Function.update_apply, fw, clSt, h1, h1h, h5, h5h, h8h, z40, hi], by simp [Function.update_apply, fw, clSt, h1, h1h, h5, h5h, h8h, z40, hi]⟩ (by simp [Function.update_apply, fw, clSt, h1, h1h, h5, h5h, h8h, z40, hi]) (by simp [Function.update_apply, fw, clSt, h1, h1h, h5, h5h, h8h, z40, hi]) (by omega))
  have c3 := WExec.seq c2 (WExec.inc (cap := cap) 6 _ (by simp [Function.update_apply, fw, clSt, h1, h1h, h5, h5h, h8h, z40, hi]; omega))
  have c4 := WExec.seq c3 (RegRat.ltB_spec cap wd (ns := 8) (nr := 48) (A := 8) (B := 5) (F := 39) (R := 40)
    (by decide) (by decide) _ (2 * 2 ^ i) V ⟨by simp [Function.update_apply, fw, clSt, h1, h1h, h5, h5h, h8h, z40, hi], by simp [Function.update_apply, fw, clSt, h1, h1h, h5, h5h, h8h, z40, hi]⟩ ⟨by simp [Function.update_apply, fw, clSt, h1, h1h, h5, h5h, h8h, z40, hi], by simp [Function.update_apply, fw, clSt, h1, h1h, h5, h5h, h8h, z40, hi]⟩ (by simp [Function.update_apply, fw, clSt, h1, h1h, h5, h5h, h8h, z40, hi]) (by simp [Function.update_apply, fw, clSt, h1, h1h, h5, h5h, h8h, z40, hi])
    (by omega) (by omega) (by omega))
  refine WExec.cast cap c4 ?_ (by omega)
  clear c1 c2 c3 c4
  unfold clSt
  apply WState.eq
  · simp
  · funext x
    simp only [WState.setv_st, WState.sets_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [fw, pow_succ, Nat.mul_comm]
  · funext r
    simp only [WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [pow_succ, Nat.mul_comm]
  · simp

/-- **`e := ⌈log₂ V⌉ + 1`** (register `6`), `Q := 2^{⌈log₂ V⌉}`, the flag back at `0`. -/
def clW : WM 8 48 := .seq (.seq (RegRat.ltB 8 5 39 40) (.whr 39 clBody)) (.inc 6)

theorem cl_spec (h8 : σ.st 8 = fw wd 1) (z6 : σ.val 6 = 0) (z39 : σ.val 39 = 0) (hV : 2 * V ≤ 2 ^ wd)
    (hV1 : 1 ≤ V) (hcap : 2 * wd + 4 ≤ cap) :
    WExec cap clW σ ((σ.sets 8 (fw wd (2 ^ Nat.clog 2 V))).setv 6 (Nat.clog 2 V + 1))
      (wd * (100 * wd + 22) + 50 * wd + 20) := by
  have hcl := clog_le_wd wd V hV
  have hw0 : 0 < 2 ^ wd := Nat.two_pow_pos wd
  have c1 := RegRat.ltB_spec cap wd (ns := 8) (nr := 48) (A := 8) (B := 5) (F := 39) (R := 40) (by decide)
    (by decide) σ 1 V ⟨by simp [h8, fw], h8h⟩ ⟨h5, h5h⟩ z39 z40 (by omega) (by omega) (by omega)
  have e0 : σ.setv 39 (decide (1 < V)).toNat = clSt σ wd V 0 := by
    unfold clSt
    apply WState.eq
    · simp
    · funext x
      simp only [WState.setv_st, WState.sets_st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext r
      simp only [WState.setv_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · simp
  rw [e0] at c1
  have lp := PrimAsm.UnaryPow.flagLoop cap 39 clBody (100 * wd + 20) (Nat.clog 2 V) (clSt σ wd V)
    (fun k hk => by
      have := Nat.pow_lt_of_lt_clog hk
      simp [clSt, this])
    (by
      have := Nat.le_pow_clog (b := 2) (by norm_num) V
      simp [clSt]; omega)
    (fun k hk => clBody_spec cap σ wd m V h1 h1h h5 h5h h8h z40 k (Nat.pow_lt_of_lt_clog hk) hV (by omega)
      (by omega))
  have c3 := WExec.seq (WExec.seq c1 lp) (WExec.inc (cap := cap) 6 (clSt σ wd V (Nat.clog 2 V))
    (by simp [clSt]; omega))
  refine WExec.cast cap c3 ?_ ?_
  · unfold clSt
    apply WState.eq
    · simp
    · simp
    · funext r
      have hs := Nat.le_pow_clog (b := 2) (by norm_num) V
      simp only [WState.setv_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega
    · simp
  · have := Nat.mul_le_mul_right (100 * wd + 20 + 2) hcl
    nlinarith

end Cl

end NearCubicWires.WireExponent3_5.UnionMachine.EwClog
