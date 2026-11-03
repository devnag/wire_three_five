import Proof.Wire_3_5.UnionMachine.NumsA6Base
import Proof.Wire_3_5.UnionMachine.NumsC2

/-! # NW phase (a), part 7: the data stage's width from the input

PA's data stage (`dataDock`) needs `1^n`, `1^L`, `1^W` with `L, W` above every code of the request and the unary counts
(`hL`, `hLX`, `hcx`, `hcy`, `hcu`). Phase (a) takes `L = W = 3|fpIn| + 8(n+1)^{26} + 16`: the codes are words inside
`fpIn`, `n ≤ |fpIn|`, the circuits' descriptions and the carriers' gates are `≤ (n+1)^{26}` (the call's envelope).

* `addK`, **`addK_spec`** (`v += k·p`), `R26`, `wOf`, `widthW`, **`width_run`** (`g 2 := W`, every other register as at
  entry, the input's head back at `0`).

Paper quantity: none (plumbing: the data stage's register fill). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g powN powN_spec)

section Kit
variable {ns nr : ℕ} (cap : ℕ)

/-- `v += k·p` (`p` kept, `t` scratch). -/
def addK (p v t : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | k + 1 => .seq (ParseNat.addTo p v t) (addK p v t k)

theorem addK_spec (p v t : Fin nr) (hpv : p ≠ v) (hpt : p ≠ t) (hvt : v ≠ t) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val t = 0 → σ.val p ≤ cap → σ.val v + k * σ.val p ≤ cap →
      WExec cap (addK p v t k) σ (σ.setv v (σ.val v + k * σ.val p)) (k * (18 * σ.val p + 4))
  | 0, σ, _, _, _ => by
    rw [Nat.zero_mul, Nat.add_zero, wsetv_same, Nat.zero_mul]
    exact WExec.skip σ
  | k + 1, σ, ht, hp, hv => by
    have h1 := ParseNat.addTo_spec cap p v t hpv hpt hvt σ ht hp (by nlinarith)
    have e1 : (σ.setv v (σ.val v + σ.val p)).val t = 0 := by
      simp only [WState.setv_val, Function.update_of_ne (Ne.symm hvt), ht]
    have e2 : (σ.setv v (σ.val v + σ.val p)).val p = σ.val p := by
      simp only [WState.setv_val, Function.update_of_ne hpv]
    have e3 : (σ.setv v (σ.val v + σ.val p)).val v = σ.val v + σ.val p := by
      simp only [WState.setv_val, Function.update_self]
    have h2 := addK_spec p v t hpv hpt hvt k (σ.setv v (σ.val v + σ.val p)) e1 (by rw [e2]; exact hp)
      (by rw [e2, e3]; nlinarith)
    rw [e2, e3] at h2
    refine WExec.cast cap (WExec.seq h1 h2) ?_ ?_
    · rw [wsetv_setv]
      congr 1
      ring
    · have : (k + 1) * (18 * σ.val p + 4) = 18 * σ.val p + 4 + k * (18 * σ.val p + 4) := by ring
      omega

end Kit

/-- `powN`'s registers for `(n+1)^{26}`: `(g 4, g 3, g 5, g 6, g 7, g 8)`. -/
def R26 : Fin 6 ↪ Fin LNR := ⟨![g 4, g 3, g 5, g 6, g 7, g 8], by decide⟩

/-- **The data stage's width** `W = 3F + 8(n+1)^{26} + 16`. -/
def wOf (F n : ℕ) : ℕ := 3 * F + 8 * (n + 1) ^ 26 + 16

/-- **The width program**: `g 2 := W` from the framed input on `sIn` and `n` in `rN`. -/
def widthW (x : ℕ) : WM (LNS x) LNR :=
  .seq (frameLenW (sIn x) (g 0) (g 1)) (.seq (addK (g 0) (g 2) (g 1) 3) (.seq (WM.clear (g 0))
    (.seq (FinalPass.Hash4.wcopyR rN (g 3) (g 1)) (.seq (.inc (g 3)) (.seq (.inc (g 4))
    (.seq (powN R26 26) (.seq (addK (g 4) (g 2) (g 1) 8) (.seq (incK (g 2) 16)
    (.seq (WM.clear (g 3)) (WM.clear (g 4)))))))))))

theorem width_run (x cap : ℕ) (w : List Bool) (n : ℕ) (σ : St x) (hin : σ.st (sIn x) = frame w)
    (hh : σ.sh (sIn x) = 0) (hN : σ.val rN = n) (hg : ∀ j, σ.val (g j) = 0)
    (hc : wOf w.length n + 2 * w.length + n + 2 ≤ cap) :
    ∃ c, WExec cap (widthW x) σ (σ.setv (g 2) (wOf w.length n)) c ∧ c ≤ 4000 * (w.length + n + 2) ^ 27 := by
  obtain ⟨F, hF⟩ : ∃ v, v = w.length := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ v, v = (n + 1) ^ 26 := ⟨_, rfl⟩
  rw [← hF] at hc ⊢
  have hWd : wOf F n = 3 * F + 8 * P + 16 := by rw [hP]; rfl
  rw [hWd] at hc ⊢
  have n01 : g 0 ≠ g 1 := by decide
  have n02 : g 0 ≠ g 2 := by decide
  have n03 : g 0 ≠ g 3 := by decide
  have n04 : g 0 ≠ g 4 := by decide
  have n12 : g 1 ≠ g 2 := by decide
  have n13 : g 1 ≠ g 3 := by decide
  have n14 : g 1 ≠ g 4 := by decide
  have n23 : g 2 ≠ g 3 := by decide
  have n24 : g 2 ≠ g 4 := by decide
  have n34 : g 3 ≠ g 4 := by decide
  have nN3 : rN ≠ g 3 := by decide
  have nN1 : rN ≠ g 1 := by decide
  have hP1 : 1 ≤ P := by rw [hP]; exact Nat.one_le_pow _ _ (by omega)
  -- 1: `g 0 := F`
  have e1 := frameLen_spec cap (sIn x) (g 0) (g 1) n01 w σ hin hh (hg 0) (hg 1) (by omega)
  rw [← hF] at e1
  -- 2: `g 2 := 3F`
  have e2 := addK_spec cap (g 0) (g 2) (g 1) n02 n01 n12.symm 3 (σ.setv (g 0) F)
    (by simp [Function.update_of_ne n01.symm, hg]) (by simp; omega) (by simp [Function.update_of_ne n02.symm, hg]; omega)
  simp only [WState.setv_val, Function.update_self, Function.update_of_ne n02.symm, hg, Nat.zero_add] at e2
  -- 3: `g 0 := 0`
  have e3 := wclear_spec cap (g 0) F ((σ.setv (g 0) F).setv (g 2) (3 * F))
    (by simp [Function.update_of_ne n02]) (by simp [Function.update_of_ne n02]; omega)
  -- 4: `g 3 := n`
  have e4 := FinalPass.Hash4.wcopyR_spec cap rN (g 3) (g 1) nN3 nN1 n13.symm
    (((σ.setv (g 0) F).setv (g 2) (3 * F)).setv (g 0) 0)
    (by simp [Function.update_of_ne n03.symm, Function.update_of_ne n23.symm, hg])
    (by simp [Function.update_of_ne n01.symm, Function.update_of_ne n12, hg])
    (by simp [Function.update_of_ne (show rN ≠ g 0 by decide), Function.update_of_ne (show rN ≠ g 2 by decide), hN];
        omega)
  have v4 : (((σ.setv (g 0) F).setv (g 2) (3 * F)).setv (g 0) 0).val rN = n := by
    simp [Function.update_of_ne (show rN ≠ g 0 by decide), Function.update_of_ne (show rN ≠ g 2 by decide), hN]
  rw [v4] at e4
  -- 5, 6: `g 3 := n + 1`, `g 4 := 1`
  have e5 := WExec.inc (cap := cap) (g 3) ((((σ.setv (g 0) F).setv (g 2) (3 * F)).setv (g 0) 0).setv (g 3) n)
    (by simp; omega)
  simp only [WState.setv_val, Function.update_self] at e5
  have e6 := WExec.inc (cap := cap) (g 4)
    (((((σ.setv (g 0) F).setv (g 2) (3 * F)).setv (g 0) 0).setv (g 3) n).setv (g 3) (n + 1))
    (by simp [Function.update_of_ne n34.symm, Function.update_of_ne n24.symm, Function.update_of_ne n04.symm, hg];
        omega)
  simp only [WState.setv_val, Function.update_of_ne n34.symm, Function.update_of_ne n24.symm,
    Function.update_of_ne n04.symm, hg, Nat.zero_add] at e6
  -- 7: `g 4 := (n+1)^26`
  obtain ⟨σ6, h6⟩ : ∃ s, s = ((((((σ.setv (g 0) F).setv (g 2) (3 * F)).setv (g 0) 0).setv (g 3) n).setv (g 3)
      (n + 1)).setv (g 4) 1) := ⟨_, rfl⟩
  rw [← h6] at e6
  have r0 : R26 0 = g 4 := rfl
  have r1 : R26 1 = g 3 := rfl
  have v6 : ∀ j : Fin 10, j ≠ 0 → j ≠ 2 → j ≠ 3 → j ≠ 4 → σ6.val (g j) = 0 := by
    intro j a0 a2 a3 a4
    have m0 : g j ≠ g 0 := fun e => a0 (Fin.ext (by have := congrArg Fin.val e; simp [g] at this; omega))
    have m2 : g j ≠ g 2 := fun e => a2 (Fin.ext (by have := congrArg Fin.val e; simp [g] at this; omega))
    have m3 : g j ≠ g 3 := fun e => a3 (Fin.ext (by have := congrArg Fin.val e; simp [g] at this; omega))
    have m4 : g j ≠ g 4 := fun e => a4 (Fin.ext (by have := congrArg Fin.val e; simp [g] at this; omega))
    rw [h6]
    simp [Function.update_of_ne m0, Function.update_of_ne m2, Function.update_of_ne m3, Function.update_of_ne m4, hg]
  have v63 : σ6.val (g 3) = n + 1 := by rw [h6]; simp [Function.update_of_ne n34]
  have v64 : σ6.val (g 4) = 1 := by rw [h6]; simp
  obtain ⟨c7, e7, hc7⟩ := powN_spec cap R26 P (by omega) 26 σ6 (v6 5 (by decide) (by decide) (by decide) (by decide))
    (v6 6 (by decide) (by decide) (by decide) (by decide)) (v6 7 (by decide) (by decide) (by decide) (by decide))
    (v6 8 (by decide) (by decide) (by decide) (by decide)) (by rw [r1, v63]; omega)
    (fun j hj => by
      rw [r0, r1, v64, v63, Nat.one_mul, hP]
      exact Nat.pow_le_pow_right (by omega) hj)
  rw [r0, r1, v64, v63, Nat.one_mul, ← hP] at e7
  rw [r1, v63] at hc7
  -- 8: `g 2 := 3F + 8P`
  have v72 : (σ6.setv (g 4) P).val (g 2) = 3 * F := by
    rw [h6]; simp [Function.update_of_ne n24, Function.update_of_ne n23, Function.update_of_ne n02.symm]
  have v71 : (σ6.setv (g 4) P).val (g 1) = 0 := by
    rw [h6]; simp [Function.update_of_ne n14, Function.update_of_ne n13, Function.update_of_ne n12,
      Function.update_of_ne n01.symm, hg]
  have e8 := addK_spec cap (g 4) (g 2) (g 1) n24.symm n14.symm n12.symm 8 (σ6.setv (g 4) P) v71
    (by simp; omega) (by rw [v72]; simp; omega)
  rw [v72] at e8
  simp only [WState.setv_val, Function.update_self] at e8
  -- 9: `g 2 := W`
  have e9 := incK_spec cap (g 2) 16 ((σ6.setv (g 4) P).setv (g 2) (3 * F + 8 * P)) (by simp; omega)
  simp only [WState.setv_val, Function.update_self] at e9
  -- 10, 11: clear `g 3`, `g 4`
  have e10 := wclear_spec cap (g 3) (n + 1)
    ((((σ6.setv (g 4) P).setv (g 2) (3 * F + 8 * P))).setv (g 2) (3 * F + 8 * P + 16))
    (by simp [Function.update_of_ne n23.symm, Function.update_of_ne n34, v63])
    (by simp [Function.update_of_ne n23.symm, Function.update_of_ne n34, v63]; omega)
  have e11 := wclear_spec cap (g 4) P
    (((((σ6.setv (g 4) P).setv (g 2) (3 * F + 8 * P))).setv (g 2) (3 * F + 8 * P + 16)).setv (g 3) 0)
    (by simp [Function.update_of_ne n24.symm, Function.update_of_ne n34.symm])
    (by simp [Function.update_of_ne n24.symm, Function.update_of_ne n34.symm]; omega)
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 e11)))))))))) ?_ le_rfl, ?_⟩
  · rw [h6]
    apply WState.eq
    · simp only [WState.setv_sh]
    · simp only [WState.setv_st]
    · funext q
      simp only [WState.setv_val, Function.update_apply]
      by_cases a4 : q = g 4
      · subst a4; simp [n24.symm, hg]
      · by_cases a3 : q = g 3
        · subst a3; simp [n23.symm, n34, hg]
        · by_cases a2 : q = g 2
          · subst a2; simp [n24, n23]
          · by_cases a0 : q = g 0
            · subst a0; simp [n02, n03, n04, hg]
            · simp [a0, a2, a3, a4]
    · simp only [WState.setv_cell]
  · obtain ⟨Y, hYd⟩ : ∃ v, v = F + n + 2 := ⟨_, rfl⟩
    rw [← hYd]
    have hY2 : 2 ≤ Y := by omega
    have hPY : P + 1 ≤ Y ^ 26 := by
      rw [hP]
      calc (n + 1) ^ 26 + 1 ≤ (n + 2) ^ 26 := PrimAsm.CallIndex.succ_le_N26 n
        _ ≤ Y ^ 26 := Nat.pow_le_pow_left (by omega) 26
    have hY26 : Y ≤ Y ^ 26 := by
      calc Y = Y ^ 1 := (pow_one Y).symm
        _ ≤ Y ^ 26 := Nat.pow_le_pow_right (by omega) (by omega)
    have hZ : (P + 1) * (n + 1 + 1) ≤ Y ^ 27 := by
      rw [pow_succ]; exact Nat.mul_le_mul hPY (by omega)
    have h2627 : Y ^ 26 ≤ Y ^ 27 := Nat.pow_le_pow_right (by omega) (by omega)
    have e60 : 26 * (60 * (P + 1) * (n + 1 + 1) + 1) = 1560 * ((P + 1) * (n + 1 + 1)) + 26 := by ring
    have hmul : 8 * (18 * P + 4) = 144 * P + 32 := by ring
    have hmul3 : 3 * (18 * F + 4) = 54 * F + 12 := by ring
    rw [e60] at hc7
    omega

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
