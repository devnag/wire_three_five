import Proof.Wire_3_5.Primitive.SeedFix.C4KWf

/-! # C4KW, part 7: the stage B3 (the elimination's modulus word)

The kept word `71` is `frame (binary ℓ₀ p)` (`p` the field's modulus `refMod`, `kw_mod`). B3 (streams: `0` the output,
`1` the input `1^{ℓ₀}`, `2` the input `1^p`; registers `ℓ`, the current value, a half, a parity) counts both inputs,
then `ℓ₀` times halves the value, emitting its parity framed twice; then the terminators.

* `cntW`, **`cnt_loop`** (count a unary word into a register), `togW`, **`tog_loop`** (halve by a parity toggle);
* `b3Body`, **`b3_loop`**: the output `prs (prs (binary k v))`;
* **`b3_run`**, **`partB3 : PartB3`**.

Paper quantity of the main type: the elimination's field modulus word `frame (binary ℓ₀ p)` (P3:2268-2269). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.C4Hk (apd apd_nil apd_apd apd_seth apd_sh_d apd_st_d apd_st_ne apd_sh_ne
  wlist wlist_spec)

section Loops
variable {ns nr : ℕ} (cap : ℕ)

/-- Count the ones of `S` into the register `r`. -/
def cntW (S : Fin (ns + 1)) (r : Fin nr) : WM ns nr := .whs S (.seq (.inc r) (.fwd S))

theorem cnt_loop (S : Fin (ns + 1)) (r : Fin nr) (c : List Bool) (hi : ℕ)
    (hT : ∀ q, q < hi → readTapeBit c q = true) (hF : readTapeBit c hi = false) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.st S = c → σ.sh S + k = hi → σ.val r + k ≤ cap →
      WExec cap (cntW S r) σ ((σ.seth S hi).setv r (σ.val r + k)) (7 * k + 1)
  | 0, σ, hc, hk, _ => by
    have e : (σ.seth S hi).setv r (σ.val r + 0) = σ := by
      apply WState.eq
      · funext j; by_cases hj : j = S
        · subst hj; simp [WState.seth, WState.setv]; omega
        · simp [WState.seth, WState.setv, hj]
      · rfl
      · funext j; by_cases hj : j = r
        · subst hj; simp [WState.seth, WState.setv]
        · simp [WState.seth, WState.setv, hj]
      · rfl
    show WExec cap (cntW S r) σ ((σ.seth S hi).setv r (σ.val r + 0)) (7 * 0 + 1)
    rw [e]
    exact WExec.whsF (by show readTapeBit _ _ = false; rw [hc, show σ.sh S = hi by omega]; exact hF)
  | k + 1, σ, hc, hk, hcap => by
    have hb : wbit σ S = true := by show readTapeBit _ _ = true; rw [hc]; exact hT _ (by omega)
    have t1 := WExec.inc (cap := cap) r σ (by omega)
    have t2 := WExec.fwd (cap := cap) S (σ.setv r (σ.val r + 1))
    have ih := cnt_loop S r c hi hT hF k ((σ.setv r (σ.val r + 1)).seth S ((σ.setv r (σ.val r + 1)).sh S + 1))
      (by simp [hc]) (by simp; omega) (by simp; omega)
    have e : (((σ.setv r (σ.val r + 1)).seth S ((σ.setv r (σ.val r + 1)).sh S + 1)).seth S hi).setv r
        (((σ.setv r (σ.val r + 1)).seth S ((σ.setv r (σ.val r + 1)).sh S + 1)).val r + k) =
        (σ.seth S hi).setv r (σ.val r + (k + 1)) := by
      apply WState.eq
      · funext j; by_cases hj : j = S
        · subst hj; simp [WState.seth, WState.setv]
        · simp [WState.seth, WState.setv, hj]
      · rfl
      · funext j; by_cases hj : j = r
        · subst hj; simp [WState.seth, WState.setv]; omega
        · simp [WState.seth, WState.setv, hj]
      · rfl
    rw [e] at ih
    exact WExec.cast cap (WExec.whsT hb (WExec.seq t1 t2) ih) rfl (by omega)

/-- Halve register `1` into register `2`, its parity toggled in register `3`. -/
def togW : WM ns 4 := .whr 1 (.seq (.dec 1) (.ifr 3 (.seq (.dec 3) (.inc 2)) (.inc 3)))

theorem tog_loop : ∀ (m : ℕ) (σ : WState ns 4), σ.val 1 = m → σ.val 3 ≤ 1 → σ.val 2 + σ.val 3 + m + 1 ≤ cap →
    WExec cap togW σ (((σ.setv 1 0).setv 2 (σ.val 2 + (σ.val 3 + m) / 2)).setv 3 ((σ.val 3 + m) % 2)) (10 * m + 1)
  | 0, σ, h1, h3, _ => by
    have e : ((σ.setv 1 0).setv 2 (σ.val 2 + (σ.val 3 + 0) / 2)).setv 3 ((σ.val 3 + 0) % 2) = σ := by
      apply WState.eq
      · rfl
      · rfl
      · funext r; fin_cases r <;> simp [WState.setv] <;> omega
      · rfl
    rw [e]
    exact WExec.whrF h1
  | m + 1, σ, h1, h3, hc => by
    have t1 := WExec.dec (cap := cap) (1 : Fin 4) σ (by omega)
    set σ1 := σ.setv 1 (σ.val 1 - 1) with hσ1
    have v1 : σ1.val 1 = m := by rw [hσ1]; simp [WState.setv, h1]
    by_cases hb : σ.val 3 = 1
    · have d3 := WExec.dec (cap := cap) (3 : Fin 4) σ1 (by rw [hσ1]; simp [WState.setv]; omega)
      have i2 := WExec.inc (cap := cap) (2 : Fin 4) (σ1.setv 3 (σ1.val 3 - 1)) (by simp [hσ1, WState.setv]; omega)
      set σ2 := (σ1.setv 3 (σ1.val 3 - 1)).setv 2 ((σ1.setv 3 (σ1.val 3 - 1)).val 2 + 1) with hσ2
      have ih := tog_loop m σ2 (by rw [hσ2]; simp [WState.setv, v1]) (by rw [hσ2]; simp [WState.setv, hσ1]; omega)
        (by rw [hσ2]; simp [WState.setv, hσ1]; omega)
      have e : ((σ2.setv 1 0).setv 2 (σ2.val 2 + (σ2.val 3 + m) / 2)).setv 3 ((σ2.val 3 + m) % 2) =
          ((σ.setv 1 0).setv 2 (σ.val 2 + (σ.val 3 + (m + 1)) / 2)).setv 3 ((σ.val 3 + (m + 1)) % 2) := by
        apply WState.eq
        · rfl
        · rfl
        · funext r; fin_cases r <;> simp [WState.setv, hσ2, hσ1, hb] <;> omega
        · rfl
      rw [e] at ih
      have tb : WExec cap (.ifr 3 (.seq (.dec 3) (.inc 2)) (.inc 3) : WM ns 4) σ1 σ2 6 :=
        WExec.cast cap (WExec.ifrT (by rw [hσ1]; simp [WState.setv]; omega) (WExec.seq d3 i2)) rfl (by omega)
      exact WExec.cast cap (WExec.whrT (by omega) (WExec.seq t1 tb) ih) rfl (by omega)
    · have h30 : σ.val 3 = 0 := by omega
      have i3 := WExec.inc (cap := cap) (3 : Fin 4) σ1 (by rw [hσ1]; simp [WState.setv]; omega)
      set σ2 := σ1.setv 3 (σ1.val 3 + 1) with hσ2
      have ih := tog_loop m σ2 (by rw [hσ2]; simp [WState.setv, v1]) (by rw [hσ2]; simp [WState.setv, hσ1, h30])
        (by rw [hσ2]; simp [WState.setv, hσ1]; omega)
      have e : ((σ2.setv 1 0).setv 2 (σ2.val 2 + (σ2.val 3 + m) / 2)).setv 3 ((σ2.val 3 + m) % 2) =
          ((σ.setv 1 0).setv 2 (σ.val 2 + (σ.val 3 + (m + 1)) / 2)).setv 3 ((σ.val 3 + (m + 1)) % 2) := by
        apply WState.eq
        · rfl
        · rfl
        · funext r; fin_cases r <;> simp [WState.setv, hσ2, hσ1, h30] <;> omega
        · rfl
      rw [e] at ih
      have tb : WExec cap (.ifr 3 (.seq (.dec 3) (.inc 2)) (.inc 3) : WM ns 4) σ1 σ2 4 :=
        WExec.cast cap (WExec.ifrF (by rw [hσ1]; simp [WState.setv]; omega) i3) rfl (by omega)
      exact WExec.cast cap (WExec.whrT (by omega) (WExec.seq t1 tb) ih) rfl (by omega)

end Loops

/-! ## The modulus word -/

theorem apd_setv {ns nr : ℕ} (τ : WState ns nr) (r : Fin nr) (x : ℕ) (d : Fin (ns + 1)) (y : List Bool) :
    apd (τ.setv r x) d y = (apd τ d y).setv r x := rfl

/-- One bit: halve the value, emit its parity framed twice, clear the parity. -/
def b3Body : WM 2 4 :=
  .seq (.dec 0) (.seq togW (.seq (WM.move 2 1) (.seq (wlist 0 [true, true, true])
    (.seq (.ifr 3 (wlist 0 [true]) (wlist 0 [false])) (.ifr 3 (.dec 3) .skip)))))

theorem b3_loop (cap : ℕ) : ∀ (k v : ℕ) (σ : WState 2 4), σ.val 0 = k → σ.val 1 = v → σ.val 2 = 0 → σ.val 3 = 0 →
    σ.sh 0 = (σ.st 0).length → v + 2 ≤ cap → k ≤ cap →
    WExec cap (.whr 0 b3Body) σ (((apd σ 0 (prs (prs (SignedSortKey.binary k v)))).setv 0 0).setv 1 (v / 2 ^ k))
      (k * (20 * v + 60) + 1)
  | 0, v, σ, h0, h1, _, _, hO, _, _ => by
    have e : ((apd σ 0 (prs (prs (SignedSortKey.binary 0 v)))).setv 0 0).setv 1 (v / 2 ^ 0) = σ := by
      have : SignedSortKey.binary 0 v = [] := rfl
      rw [this, show prs (prs []) = [] from rfl, apd_nil σ 0 hO]
      apply WState.eq
      · rfl
      · rfl
      · funext r; fin_cases r <;> simp [WState.setv, h0, h1]
      · rfl
    rw [e]
    exact WExec.cast cap (WExec.whrF h0) rfl (by omega)
  | k + 1, v, σ, h0, h1, h2, h3, hO, hv, hk => by
    have t1 := WExec.dec (cap := cap) (0 : Fin 4) σ (by omega)
    set σ1 := σ.setv 0 (σ.val 0 - 1) with hσ1
    have t2 := tog_loop cap v σ1 (by rw [hσ1]; simp [WState.setv, h1]) (by rw [hσ1]; simp [WState.setv, h3])
      (by rw [hσ1]; simp [WState.setv, h2, h3]; omega)
    set σ2 := ((σ1.setv 1 0).setv 2 (σ1.val 2 + (σ1.val 3 + v) / 2)).setv 3 ((σ1.val 3 + v) % 2) with hσ2
    have v22 : σ2.val 2 = v / 2 := by rw [hσ2]; simp [WState.setv, hσ1, h2, h3]
    have v21 : σ2.val 1 = 0 := by rw [hσ2]; simp [WState.setv]
    have t3 := wmove_spec cap (2 : Fin 4) (1 : Fin 4) (by decide) (v / 2) σ2 v22 (by rw [v22]; omega)
      (by rw [v21, v22]; omega)
    set σ3 := (σ2.setv 2 0).setv 1 (σ2.val 1 + σ2.val 2) with hσ3
    have hO3 : σ3.sh 0 = (σ3.st 0).length := by
      rw [hσ3, hσ2, hσ1]; simp only [WState.setv]; exact hO
    have t4 := wlist_spec cap (0 : Fin 3) [true, true, true] σ3 hO3
    set σ4 := apd σ3 0 [true, true, true] with hσ4
    have v43 : σ4.val 3 = v % 2 := by rw [hσ4, hσ3, hσ2]; simp [apd, WState.setv, hσ1, h3]
    have hO4 : σ4.sh 0 = (σ4.st 0).length := by rw [hσ4, apd_sh_d, apd_st_d, List.length_append]
    set b := (v % 2 == 1) with hb
    have t5 : WExec cap (.ifr 3 (wlist 0 [true]) (wlist 0 [false]) : WM 2 4) σ4 (apd σ4 0 [b]) 5 := by
      rcases Nat.mod_two_eq_zero_or_one v with hm | hm
      · have : b = false := by rw [hb, hm]; rfl
        rw [this]
        exact WExec.cast cap (WExec.ifrF (by rw [v43, hm]) (wlist_spec cap 0 [false] σ4 hO4)) rfl (by simp)
      · have : b = true := by rw [hb, hm]; rfl
        rw [this]
        exact WExec.cast cap (WExec.ifrT (by rw [v43, hm]; omega) (wlist_spec cap 0 [true] σ4 hO4)) rfl (by simp)
    set σ5 := apd σ4 0 [b] with hσ5
    have v53 : σ5.val 3 = v % 2 := by rw [hσ5]; exact v43
    have t6 : WExec cap (.ifr 3 (.dec 3) .skip : WM 2 4) σ5 (σ5.setv 3 0) 2 := by
      rcases Nat.mod_two_eq_zero_or_one v with hm | hm
      · rw [show σ5.setv 3 0 = σ5 by rw [← hm, ← v53, wsetv_same]]
        exact WExec.cast cap (WExec.ifrF (by rw [v53, hm]) (WExec.skip _)) rfl (by omega)
      · have t := WExec.dec (cap := cap) (3 : Fin 4) σ5 (by rw [v53, hm]; omega)
        rw [v53, hm] at t
        exact WExec.cast cap (WExec.ifrT (by rw [v53, hm]; omega) t) rfl (by omega)
    set σ' := ((apd σ 0 [true, true, true, b]).setv 0 k).setv 1 (v / 2) with hσ'
    have e6 : σ5.setv 3 0 = σ' := by
      rw [hσ5, hσ4, hσ3, hσ2, hσ1, hσ']
      apply WState.eq
      · funext j; by_cases hj : j = 0
        · subst hj; (simp [apd, WState.setv]) <;> omega
        · simp [apd, WState.setv, hj]
      · funext j; by_cases hj : j = 0
        · subst hj; simp [apd, WState.setv]
        · simp [apd, WState.setv, hj]
      · funext r; fin_cases r <;> simp [apd, WState.setv, h0, h2, h3]
      · rfl
    rw [e6] at t6
    have ih := b3_loop cap k (v / 2) σ' (by rw [hσ']; simp [WState.setv]) (by rw [hσ']; simp [WState.setv])
      (by rw [hσ']; simp [apd, WState.setv, h2]) (by rw [hσ']; simp [apd, WState.setv, h3])
      (by rw [hσ']; show (apd σ 0 [true, true, true, b]).sh 0 = ((apd σ 0 [true, true, true, b]).st 0).length
          rw [apd_sh_d, apd_st_d, List.length_append])
      (by omega) (by omega)
    have eF : ((apd σ' 0 (prs (prs (SignedSortKey.binary k (v / 2))))).setv 0 0).setv 1 (v / 2 / 2 ^ k) =
        ((apd σ 0 (prs (prs (SignedSortKey.binary (k + 1) v)))).setv 0 0).setv 1 (v / 2 ^ (k + 1)) := by
      have hbin : prs (prs (SignedSortKey.binary (k + 1) v)) = [true, true, true, b] ++
          prs (prs (SignedSortKey.binary k (v / 2))) := rfl
      rw [hσ', apd_setv, apd_setv, apd_apd, hbin, Nat.div_div_eq_div_mul, ← pow_succ']
      apply WState.eq
      · rfl
      · rfl
      · funext r; fin_cases r <;> simp [WState.setv]
      · rfl
    rw [eF] at ih
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 (WExec.seq t4
      (WExec.seq t5 t6))))) ih) rfl ?_
    have hdiv : v / 2 ≤ v := Nat.div_le_self v 2
    have hm1 : k * (20 * (v / 2) + 60) ≤ k * (20 * v + 60) := Nat.mul_le_mul_left _ (by omega)
    simp only [List.length_cons, List.length_nil]
    nlinarith

end NearCubicWires.WireExponent3_5.PrimT.C4KW
