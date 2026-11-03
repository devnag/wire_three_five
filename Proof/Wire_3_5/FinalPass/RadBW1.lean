import Proof.Wire_3_5.Primitive.Writers.WriteNat
import Proof.Wire_3_5.UnionMachine.RadSpecBase

/-! # RADIX stage 5b, part 1: the block writer's register kit (row:radix, P3:2585-2623)

The RADIX block writer (`RadSpec2.RadBlockW2`) appends one factor block
`marks (true :: blockC D L t sgn false labs) = blockE (4L) d (labSum labs) labs (lw.flatMap m2) t sgn c false`
(`PopRec.blockE_eq`). This module holds its register maps and the pieces before the labels:

* `fF`, `fL`: the FILTER bank's and the label writer's registers inside the block writer's 64 (output counter `7`);
* `quarter`, `subLp`, `add4`: `K += A/4`, `K -= B`, `v += 4p` (**`quarter_spec`**, **`subLp_spec`**, **`add4_spec`**);
* `phA`/**`phA_spec`**: `pieceA (4L) d` (PA's `FiltRecW.phaseA` at `Lp = 4L`);
* `kComp`/**`kComp_spec`**: the table word's length `|lw| = capC/4 − L − 1` from `capC = 4(|lw| + L + 1)`.

Paper quantity of the main types: the RADIX row's factor block's fields (row:radix, P3:2585-2623). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.RadB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Register maps -/

/-- The FILTER bank's registers inside the block writer's: `0 ↦ 7` (output counter), `13 ↦ 8` (`4L`), `14 ↦ 5`
(`d`), `19 ↦ 9`, `9 ↦ 10` (scratch), the rest unused by `phaseA`. -/
def fF : Fin 20 ↪ Fin 64 :=
  ⟨![7, 22, 23, 24, 25, 26, 27, 28, 29, 10, 30, 31, 32, 8, 5, 33, 34, 35, 36, 9], by decide⟩

/-- The label writer's registers (`Emit.LReg`): `0 ↦ 7`, `1 ↦ 11` (`4·row`), `2 ↦ 1` (`G`), `6 ↦ 15` (`gi`),
`11 ↦ 20` (the label log), the rest scratch. -/
def fL : Fin 13 ↪ Fin 64 := ⟨![7, 11, 1, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21], by decide⟩

theorem setv_eq_self (σ : WState ns nr) (r : Fin nr) (x : ℕ) (h : σ.val r = x) : σ.setv r x = σ := by
  rw [← h, wsetv_same]

/-! ## Unary steps -/

theorem dec_setv (r : Fin nr) (σ : WState ns nr) (x y : ℕ) (hxy : y = x + 1) (hc : y ≤ cap) :
    WExec cap (.dec r) (σ.setv r y) (σ.setv r x) 1 :=
  WExec.cast cap (WExec.dec (cap := cap) r _ (by rw [wsetv_val_self]; exact hc))
    (by rw [wsetv_val_self, wsetv_setv, hxy, Nat.add_sub_cancel]) le_rfl

theorem inc_to (r : Fin nr) (σ : WState ns nr) (x : ℕ) (hx : σ.val r = x) (hc : x < cap) :
    WExec cap (.inc r) σ (σ.setv r (x + 1)) 3 :=
  WExec.cast cap (WExec.inc (cap := cap) r σ (by omega)) (by rw [hx]) le_rfl

/-- `K += A/4`, `A := 0` (for `4 ∣ A`). -/
def quarter (A K : Fin nr) : WM ns nr :=
  .whr A (.seq (.dec A) (.seq (.dec A) (.seq (.dec A) (.seq (.dec A) (.inc K)))))

theorem quarter_spec (A K : Fin nr) (hAK : A ≠ K) :
    ∀ (q : ℕ) (σ : WState ns nr), σ.val A = 4 * q → 4 * q ≤ cap → σ.val K + q ≤ cap →
      WExec cap (quarter A K) σ ((σ.setv A 0).setv K (σ.val K + q)) (15 * q + 1)
  | 0, σ, h0, _, _ => by
    have e : (σ.setv A 0).setv K (σ.val K + 0) = σ := by
      refine WState.eq rfl rfl ?_ rfl
      funext j
      by_cases hjK : j = K
      · subst hjK; simp
      · by_cases hjA : j = A
        · subst hjA; simp [Function.update_apply, hjK]; omega
        · simp [Function.update_apply, hjK, hjA]
    rw [e]
    exact WExec.whrF (by omega)
  | q + 1, σ, hq, hA, hK => by
    have h1 : WExec cap (.dec A) σ (σ.setv A (4 * q + 3)) 1 :=
      WExec.cast cap (WExec.dec (cap := cap) A σ (by omega))
        (by rw [hq, show 4 * (q + 1) - 1 = 4 * q + 3 by omega]) le_rfl
    have h2 := dec_setv cap A σ (4 * q + 2) (4 * q + 3) (by omega) (by omega)
    have h3 := dec_setv cap A σ (4 * q + 1) (4 * q + 2) (by omega) (by omega)
    have h4 := dec_setv cap A σ (4 * q) (4 * q + 1) (by omega) (by omega)
    have h5 := inc_to cap K (σ.setv A (4 * q)) (σ.val K) (by rw [wsetv_val_ne _ _ (Ne.symm hAK)]) (by omega)
    have ih := quarter_spec A K hAK q ((σ.setv A (4 * q)).setv K (σ.val K + 1))
      (by rw [wsetv_val_ne _ _ hAK, wsetv_val_self]) (by omega) (by rw [wsetv_val_self]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 h5)))) ih)
      ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext j
    by_cases hjK : j = K
    · subst hjK; simp [Function.update_apply]; omega
    · by_cases hjA : j = A
      · subst hjA; simp [Function.update_apply, hjK]
      · simp [Function.update_apply, hjK, hjA]

/-- `K -= B` (truncated), `B := 0`. -/
def subLp (B K : Fin nr) : WM ns nr := .whr B (.seq (.dec B) (.dec K))

theorem subLp_spec (B K : Fin nr) (hBK : B ≠ K) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val B = n → n ≤ cap → σ.val K ≤ cap →
      WExec cap (subLp B K) σ ((σ.setv B 0).setv K (σ.val K - n)) (5 * n + 1)
  | 0, σ, h0, _, _ => by
    have e : (σ.setv B 0).setv K (σ.val K - 0) = σ := by
      refine WState.eq rfl rfl ?_ rfl
      funext j
      by_cases hjK : j = K
      · subst hjK; simp
      · by_cases hjB : j = B
        · subst hjB; simp [Function.update_apply, hjK]; omega
        · simp [Function.update_apply, hjK, hjB]
    rw [e]
    exact WExec.whrF h0
  | n + 1, σ, hn, hB, hK => by
    have h1 : WExec cap (.dec B) σ (σ.setv B n) 1 :=
      WExec.cast cap (WExec.dec (cap := cap) B σ (by omega)) (by rw [hn, Nat.add_sub_cancel]) le_rfl
    have h2 := WExec.dec (cap := cap) K (σ.setv B n) (by rw [wsetv_val_ne _ _ (Ne.symm hBK)]; exact hK)
    have ih := subLp_spec B K hBK n ((σ.setv B n).setv K ((σ.setv B n).val K - 1))
      (by rw [wsetv_val_ne _ _ hBK, wsetv_val_self]) (by omega)
      (by rw [wsetv_val_self, wsetv_val_ne _ _ (Ne.symm hBK)]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 h2) ih) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext j
    by_cases hjK : j = K
    · subst hjK; simp [Function.update_apply, Ne.symm hBK]; omega
    · by_cases hjB : j = B
      · subst hjB; simp [Function.update_apply, hjK]
      · simp [Function.update_apply, hjK, hjB]

theorem addTo_setv (p v t : Fin nr) (hpv : p ≠ v) (hpt : p ≠ t) (hvt : v ≠ t) (σ : WState ns nr) (x : ℕ)
    (ht : σ.val t = 0) (hp : σ.val p ≤ cap) (hx : x + σ.val p ≤ cap) :
    WExec cap (PrimAsm.ParseNat.addTo p v t) (σ.setv v x) (σ.setv v (x + σ.val p)) (18 * σ.val p + 3) := by
  have h := PrimAsm.ParseNat.addTo_spec cap p v t hpv hpt hvt (σ.setv v x)
    (by rw [wsetv_val_ne _ _ (Ne.symm hvt)]; exact ht) (by rw [wsetv_val_ne _ _ hpv]; exact hp)
    (by rw [wsetv_val_ne _ _ hpv, wsetv_val_self]; exact hx)
  rw [wsetv_val_ne _ _ hpv, wsetv_val_self, wsetv_setv] at h
  exact h

/-- `v += 4p`, `p` kept (scratch `t` at `0`). -/
def add4 (p v t : Fin nr) : WM ns nr :=
  .seq (PrimAsm.ParseNat.addTo p v t) (.seq (PrimAsm.ParseNat.addTo p v t)
    (.seq (PrimAsm.ParseNat.addTo p v t) (PrimAsm.ParseNat.addTo p v t)))

theorem add4_spec (p v t : Fin nr) (hpv : p ≠ v) (hpt : p ≠ t) (hvt : v ≠ t) (σ : WState ns nr)
    (ht : σ.val t = 0) (hp : σ.val p ≤ cap) (hv : σ.val v + 4 * σ.val p ≤ cap) :
    WExec cap (add4 p v t) σ (σ.setv v (σ.val v + 4 * σ.val p)) (4 * (18 * σ.val p + 3) + 3) := by
  have a1 := addTo_setv cap p v t hpv hpt hvt σ (σ.val v) ht hp (by omega)
  have a2 := addTo_setv cap p v t hpv hpt hvt σ (σ.val v + σ.val p) ht hp (by omega)
  have a3 := addTo_setv cap p v t hpv hpt hvt σ (σ.val v + σ.val p + σ.val p) ht hp (by omega)
  have a4 := addTo_setv cap p v t hpv hpt hvt σ (σ.val v + σ.val p + σ.val p + σ.val p) ht hp (by omega)
  rw [wsetv_same] at a1
  refine WExec.cast cap (WExec.seq a1 (WExec.seq a2 (WExec.seq a3 a4))) ?_ (by omega)
  congr 1; omega

/-! ## The bank's first fields -/

/-- `pieceA (4L) d`: `8 := 4L`, `FiltRecW.phaseA` on the bank `fF`, `8 := 0`. -/
def phA (O : Fin (ns + 1)) (Rg : Fin 64 ↪ Fin nr) : WM ns nr :=
  .seq (add4 (Rg 0) (Rg 8) (Rg 9)) (.seq (phaseA O (fF.trans Rg)) (WM.clear (Rg 8)))

theorem phA_spec (O S : Fin (ns + 1)) (hOS : O ≠ S) (Rg : Fin 64 ↪ Fin nr) (τ : WState ns nr) (L d : ℕ)
    (h0 : τ.val (Rg 0) = L) (h5 : τ.val (Rg 5) = d) (h8 : τ.val (Rg 8) = 0) (h9 : τ.val (Rg 9) = 0)
    (h10 : τ.val (Rg 10) = 0) (ho : τ.sh O = (τ.st O).length)
    (hcap : τ.val (Rg 7) + 4 * (8 * (4 * L) + 6) + 30 + 4 * d + 6 + 4 * L + d + 10 ≤ cap) :
    ∃ n, WExec cap (phA O Rg) τ (appendO τ O (Rg 7) (pieceA (4 * L) d)) n ∧ n ≤ 2000 * (L + d + 10) := by
  have hne : ∀ {i j : Fin 64}, i ≠ j → Rg i ≠ Rg j := fun h => Rg.injective.ne h
  have a1 := add4_spec cap (Rg 0) (Rg 8) (Rg 9) (hne (by decide)) (hne (by decide)) (hne (by decide)) τ h9
    (by omega) (by omega)
  rw [h8, h0, Nat.zero_add] at a1
  have hF0 : (fF.trans Rg) 0 = Rg 7 := rfl
  have hF9 : (fF.trans Rg) 9 = Rg 10 := rfl
  have hF13 : (fF.trans Rg) 13 = Rg 8 := rfl
  have hF14 : (fF.trans Rg) 14 = Rg 5 := rfl
  have hF19 : (fF.trans Rg) 19 = Rg 9 := rfl
  obtain ⟨nA, eA, bA⟩ := phaseA_spec cap O S (fF.trans Rg) hOS (τ.setv (Rg 8) (4 * L)) []
    (by rw [hF19, wsetv_val_ne _ _ (hne (by decide))]; exact h9)
    (by rw [hF9, wsetv_val_ne _ _ (hne (by decide))]; exact h10) (by simpa using ho) (4 * L) d
    (by rw [hF13, wsetv_val_self]) (by rw [hF14, wsetv_val_ne _ _ (hne (by decide))]; exact h5)
    (by rw [hF0, wsetv_val_ne _ _ (hne (by decide))]; simp only [List.length_nil]; omega)
  rw [fSt_zero, PrimAsm.PopBlockW.fSt_zero_s hOS, List.nil_append, hF0] at eA
  have a3 := wclear_spec cap (Rg 8) (4 * L) (appendO (τ.setv (Rg 8) (4 * L)) O (Rg 7) (pieceA (4 * L) d))
    (by rw [appendO_val, Function.update_of_ne (hne (by decide)), wsetv_val_self])
    (by rw [appendO_val, Function.update_of_ne (hne (by decide)), wsetv_val_self]; omega)
  rw [← appendO_setv _ O (Rg 7) (Rg 8) (hne (by decide)), wsetv_setv, setv_eq_self τ (Rg 8) 0 h8] at a3
  exact ⟨_, WExec.seq a1 (WExec.seq eA a3), by omega⟩

/-! ## The table word's length -/

/-- `40 := capC/4 − L − 1` (scratch `38`, `39`, `42`). -/
def kComp (Rg : Fin 64 ↪ Fin nr) : WM ns nr :=
  .seq (Hash4.wcopyR (Rg 6) (Rg 38) (Rg 42)) (.seq (quarter (Rg 38) (Rg 40))
    (.seq (Hash4.wcopyR (Rg 0) (Rg 39) (Rg 42)) (.seq (subLp (Rg 39) (Rg 40)) (.dec (Rg 40)))))

theorem kComp_spec (Rg : Fin 64 ↪ Fin nr) (τ : WState ns nr) (w L : ℕ) (h0 : τ.val (Rg 0) = L)
    (h6 : τ.val (Rg 6) = 4 * (w + L + 1)) (h38 : τ.val (Rg 38) = 0) (h39 : τ.val (Rg 39) = 0)
    (h40 : τ.val (Rg 40) = 0) (h42 : τ.val (Rg 42) = 0) (hc : 4 * (w + L + 1) ≤ cap) :
    ∃ n, WExec cap (kComp Rg) τ (τ.setv (Rg 40) w) n ∧ n ≤ 120 * (w + L + 1) := by
  have hne : ∀ {i j : Fin 64}, i ≠ j → Rg i ≠ Rg j := fun h => Rg.injective.ne h
  have k1 := FinalPass.Hash4.wcopyR_spec cap (Rg 6) (Rg 38) (Rg 42) (hne (by decide)) (hne (by decide))
    (hne (by decide)) τ h38 h42 (by omega)
  rw [h6] at k1
  have k2 := quarter_spec cap (Rg 38) (Rg 40) (hne (by decide)) (w + L + 1) (τ.setv (Rg 38) (4 * (w + L + 1)))
    (by rw [wsetv_val_self]) hc (by rw [wsetv_val_ne _ _ (hne (by decide)), h40]; omega)
  rw [wsetv_setv, setv_eq_self τ (Rg 38) 0 h38, wsetv_val_ne _ _ (hne (by decide)), h40, Nat.zero_add] at k2
  have k3 := FinalPass.Hash4.wcopyR_spec cap (Rg 0) (Rg 39) (Rg 42) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (τ.setv (Rg 40) (w + L + 1)) (by rw [wsetv_val_ne _ _ (hne (by decide)), h39])
    (by rw [wsetv_val_ne _ _ (hne (by decide)), h42]) (by rw [wsetv_val_ne _ _ (hne (by decide)), h0]; omega)
  rw [wsetv_val_ne _ _ (hne (by decide)), h0] at k3
  have k4 := subLp_spec cap (Rg 39) (Rg 40) (hne (by decide)) L ((τ.setv (Rg 40) (w + L + 1)).setv (Rg 39) L)
    (by rw [wsetv_val_self]) (by omega) (by rw [wsetv_val_ne _ _ (hne (by decide)), wsetv_val_self]; omega)
  rw [wsetv_setv, wsetv_val_ne _ _ (hne (by decide)), wsetv_val_self,
    setv_eq_self (τ.setv (Rg 40) (w + L + 1)) (Rg 39) 0 (by rw [wsetv_val_ne _ _ (hne (by decide)), h39]),
    wsetv_setv, show w + L + 1 - L = w + 1 by omega] at k4
  have k5 := dec_setv cap (Rg 40) τ w (w + 1) rfl (by omega)
  refine ⟨_, WExec.seq k1 (WExec.seq k2 (WExec.seq k3 (WExec.seq k4 k5))), ?_⟩
  omega

end NearCubicWires.WireExponent3_5.FinalPass.RadB
