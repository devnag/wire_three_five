import Lean
import Proof.Wire_3_5.UnionMachine.FrontSemTopSBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.FrontCaps
import Proof.Wire_3_5.UnionMachine.PlanW2


noncomputable section
set_option maxRecDepth 120000


/-! # C6 front, the time (1): the per-call budget dominates every fixed-degree polynomial of `N` (P3:3637-3655, 3797-3811)

At the pinned ledger `BU` (width `q(N)`, clock `N^{k+2}`, `k = kE l e`), the per-call budget
`callBudget q ≥ coef·2^{q−⌊k(q)/4⌋}·q^{A_main}` dominates `c·(N+2)^D·(q+2)^d` eventually whenever `D + 1 ≤ k`
(**`cb_dom`**): `2^q ≥ N^{k+2}` (the width's `⌈log₂ N^{k+2}⌉`), `2^{⌊k(q)/4⌋} ≤ N` (the star width is `O(L(q)²)` and
`q = O(L(N))`), `(q+2)^d ≤ N`.

Paper quantity of the main type: the union's per-call budget against the front's own work. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCostLedger
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.UnionMachine.PlanW2
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps (BU)
open Filter

section Dom
variable (l : Literals) (F : GateFree l) (e coef A : ℕ)

/-- `2^{⌊k(q)/4⌋} ≤ N` past an onset. -/
theorem kOf_small : ∀ᶠ N : ℕ in atTop,
    2 ^ ((BU l F e coef A).kOf ((BU l F e coef A).q N) / 4) ≤ N := by
  have hq : Tendsto (BU l F e coef A).q atTop atTop := Ledger.tendsto_nativeWidth (kE l e) (gateApad l)
  set Kn := FrontSemEv.Kn (kE l e) (gateApad l) with hKn
  have e1 := eventually_mul_Lq_pow_le (2 * Kn * (2 * (gate0 l F).row.cr + 3)) 2
  have e2 : ∀ᶠ q : ℕ in atTop, 2 * (3 * Kn) ≤ q := eventually_ge_atTop _
  filter_upwards [hq.eventually e1, hq.eventually e2, eventually_ge_atTop 1] with N h1 h2 hN1
  set q := (BU l F e coef A).q N with hqd
  have hk : (BU l F e coef A).kOf q ≤ (2 * (gate0 l F).row.cr + 3) * (Lq q * Lq q) :=
    FrontLedger.kOf_le (gate0 l F).E coef (gate0 l F).row
      (nativeWidthData (kE l e) (gate0 l F).Apad (gate0 l F).E (gate0 l F).hσ A (aE l e) (haE l e)) q
  have hw : q ≤ Kn * Lq N := FrontSemEv.nw_le_Lq (kE l e) (gateApad l) N
  have hKn1 : 1 ≤ Kn := by rw [hKn]; unfold FrontSemEv.Kn; nlinarith
  -- m + 3 ≤ L(N)
  have hm : Kn * ((BU l F e coef A).kOf q / 4 + 3) ≤ Kn * Lq N := by
    have a1 : Kn * ((2 * (gate0 l F).row.cr + 3) * (Lq q * Lq q)) * 2 ≤ q := by
      have e : 2 * Kn * (2 * (gate0 l F).row.cr + 3) * Lq q ^ 2 =
          Kn * ((2 * (gate0 l F).row.cr + 3) * (Lq q * Lq q)) * 2 := by ring
      rw [← e]; exact h1
    have a2 : Kn * ((BU l F e coef A).kOf q / 4) ≤ Kn * ((2 * (gate0 l F).row.cr + 3) * (Lq q * Lq q)) :=
      Nat.mul_le_mul_left _ ((Nat.div_le_self _ _).trans hk)
    rw [Nat.mul_add]; omega
  have hm' : (BU l F e coef A).kOf q / 4 + 3 ≤ Lq N := Nat.le_of_mul_le_mul_left hm (by omega)
  have hlt : 2 ^ (Nat.clog 2 (N + 2)).pred < N + 2 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < N + 2 by omega)
  have hlt' : 2 ^ (Lq N - 1) < N + 2 := hlt
  have hL1 : 1 ≤ Lq N := Lq_pos N
  have hpow : 2 ^ ((BU l F e coef A).kOf q / 4) * 4 ≤ 2 ^ (Lq N - 1) := by
    calc 2 ^ ((BU l F e coef A).kOf q / 4) * 4 = 2 ^ ((BU l F e coef A).kOf q / 4 + 2) := by rw [pow_add]; norm_num
      _ ≤ 2 ^ (Lq N - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- `N^{k+2} ≤ 2^{q(N)}`. -/
theorem pow_le_two_pow_q (N : ℕ) : N ^ (kE l e + 2) ≤ 2 ^ (BU l F e coef A).q N :=
  (Nat.le_pow_clog (by norm_num) _).trans
    (Nat.pow_le_pow_right (by norm_num) (clog_le_nativeWidth (kE l e) (gateApad l) N))

/-- **The per-call budget dominates `c·(N+2)^D·(q+2)^d` eventually** (`D + 1 ≤ k`). -/
theorem cb_dom (hcoef : 1 ≤ coef) (c d D : ℕ) (hD : D + 1 ≤ kE l e) : ∀ᶠ N : ℕ in atTop,
    c * (N + 2) ^ D * ((BU l F e coef A).q N + 2) ^ d ≤
      (BU l F e coef A).callBudget ((BU l F e coef A).q N) := by
  have e1 := kOf_small l F e coef A
  have e2 := FrontSemEv.polyq_le (kE l e) (gateApad l) (2 ^ d) d
  have e3 : ∀ᶠ N : ℕ in atTop, c * 3 ^ D ≤ N := eventually_ge_atTop _
  have hq : Tendsto (BU l F e coef A).q atTop atTop := Ledger.tendsto_nativeWidth (kE l e) (gateApad l)
  filter_upwards [e1, e2, e3, eventually_ge_atTop 1, hq.eventually (eventually_ge_atTop 1)] with N h1 h2 h3 hN hq1
  set q := (BU l F e coef A).q N with hqd
  set m := (BU l F e coef A).kOf q / 4 with hmd
  have hqd2 : (q + 2) ^ d ≤ N := by
    have : (q + 2) ^ d ≤ 2 ^ d * (q + 1) ^ d := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) d
    exact this.trans h2
  have hN2 : (N + 2) ^ D ≤ 3 ^ D * N ^ D := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) D
  have hpq : N ^ (kE l e + 2) ≤ 2 ^ q := pow_le_two_pow_q l F e coef A N
  have hmq : m ≤ q := by
    have := Nat.lt_pow_self (show 1 < 2 by norm_num) (n := m)
    have h4 : N ^ 1 ≤ N ^ (kE l e + 2) := Nat.pow_le_pow_right hN (by omega)
    have h5 : 2 ^ m ≤ 2 ^ q := by rw [pow_one] at h4; omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h5
  have hsplit : 2 ^ q = 2 ^ (q - m) * 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel hmq]
  have hlow := FrontCaps.callBudget_lower l F e coef A q
  have hq1' : 1 ≤ q ^ (gate0 l F).E.Amain := Nat.one_le_pow _ _ hq1
  have hcb : 2 ^ (q - m) ≤ (BU l F e coef A).callBudget q := by
    refine le_trans ?_ hlow
    calc 2 ^ (q - m) = 1 * (2 ^ (q - m) * 1) := by ring
      _ ≤ coef * (2 ^ (q - m) * q ^ (gate0 l F).E.Amain) := Nat.mul_le_mul hcoef (Nat.mul_le_mul_left _ hq1')
  -- the main chain
  have key : c * (N + 2) ^ D * (q + 2) ^ d * 2 ^ m ≤ N ^ (kE l e + 2) := by
    calc c * (N + 2) ^ D * (q + 2) ^ d * 2 ^ m ≤ c * (3 ^ D * N ^ D) * N * N :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hN2) hqd2) h1
      _ = (c * 3 ^ D) * N ^ D * N * N := by ring
      _ ≤ N * N ^ D * N * N := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3))
      _ = N ^ (D + 3) := by ring
      _ ≤ N ^ (kE l e + 2) := Nat.pow_le_pow_right hN (by omega)
  have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have key2 : c * (N + 2) ^ D * (q + 2) ^ d * 2 ^ m ≤ 2 ^ (q - m) * 2 ^ m := by rw [← hsplit]; exact key.trans hpq
  exact (Nat.le_of_mul_le_mul_right key2 (by omega)).trans hcb

end Dom

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCostLedger

end
