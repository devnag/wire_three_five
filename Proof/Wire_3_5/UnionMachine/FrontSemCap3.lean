import Proof.Wire_3_5.UnionMachine.FrontSemCap2Base

/-! # C6 front, the semantic core (14): the numbers' caps and the sparse bound (P3:3400, 3690-3691, 3742-3744)

* **`sparse_pq`**: the sparse count's value bound `sparseBound ζ C_δ L(q) (t(q) − 1)` is polynomial in `q` (PA2's
  `sparse_le_P` / `rowBt_le` / `sparse_le_gate`, re-derived at a general `ζ` with a block length `J`: `t = O(L)`, each
  value `≤ 20(L³+1)·X^{32t}`, `2^L ≤ 4(q+1)`).
* **`numsCaps_of`**: the numbers' capacities (`FrontCh3P.NumsCaps`) at `2W + 2` from a numeric envelope `K` (the width,
  the PCPP output's counts, `2^{cb}`, the grid, the mass), the width above `PW K`, the data bound above `BK K`.

Paper quantity of the main types: the row-B ledger's sparse count and the numbers the union machine computes from `q`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap3
open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.PrimAsm.SparseNum (sparseBound zB c1 c2)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap2 (BK PW pow2_bits bits_le pw_small bk_po)

/-- The sparse bound's base `X`. -/
def spX (ζ : ℚ) (Cδ : ℕ) : ℕ := 2 * zB ζ + c1 ζ + c2 ζ + Cδ + 4

/-- **Every value of the sparse count's program** `≤ 20(L³+1)·X^{32(m+1)}` (`sparse_le_P`). -/
theorem sparse_le_P (ζ : ℚ) (Cδ L m : ℕ) :
    sparseBound ζ Cδ L m ≤ 20 * (L ^ 3 + 1) * spX ζ Cδ ^ (32 * (m + 1)) := by
  obtain ⟨X, hX⟩ : ∃ x, x = spX ζ Cδ := ⟨_, rfl⟩
  rw [← hX]
  have hX4 : 4 ≤ X := by rw [hX]; unfold spX; omega
  have hX1 : 1 ≤ X := by omega
  have hz : zB ζ ≤ X := by rw [hX]; unfold spX; omega
  have hz2 : 2 * zB ζ ≤ X := by rw [hX]; unfold spX; omega
  have hc1 : c1 ζ ≤ X := by rw [hX]; unfold spX; omega
  have hc2 : c2 ζ ≤ X := by rw [hX]; unfold spX; omega
  have hd : Cδ ≤ X := by rw [hX]; unfold spX; omega
  obtain ⟨P, hP⟩ : ∃ p, p = X ^ (32 * (m + 1)) := ⟨_, rfl⟩
  have hp : ∀ e, e ≤ 32 * (m + 1) → X ^ e ≤ P := fun e he => by rw [hP]; exact Nat.pow_le_pow_right hX1 he
  have hP1 : 1 ≤ P := by rw [hP]; exact Nat.one_le_pow _ _ hX1
  have hXP : X ≤ P := by have := hp 1 (by omega); rwa [pow_one] at this
  have q1 : c2 ζ ^ 16 * (c1 ζ ^ 16) ^ m ≤ P := by
    calc c2 ζ ^ 16 * (c1 ζ ^ 16) ^ m ≤ X ^ 16 * (X ^ 16) ^ m :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hc2 _) (Nat.pow_le_pow_left (Nat.pow_le_pow_left hc1 _) _)
      _ = X ^ (16 + 16 * m) := by rw [← pow_mul, ← pow_add]
      _ ≤ P := hp _ (by omega)
  have q2 : (2 * zB ζ) ^ 16 * (zB ζ ^ 16) ^ m ≤ P := by
    calc (2 * zB ζ) ^ 16 * (zB ζ ^ 16) ^ m ≤ X ^ 16 * (X ^ 16) ^ m :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hz2 _) (Nat.pow_le_pow_left (Nat.pow_le_pow_left hz _) _)
      _ = X ^ (16 + 16 * m) := by rw [← pow_mul, ← pow_add]
      _ ≤ P := hp _ (by omega)
  have hw : zB ζ * zB ζ ^ m * 4 ≤ X ^ (m + 2) := by
    calc zB ζ * zB ζ ^ m * 4 ≤ X * X ^ m * X :=
          Nat.mul_le_mul (Nat.mul_le_mul hz (Nat.pow_le_pow_left hz _)) (by omega)
      _ = X ^ (m + 2) := by ring
  have q3 : zB ζ * zB ζ ^ m * 4 * (zB ζ * zB ζ ^ m * 4) * Cδ ≤ P := by
    calc zB ζ * zB ζ ^ m * 4 * (zB ζ * zB ζ ^ m * 4) * Cδ ≤ X ^ (m + 2) * X ^ (m + 2) * X :=
          Nat.mul_le_mul (Nat.mul_le_mul hw hw) hd
      _ = X ^ (2 * m + 5) := by ring
      _ ≤ P := hp _ (by omega)
  have q4 : zB ζ * zB ζ ^ m * 4 * (zB ζ * zB ζ ^ m * 4) ≤ P := by
    calc zB ζ * zB ζ ^ m * 4 * (zB ζ * zB ζ ^ m * 4) ≤ X ^ (m + 2) * X ^ (m + 2) := Nat.mul_le_mul hw hw
      _ = X ^ (2 * m + 4) := by ring
      _ ≤ P := hp _ (by omega)
  have q5 : zB ζ * zB ζ ^ m * 4 ≤ P := le_trans hw (hp _ (by omega))
  have q6 : c1 ζ ^ m * c2 ζ ≤ P := by
    calc c1 ζ ^ m * c2 ζ ≤ X ^ m * X := Nat.mul_le_mul (Nat.pow_le_pow_left hc1 _) hc2
      _ = X ^ (m + 1) := by ring
      _ ≤ P := hp _ (by omega)
  have q7 : c1 ζ ^ 16 ≤ P := le_trans (Nat.pow_le_pow_left hc1 _) (hp _ (by omega))
  have q8 : zB ζ ^ 16 ≤ P := le_trans (Nat.pow_le_pow_left hz _) (hp _ (by omega))
  have q9 : c2 ζ ^ 16 ≤ P := le_trans (Nat.pow_le_pow_left hc2 _) (hp _ (by omega))
  have q10 : (2 * zB ζ) ^ 16 ≤ P := le_trans (Nat.pow_le_pow_left hz2 _) (hp _ (by omega))
  have q11 : c1 ζ ^ m ≤ P := le_trans (Nat.pow_le_pow_left hc1 _) (hp _ (by omega))
  have q12 : m ≤ P := by
    have a1 : m < 2 ^ m := Nat.lt_two_pow_self
    have a2 : 2 ^ m ≤ X ^ m := Nat.pow_le_pow_left (by omega) _
    have a3 := hp m (by omega)
    omega
  have q13 : 8 ≤ P := by
    have a1 : 4 ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hX4 2
    have a2 := hp 2 (by omega)
    norm_num at a1; omega
  have hL : L ≤ L ^ 3 := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; simp
    · calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 3 := Nat.pow_le_pow_right h (by norm_num)
  have r1 : L ^ 3 * c2 ζ ^ 16 * (c1 ζ ^ 16) ^ m ≤ L ^ 3 * P := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ q1
  have r2 : L ^ 3 ≤ L ^ 3 * P := Nat.le_mul_of_pos_right _ hP1
  have e : 20 * (L ^ 3 + 1) * P = 20 * (L ^ 3 * P) + 20 * P := by ring
  unfold sparseBound
  rw [← hP, e]
  omega

section Sparse
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **`t = O(L)`**: `rowBt q ≤ J(L+1) + 1` (`rowBt_le`, at a general `ζ`). -/
theorem rowBt_le {J : ℕ} (hJ : ((1 - ζ) ^ 16) ^ J ≤ 1 / 8) (n : ℕ) :
    Ledger.rowBt h0 h1 n ≤ J * (Ledger.Lq n + 1) + 1 := by
  have h := Schedule.sched_log h0 h1 hJ (Ledger.Lq n)
  have h2 : Nat.log 2 (Ledger.Lq n) ≤ Ledger.Lq n := Nat.log_le_self 2 _
  have h3 : J * (Nat.log 2 (Ledger.Lq n) + 1) ≤ J * (Ledger.Lq n + 1) := Nat.mul_le_mul_left _ (by omega)
  show Schedule.sched ζ h0 h1 (Ledger.Lq n) ≤ _
  omega

/-- **The sparse count's value bound is polynomial in `q`.** -/
theorem sparse_pq {J : ℕ} (hJ : ((1 - ζ) ^ 16) ^ J ≤ 1 / 8) (Cδ : ℕ) :
    FrontCaps.PQ (fun n => sparseBound ζ Cδ (Ledger.Lq n) (Ledger.rowBt h0 h1 n - 1)) := by
  obtain ⟨cX, hcX⟩ : ∃ c, c = Nat.clog 2 (spX ζ Cδ) := ⟨_, rfl⟩
  refine ⟨2 ^ (6 + 32 * cX * (J + 1) + 2 * (3 + 32 * cX * J)), 3 + 32 * cX * J, fun n => ?_⟩
  have hs := sparse_le_P ζ Cδ (Ledger.Lq n) (Ledger.rowBt h0 h1 n - 1)
  have ht := rowBt_le h0 h1 hJ n
  have h2L : 2 ^ Ledger.Lq n ≤ 4 * (n + 1) := FrontCaps.two_pow_unionBits n
  obtain ⟨L, hL⟩ : ∃ x, x = Ledger.Lq n := ⟨_, rfl⟩
  rw [← hL] at hs ht h2L
  obtain ⟨m, hm⟩ : ∃ x, x = Ledger.rowBt h0 h1 n - 1 := ⟨_, rfl⟩
  rw [← hm] at hs
  have hm1 : m + 1 ≤ J * L + J + 1 := by
    have e : J * (L + 1) = J * L + J := by ring
    omega
  have hX : spX ζ Cδ ≤ 2 ^ cX := by rw [hcX]; exact Nat.le_pow_clog (by norm_num) _
  have hP : spX ζ Cδ ^ (32 * (m + 1)) ≤ 2 ^ (32 * cX * (J * L + J + 1)) := by
    calc spX ζ Cδ ^ (32 * (m + 1)) ≤ (2 ^ cX) ^ (32 * (m + 1)) := Nat.pow_le_pow_left hX _
      _ = 2 ^ (cX * (32 * (m + 1))) := by rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by
          calc cX * (32 * (m + 1)) = 32 * cX * (m + 1) := by ring
            _ ≤ 32 * cX * (J * L + J + 1) := Nat.mul_le_mul_left _ hm1)
  have hL3 : L ^ 3 ≤ 2 ^ (3 * L) := by
    calc L ^ 3 ≤ (2 ^ L) ^ 3 := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := L)).le 3
      _ = 2 ^ (3 * L) := by rw [← pow_mul, mul_comm]
  have h20 : 20 * (L ^ 3 + 1) ≤ 2 ^ (3 * L + 6) := by
    have : 1 ≤ 2 ^ (3 * L) := Nat.one_le_two_pow
    rw [pow_add]; omega
  show sparseBound ζ Cδ (Ledger.Lq n) (Ledger.rowBt h0 h1 n - 1) ≤ _
  rw [← hL, ← hm]
  calc sparseBound ζ Cδ L m ≤ 20 * (L ^ 3 + 1) * spX ζ Cδ ^ (32 * (m + 1)) := hs
    _ ≤ 2 ^ (3 * L + 6) * 2 ^ (32 * cX * (J * L + J + 1)) := Nat.mul_le_mul h20 hP
    _ = 2 ^ (6 + 32 * cX * (J + 1)) * (2 ^ L) ^ (3 + 32 * cX * J) := by
        rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
    _ ≤ 2 ^ (6 + 32 * cX * (J + 1)) * (4 * (n + 1)) ^ (3 + 32 * cX * J) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2L _)
    _ = 2 ^ (6 + 32 * cX * (J + 1) + 2 * (3 + 32 * cX * J)) * (n + 1) ^ (3 + 32 * cX * J) := by
        rw [mul_pow, show (4 : ℕ) ^ (3 + 32 * cX * J) = 2 ^ (2 * (3 + 32 * cX * J)) by rw [pow_mul]; norm_num,
          ← mul_assoc, ← pow_add]

/-- **The numbers' capacities** at `2W + 2` from a numeric envelope `K`. -/
theorem numsCaps_of {W Kb Db Cδ q sys aux cb K : ℕ} (hq : q ≤ K) (hnv : sys + aux ≤ K) (hcb : 2 ^ cb ≤ K)
    (hs : Ledger.rowBSparse h0 h1 2 Cδ q ≤ K) (hs1 : 1 ≤ Ledger.rowBSparse h0 h1 2 Cδ q)
    (hΛ : Ledger.rowBLambda h0 h1 2 q ≤ K)
    (hsp : sparseBound ζ Cδ (Ledger.Lq q) (Ledger.rowBt h0 h1 q - 1) ≤ 2 * W + 2)
    (hBK : BK K ≤ Kb * (q + 1) ^ Db) (hW1 : PW K ≤ W) (hW3 : Kb * (q + 1) ^ Db + Kb + (q + 1) ^ Db ≤ W) :
    FrontCh3P.NumsCaps (2 * W + 2) h0 h1 Kb Db Cδ q sys aux cb := by
  have hcb' : cb ≤ K := le_trans (Nat.lt_two_pow_self (n := cb)).le hcb
  have hsm := pw_small K
  have hbk := bk_po K
  have hvs : (sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q ≤ K * K := Nat.mul_le_mul hnv hs
  refine
    { hB := ?_
      hK := by omega
      hq4 := by omega
      hPw := fun k hk => le_trans (Nat.pow_le_pow_right (by omega) hk) (by omega)
      hBc := by omega
      hB2 := ?_
      cq := le_trans (pow2_bits q) (by omega)
      c3 := le_trans (pow2_bits 3) (by omega)
      cs := le_trans (pow2_bits _) (by omega)
      ca := le_trans (pow2_bits _) (by omega)
      cc := le_trans (pow2_bits _) (by omega)
      hsp := hsp
      hc := le_trans (FrontSemCap2.numCap_le _ _ _ _ _ _ K hs hΛ hq (by omega) (by omega) hcb' hcb) (by omega)
      hs1 := hs1
      hcE := by omega
      hhd := by omega }
  · have := FrontSemCap1.natWord_le q
    omega
  · have := FrontSemCap1.natWord_le 3
    have := FrontSemCap1.natWord_le sys
    have := FrontSemCap1.natWord_le aux
    have := FrontSemCap1.natWord_le cb
    omega

end Sparse

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap3
