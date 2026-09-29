import Proof.Wire_3_5.Primitive.SeedFix.C4HBb

/-! # C4HB, part 3: the cell's stage bounds are polynomial

P3:2262-2268 (the Hb printer's cell stages). Every stage bound of the cell (the validity program `valBound`, the
records program `consBound`, the coefficient and factor writers, the lookups and the `2t` factor records) is at most a
constant times a power of `Q` once its arguments are at most `Q` (the HASH row index at most `Q²`).

* `iCost_le`, `valBound_le`, `tgtCost_le`, `recCostH_le`, `consBound_le`, `coefCost_le`, `factorCost_le`,
  `rawCost_le`, `lookACost_le`, `lookBCost_le`, `atomCost_le`, `atomsCost_le`, `monosCost_le`, `zCost_le`,
  `zBodyBound_le`.

Paper quantity: none (the Hb printer's step counts). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4HB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.HbM

theorem q_le_q2 (Q : ℕ) : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
theorem q2_le_q3 (Q : ℕ) (hQ : 1 ≤ Q) : Q ^ 2 ≤ Q ^ 3 := Nat.pow_le_pow_right hQ (by norm_num)

theorem iCost_le (ℓ L Q : ℕ) (hQ : 1 ≤ Q) (hl : ℓ ≤ Q) (hA : 2 ^ ℓ ≤ Q) (hL : L ≤ Q) : iCost ℓ L ≤ 400 * Q ^ 2 := by
  unfold iCost
  have h1 : ℓ * (36 * 2 ^ ℓ + 12 + 4) ≤ Q * (36 * Q + 16) := Nat.mul_le_mul hl (by omega)
  have e1 : Q * (36 * Q + 16) = 36 * Q ^ 2 + 16 * Q := by ring
  have hQ := q_le_q2 Q
  generalize 2 ^ ℓ = A at *
  generalize Q ^ 2 = Q2 at *
  omega

theorem valBound_le (lam J p T2 ℓ L P Q : ℕ) (hQ : 1 ≤ Q) (h1 : lam ≤ Q) (h2 : J ≤ Q) (h3 : p ≤ Q) (h4 : T2 ≤ Q)
    (h5 : ℓ ≤ Q) (hA : 2 ^ ℓ ≤ Q) (h6 : L ≤ Q) (h7 : P ≤ Q) : valBound lam J p T2 ℓ L P ≤ 3000 * Q ^ 3 := by
  unfold valBound
  have hi := iCost_le ℓ L Q hQ h5 hA h6
  have m1 : p * (9 * P + 20 + 4) ≤ Q * (9 * Q + 24) := Nat.mul_le_mul h3 (by omega)
  have e1 : Q * (9 * Q + 24) = 9 * Q ^ 2 + 24 * Q := by ring
  have m2 : (T2 + 1) * (iCost ℓ L + 4) ≤ (2 * Q) * (404 * Q ^ 2) := Nat.mul_le_mul (by omega) (by
    have := q_le_q2 Q; omega)
  have e2 : (2 * Q) * (404 * Q ^ 2) = 808 * Q ^ 3 := by ring
  have e3 : T2 * (5 + 4) = 9 * T2 := by ring
  have hQ2 := q_le_q2 Q
  have hQ3 := q2_le_q3 Q hQ
  generalize 2 ^ ℓ = A at *
  generalize Q ^ 2 = Q2 at *
  generalize Q ^ 3 = Q3 at *
  omega

theorem tgtCost_le (lam Q : ℕ) (h : lam ≤ Q) : tgtCost lam ≤ 50 * Q + 20 := by
  unfold tgtCost; omega

theorem recCostH_le (ℓ lam Q : ℕ) (hl : ℓ ≤ Q) (h : lam ≤ Q) : HbM.recCost ℓ lam ≤ 100 * Q + 50 := by
  unfold HbM.recCost; have := tgtCost_le lam Q h; omega

theorem consBound_le (lam J T2 ℓ Q : ℕ) (hQ : 1 ≤ Q) (h1 : lam ≤ Q) (h2 : J ≤ Q) (h3 : T2 ≤ Q) (h4 : ℓ ≤ Q) :
    consBound lam J T2 ℓ ≤ 2000 * Q ^ 2 := by
  unfold consBound
  have hr := recCostH_le ℓ lam Q h4 h1
  have m1 : T2 * (HbM.recCost ℓ lam + 4) ≤ Q * (100 * Q + 54) := Nat.mul_le_mul h3 (by omega)
  have e1 : Q * (100 * Q + 54) = 100 * Q ^ 2 + 54 * Q := by ring
  have e2 : T2 * (6 + 4) = 10 * T2 := by ring
  have hQ2 := q_le_q2 Q
  generalize Q ^ 2 = Q2 at *
  omega

theorem coefCost_le (e lam wtl fl Q : ℕ) (hQ : 1 ≤ Q) (h1 : e ≤ Q) (h2 : lam ≤ Q) (h3 : wtl ≤ Q) (h4 : fl ≤ Q) :
    coefCost e lam wtl fl ≤ 100 * Q ^ 2 := by
  unfold coefCost
  have m1 : lam * (5 * wtl + 3 + 4) ≤ Q * (5 * Q + 7) := Nat.mul_le_mul h2 (by omega)
  have e1 : Q * (5 * Q + 7) = 5 * Q ^ 2 + 7 * Q := by ring
  have hQ2 := q_le_q2 Q
  generalize Q ^ 2 = Q2 at *
  omega

theorem factorCost_le (e q nE idx htl pl Q : ℕ) (hQ : 1 ≤ Q) (h1 : e ≤ Q) (h2 : q ≤ Q) (h3 : nE ≤ Q)
    (h4 : idx ≤ Q ^ 2) (h5 : htl ≤ Q) (h6 : pl ≤ Q) : factorCost e q nE idx htl pl ≤ 200 * Q ^ 3 := by
  unfold factorCost
  have m1 : nE * (18 * q + 8) ≤ Q * (18 * Q + 8) := Nat.mul_le_mul h3 (by omega)
  have e1 : Q * (18 * Q + 8) = 18 * Q ^ 2 + 8 * Q := by ring
  have m2 : idx * (2 * 9 + 1 + (4 * htl + 3 + 1 + 2 * 3) + 4) ≤ Q ^ 2 * (4 * Q + 33) := Nat.mul_le_mul h4 (by omega)
  have e2 : Q ^ 2 * (4 * Q + 33) = 4 * Q ^ 3 + 33 * Q ^ 2 := by ring
  have hQ2 := q_le_q2 Q
  have hQ3 := q2_le_q3 Q hQ
  generalize Q ^ 2 = Q2 at *
  generalize Q ^ 3 = Q3 at *
  omega

theorem rawCost_le (ℓ Q : ℕ) (hl : ℓ ≤ Q) (hA : 2 ^ ℓ ≤ Q) : rawCost ℓ ≤ 100 * Q ^ 2 + 10 := by
  unfold rawCost
  have m1 : ℓ * (36 * 2 ^ ℓ + 12 + 4) ≤ Q * (36 * Q + 16) := Nat.mul_le_mul hl (by omega)
  have e1 : Q * (36 * Q + 16) = 36 * Q ^ 2 + 16 * Q := by ring
  have hQ2 := q_le_q2 Q
  generalize 2 ^ ℓ = A at *
  generalize Q ^ 2 = Q2 at *
  omega

theorem lookACost_le (ℓ p pw Q : ℕ) (hl : ℓ ≤ Q) (hA : 2 ^ ℓ ≤ Q) (hp : p ≤ Q) (hw : pw ≤ Q) :
    lookACost ℓ p pw ≤ 200 * Q ^ 2 + 100 := by
  unfold lookACost
  have hr := rawCost_le ℓ Q hl hA
  have m1 : p * (9 * pw + 20 + 4) ≤ Q * (9 * Q + 24) := Nat.mul_le_mul hp (by omega)
  have e1 : Q * (9 * Q + 24) = 9 * Q ^ 2 + 24 * Q := by ring
  have hQ2 := q_le_q2 Q
  generalize Q ^ 2 = Q2 at *
  omega

theorem lookBCost_le (i pw G Q : ℕ) (hi : i ≤ Q) (hw : pw ≤ Q) (hG : G ≤ Q) : lookBCost i pw G ≤ 100 * Q ^ 2 + 100 := by
  unfold lookBCost
  have m1 : i * (7 * pw + 13 + 4) ≤ Q * (7 * Q + 17) := Nat.mul_le_mul hi (by omega)
  have e1 : Q * (7 * Q + 17) = 7 * Q ^ 2 + 17 * Q := by ring
  have hQ2 := q_le_q2 Q
  generalize Q ^ 2 = Q2 at *
  omega

theorem atomCost_le (q4 G gi k Q : ℕ) (hq : q4 ≤ 4 * Q) (hG : G ≤ Q) (hg : gi ≤ Q) (hk : k ≤ 3) :
    atomCost q4 G gi k ≤ 1000 * Q ^ 2 + 1000 := by
  unfold atomCost
  have m1 : G * (18 * (q4 + k) + 8) ≤ Q * (72 * Q + 62) := Nat.mul_le_mul hG (by omega)
  have e1 : Q * (72 * Q + 62) = 72 * Q ^ 2 + 62 * Q := by ring
  have m2 : (q4 + k) * G ≤ (4 * Q + 3) * Q := Nat.mul_le_mul (by omega) hG
  have e2 : (4 * Q + 3) * Q = 4 * Q ^ 2 + 3 * Q := by ring
  have m3 : (gi + (q4 + k) * G) * (8 * 2 + 4) = 20 * (gi + (q4 + k) * G) := by ring
  have hQ2 := q_le_q2 Q
  generalize Q ^ 2 = Q2 at *
  omega

theorem atomsCost_le (q4 G gi Q : ℕ) (hq : q4 ≤ 4 * Q) (hG : G ≤ Q) (hg : gi ≤ Q) :
    ∀ m : List ℕ, (∀ k ∈ m, k ≤ 3) → atomsCost q4 G gi m ≤ m.length * (1000 * Q ^ 2 + 1001)
  | [], _ => by simp [atomsCost]
  | k :: m, h => by
    have h1 := atomCost_le q4 G gi k Q hq hG hg (h k List.mem_cons_self)
    have h2 := atomsCost_le q4 G gi Q hq hG hg m (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    rw [atomsCost, List.length_cons, Nat.add_mul, one_mul]
    omega

theorem monosCost_le (q4 G gi Q : ℕ) (hq : q4 ≤ 4 * Q) (hG : G ≤ Q) (hg : gi ≤ Q) :
    ∀ ms : List (List ℕ), (∀ m ∈ ms, (∀ k ∈ m, k ≤ 3) ∧ m.length ≤ 3) →
      monosCost q4 G gi ms ≤ ms.length * (3000 * Q ^ 2 + 3100)
  | [], _ => by simp [monosCost]
  | m :: ms, h => by
    have hm := h m List.mem_cons_self
    have h1 := atomsCost_le q4 G gi Q hq hG hg m hm.1
    have h1' : m.length * (1000 * Q ^ 2 + 1001) ≤ 3 * (1000 * Q ^ 2 + 1001) := Nat.mul_le_mul_right _ hm.2
    have h2 := monosCost_le q4 G gi Q hq hG hg ms (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))
    rw [monosCost, monoCost, List.length_cons, Nat.add_mul, one_mul]
    omega

theorem zCost_le (q4 G Q : ℕ) (hq : q4 ≤ 4 * Q) (hG : G ≤ Q) : zCost q4 G G ≤ 60000 * Q ^ 2 + 62010 := by
  unfold zCost
  have hp := monosCost_le q4 G G Q hq hG hG zPlusL (zL_ok true)
  have hm := monosCost_le q4 G G Q hq hG hG zMinusL (zL_ok false)
  have l1 : zPlusL.length = 10 := zL_length true
  have l2 : zMinusL.length = 10 := zL_length false
  rw [l1] at hp
  rw [l2] at hm
  omega

theorem zBodyBound_le (q G ℓ p pw Q : ℕ) (hQ : 1 ≤ Q) (hq : q ≤ Q) (hG : G ≤ Q) (hl : ℓ ≤ Q) (hA : 2 ^ ℓ ≤ Q)
    (hp : p ≤ Q) (hw : pw ≤ Q) : zBodyBound q G ℓ p pw ≤ 130000 * Q ^ 2 := by
  unfold zBodyBound
  have h1 := lookACost_le ℓ p pw Q hl hA hp hw
  have h2 := lookBCost_le pw pw G Q hw hw hG
  have h3 := zCost_le (4 * q) G Q (by omega) hG
  have hQ2 := q_le_q2 Q
  have hQ1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ
  generalize Q ^ 2 = Q2 at *
  omega

end NearCubicWires.WireExponent3_5.PrimT.C4HB
