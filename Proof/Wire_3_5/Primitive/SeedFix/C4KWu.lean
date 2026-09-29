import Proof.Wire_3_5.Primitive.SeedFix.C4KWt
import Proof.Wire_3_5.Primitive.SeedFix.W6O

/-! # C4KW, part 20: stage B2's cost and **`partB2 : PartB2`**

Every size of B2's run is at most `Q = 200·(kwT + 1)^4` (`t, J, B* ≤ kwT`, `2^{J+1} ≤ 2^{ℓ₀} ≤ refMod ≤ kwT` since
`J < ℓ₀` and `refMod = firstPrimitive ℓ₀ ≥ 2^{ℓ₀}`, `s ≤ t·B*`, `Wmax`, the width), and the steps are at most
`10^7·Q^6` (**`b2_bound`**). **`outL_word`**: the output is the framed `wtWord (wsOf MP)` (the machine's weights are the
cleared weights, `vOf_eq`). **`partB2`**.

Paper quantity of the main type: the cleared weights' word `wtWord (wsOf MP)` (P3:2280-2281). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires.WireExponent3_5.UnionMachine.EwLevel (twOf twMax twOf_le twCost)

/-! ## The word -/

theorem prs_flatMap {α : Type} (f : α → List Bool) : ∀ L : List α, prs (L.flatMap f) = L.flatMap (fun x => prs (f x))
  | [] => rfl
  | x :: L => by rw [List.flatMap_cons, List.flatMap_cons, prs_append, prs_flatMap f L]

theorem outL_word (MP : Filters.MajorantParams) :
    outL MP.t (Nat.sqrt (MP.t * MP.Bstar)) MP.J (MP.J + 1) = prs (PrimT.HbM.wtWord (PrimT.HbM.wsOf MP)) := by
  unfold outL PrimT.HbM.wtWord PrimT.HbM.wsOf
  rw [List.flatMap_map, prs_flatMap]
  apply List.flatMap_congr
  intro l hl
  rw [vOf_eq MP l (by simpa [Nat.lt_succ_iff] using List.mem_range.mp hl)]

/-! ## The cost -/

theorem b2_bound (t s J B Q : ℕ) (hQ : 1 ≤ Q) (ht : t ≤ Q) (hJ : J ≤ Q) (hB : B ≤ Q) (hs : s ≤ Q) (hBt : B * t ≤ Q)
    (hJt : J * (2 * t) ≤ Q) (hWm : twMax t s ≤ Q) (hwd : wdOf t s J ≤ Q) (h2 : 2 ^ (J + 1) ≤ Q) :
    b2Cost t s J B + capB t s J B ≤ 10000000 * Q ^ 6 := by
  have q2 : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
  have q23 : Q ^ 2 ≤ Q ^ 3 := Nat.pow_le_pow_right hQ (by norm_num)
  have q34 : Q ^ 3 ≤ Q ^ 4 := Nat.pow_le_pow_right hQ (by norm_num)
  have q45 : Q ^ 4 ≤ Q ^ 5 := Nat.pow_le_pow_right hQ (by norm_num)
  have q56 : Q ^ 5 ≤ Q ^ 6 := Nat.pow_le_pow_right hQ (by norm_num)
  have h2J : 2 ^ J ≤ Q := le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J)) h2
  -- the setup
  have cBt : (B * t + 2) * (B * t + 2) * (B * t + 2) ≤ 27 * Q ^ 3 := by
    have e : B * t + 2 ≤ 3 * Q := by omega
    calc (B * t + 2) * (B * t + 2) * (B * t + 2) ≤ (3 * Q) * (3 * Q) * (3 * Q) :=
          Nat.mul_le_mul (Nat.mul_le_mul e e) e
      _ = 27 * Q ^ 3 := by ring
  have cB2 : B * (18 * t + 7) ≤ 25 * Q ^ 2 := by
    have : B * (18 * t + 7) = 18 * (B * t) + 7 * B := by ring
    omega
  have cJ2 : J * (18 * (2 * t) + 7) ≤ 25 * Q ^ 2 := by
    have : J * (18 * (2 * t) + 7) = 18 * (J * (2 * t)) + 7 * J := by ring
    omega
  have cJW : J * (2 * t) * (18 * twMax t s + 7) ≤ 25 * Q ^ 2 := by
    have := Nat.mul_le_mul hJt (show 18 * twMax t s + 7 ≤ 25 * Q by omega)
    have e : Q * (25 * Q) = 25 * Q ^ 2 := by ring
    omega
  have hA : costA t J B ≤ 30000 * Q ^ 3 := by
    unfold costA
    have : 1000 * (B * t + 2) * (B * t + 2) * (B * t + 2) = 1000 * ((B * t + 2) * (B * t + 2) * (B * t + 2)) := by ring
    omega
  have hB' : costB t s J ≤ 2000 * Q ^ 2 := by unfold costB; omega
  have hC : costC t s J ≤ 1000 * Q := by unfold costC UnionMachine.BinW.binCost; omega
  have hset : setupCost t s J B ≤ 40000 * Q ^ 3 := by unfold setupCost; omega
  -- the level body
  have ctw : twCost t s J ≤ 72000 * Q ^ 2 := by
    unfold twCost
    have e : t + s + J + 2 ^ J + 2 ≤ 6 * Q := by omega
    have := Nat.mul_le_mul e e
    have e2 : 6 * Q * (6 * Q) = 36 * Q ^ 2 := by ring
    have e3 : 2000 * (t + s + J + 2 ^ J + 2) * (t + s + J + 2 ^ J + 2) = 2000 * ((t + s + J + 2 ^ J + 2) * (t + s + J + 2 ^ J + 2)) := by ring
    omega
  have cmu : mulUCost (wdOf t s J) (twMax t s) ≤ 302 * Q ^ 2 := by
    unfold mulUCost
    have := Nat.mul_le_mul (show twMax t s + 3 ≤ 4 * Q by omega) (show 41 * wdOf t s J + 30 ≤ 71 * Q by omega)
    have e : 4 * Q * (71 * Q) = 284 * Q ^ 2 := by ring
    omega
  have cpw : powUCost (wdOf t s J) (twMax t s) (2 * t) ≤ 700 * Q ^ 3 := by
    unfold powUCost
    have := Nat.mul_le_mul (show 2 * t ≤ 2 * Q by omega) (show mulUCost (wdOf t s J) (twMax t s) + 4 ≤ 306 * Q ^ 2 by omega)
    have e : 2 * Q * (306 * Q ^ 2) = 612 * Q ^ 3 := by ring
    omega
  have cj : jCost (wdOf t s J) t s J ≤ 73000 * Q ^ 3 := by unfold jCost; omega
  have cem : emitCostB (wdOf t s J) ≤ 120 * Q ^ 2 := by
    unfold emitCostB
    have := Nat.mul_le_mul hwd (show 20 * wdOf t s J + 42 ≤ 62 * Q by omega)
    have e : Q * (62 * Q) = 62 * Q ^ 2 := by ring
    omega
  have cl : lCost (wdOf t s J) t s J ≤ 1800000 * Q ^ 4 := by
    unfold lCost
    have := Nat.mul_le_mul (show 8 * (J + 2) ≤ 24 * Q by omega) (show jCost (wdOf t s J) t s J + 30 ≤ 73030 * Q ^ 3 by omega)
    have e : 24 * Q * (73030 * Q ^ 3) = 1752720 * Q ^ 4 := by ring
    omega
  have cloop : (J + 1) * (lCost (wdOf t s J) t s J + 2) + 1 ≤ 3700000 * Q ^ 5 := by
    have := Nat.mul_le_mul (show J + 1 ≤ 2 * Q by omega) (show lCost (wdOf t s J) t s J + 2 ≤ 1800002 * Q ^ 4 by omega)
    have e : 2 * Q * (1800002 * Q ^ 4) = 3600004 * Q ^ 5 := by ring
    omega
  have ctear : tearCost t s J B ≤ 100 * Q := by unfold tearCost; omega
  have ccap : capB t s J B ≤ 6000 * Q ^ 2 := by
    unfold capB
    have := Nat.mul_le_mul (Nat.mul_le_mul (show 2 ≤ 2 by omega) (show B * t + 2 ≤ 3 * Q by omega)) (show B * t + 2 ≤ 3 * Q by omega)
    have e : 2 * (3 * Q) * (3 * Q) = 18 * Q ^ 2 := by ring
    omega
  unfold b2Cost
  omega

/-- **Every size of B2's run below `Q = 200·(kwT + 1)^4`.** -/
theorem q_facts (D : C4H.HashData) :
    1 ≤ 200 * (kwT D + 1) ^ 4 ∧ D.MP.t ≤ 200 * (kwT D + 1) ^ 4 ∧ D.MP.J ≤ 200 * (kwT D + 1) ^ 4 ∧
    D.MP.Bstar ≤ 200 * (kwT D + 1) ^ 4 ∧ Nat.sqrt (D.MP.t * D.MP.Bstar) ≤ 200 * (kwT D + 1) ^ 4 ∧
    D.MP.Bstar * D.MP.t ≤ 200 * (kwT D + 1) ^ 4 ∧ D.MP.J * (2 * D.MP.t) ≤ 200 * (kwT D + 1) ^ 4 ∧
    twMax D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) ≤ 200 * (kwT D + 1) ^ 4 ∧
    wdOf D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J ≤ 200 * (kwT D + 1) ^ 4 ∧
    2 ^ (D.MP.J + 1) ≤ 200 * (kwT D + 1) ^ 4 := by
  set Y := kwT D + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  have ht : D.MP.t ≤ Y := by rw [hY]; unfold kwT; omega
  have hJ : D.MP.J ≤ Y := by rw [hY]; unfold kwT; omega
  have hB : D.MP.Bstar ≤ Y := by rw [hY]; unfold kwT; omega
  have hR : D.MP.refMod + 1 ≤ Y := by rw [hY]; unfold kwT; omega
  have y2 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) Y
  have y24 : Y ^ 2 ≤ Y ^ 4 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hBt : D.MP.Bstar * D.MP.t ≤ Y ^ 2 := by
    have := Nat.mul_le_mul hB ht; rw [pow_two]; exact this
  have htB : D.MP.t * D.MP.Bstar ≤ Y ^ 2 := by rw [Nat.mul_comm]; exact hBt
  have hs : Nat.sqrt (D.MP.t * D.MP.Bstar) ≤ Y ^ 2 := (Nat.sqrt_le_self _).trans htB
  have hJt : D.MP.J * (2 * D.MP.t) ≤ 2 * Y ^ 2 := by
    have := Nat.mul_le_mul hJ (show 2 * D.MP.t ≤ 2 * Y by omega)
    have e : Y * (2 * Y) = 2 * Y ^ 2 := by ring
    omega
  have hW : twMax D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) ≤ 76 * Y ^ 2 := by unfold twMax; omega
  have hwd : wdOf D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J ≤ 153 * Y ^ 4 := by
    unfold wdOf
    have := Nat.mul_le_mul hJt hW
    have e : 2 * Y ^ 2 * (76 * Y ^ 2) = 152 * Y ^ 4 := by ring
    have : 1 ≤ Y ^ 4 := Nat.one_le_pow _ _ hY1
    omega
  have h2 : 2 ^ (D.MP.J + 1) ≤ Y := by
    have hl := Filters.MajorantParams.J_lt_ell0 D.MP
    have e1 : 2 ^ (D.MP.J + 1) ≤ 2 ^ D.MP.ell0 := Nat.pow_le_pow_right (by norm_num) hl
    have e2 := PrimT.W6.fp_split D.MP.ell0
    have e3 : D.MP.refMod = GF.firstPrimitive D.MP.ell0 := rfl
    omega
  refine ⟨by have : 1 ≤ Y ^ 4 := Nat.one_le_pow _ _ hY1; omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega⟩

/-- B2's constant. -/
def kB2 : ℕ := 30000000 * 200 ^ 6

theorem b2_le (D : C4H.HashData) (cap : ℕ) :
    2 * (b2Cost D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J D.MP.Bstar +
      capB D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J D.MP.Bstar) + 2 ≤
      kB2 * (kwS D cap + 1) ^ 2 + kB2 * (kwT D + 1) ^ 24 := by
  obtain ⟨q1, qt, qJ, qB, qs, qBt, qJt, qW, qwd, q2⟩ := q_facts D
  have hb := b2_bound _ _ _ _ _ q1 qt qJ qB qs qBt qJt qW qwd q2
  have e : (200 * (kwT D + 1) ^ 4) ^ 6 = 200 ^ 6 * (kwT D + 1) ^ 24 := by ring
  rw [e] at hb
  have y1 : 1 ≤ (kwT D + 1) ^ 24 := Nat.one_le_pow _ _ (by omega)
  unfold kB2
  have : 0 ≤ 30000000 * 200 ^ 6 * (kwS D cap + 1) ^ 2 := Nat.zero_le _
  nlinarith

/-- **B2** (the cleared weights' word `wtWord (wsOf MP)`). -/
noncomputable def partB2 : PartB2 where
  x := 52
  s := _
  M := partM (no := 1) (ni := 3) (ns := 5) (nr := 48) (x := 52) (by norm_num) (by norm_num) b2P
  cost := fun D _ => 2 * (b2Cost D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J D.MP.Bstar +
      capB D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J D.MP.Bstar) + 2
  K := kB2
  Dg := 24
  cost_le := b2_le
  run := fun D cap => by
    obtain ⟨τ, hw, hc, hv, h0, hst, hP, hC⟩ := b2_core D cap
    refine part_run (no := 1) (ni := 3) (ns := 5) (nr := 48) (x := 52) (by norm_num) (by norm_num) (by norm_num) oB2 iB2
      b2P D cap (capB D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J D.MP.Bstar) τ
      (b2Cost D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J D.MP.Bstar +
        capB D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J D.MP.Bstar)
      (WExec.mono hw (Nat.le_add_right _ _)) hc hv (Nat.le_add_left _ _) (fun j => ?_) (fun k => ?_) (fun i hi => ?_)
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      show τ.st 0 = _
      rw [h0, outL_word, frame_prs]; rfl
    · have hk := k.isLt
      rw [hst _ (fun e => by have := congrArg Fin.val e; simp at this) (fun e => by have := congrArg Fin.val e; simp at this; omega)
        (fun e => by have := congrArg Fin.val e; simp at this; omega)]
      show stIn (no := 1) iB2 D cap _ = _
      unfold stIn
      rw [dif_pos (by simp; omega)]
      congr 2; apply Fin.ext; simp
    · have hi6 := i.isLt
      have hwd : 2 * wdOf D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J + 1 ≤
          capB D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J D.MP.Bstar := by
        unfold capB
        generalize 2 * (D.MP.Bstar * D.MP.t + 2) * (D.MP.Bstar * D.MP.t + 2) = Q1
        generalize 2 ^ (D.MP.J + 1) = P1
        omega
      by_cases h4 : i.val = 4
      · have e : i = sP := Fin.ext h4
        subst e
        exact ⟨_, by omega, hP⟩
      · have e : i = sC := Fin.ext (by show i.val = 5; omega)
        subst e
        exact ⟨_, by omega, hC⟩

end NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
