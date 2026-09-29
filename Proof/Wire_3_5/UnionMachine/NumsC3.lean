import Proof.Wire_3_5.UnionMachine.NumsC2

/-! # NW phase (c), part 3: the run after the front (`k`, `e`, `T_f`, the cleaning, the rewind)

From a state with `n` in `rN`, the mode bit in `rM` and every other register `0`, the head of `sIn` at `h ≤ T_f`, the
rest of `cProg` leaves `e = n − k` in `rE`, `T_f = KT·(n+2)^{ZT}` in `rT`, every other register as before (`0`), and the
head back at `0` (`rest_run`), within `restCost`.

* `vne`, `mem_rsC`, `rsC_roles`, `restCost`, **`rest_run`**.

Paper quantities of the main type: the shift `n − k` and the width `T_f` (P3:3044-3048, P3:1188-1189). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsC
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2

theorem vne {a b : Fin LNR} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

theorem starBlk_val (j : Fin 20) : (starBlk j).val = 480 + j.val := rfl
theorem g_val (j : Fin 10) : (g j).val = 470 + j.val := rfl

theorem mem_rsC (q : Fin LNR) : q ∈ rsC ↔ (∃ j, q = starBlk j) ∨ (∃ j, q = g j) := by
  unfold rsC
  simp only [List.mem_append, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr ⟨j, rfl⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr ⟨j, rfl⟩

/-- The listed registers avoid the roles. -/
theorem rsC_roles (q : Fin LNR) (hq : q ∈ rsC) : q ≠ rN ∧ q ≠ rM ∧ q ≠ rE ∧ q ≠ rT ∧ q ≠ rV := by
  rcases (mem_rsC q).1 hq with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have := j.isLt
    refine ⟨vne ?_, vne ?_, vne ?_, vne ?_, vne ?_⟩ <;> rw [starBlk_val] <;> simp [rN, rM, rE, rT, rV] <;> omega
  · have := j.isLt
    refine ⟨vne ?_, vne ?_, vne ?_, vne ?_, vne ?_⟩ <;> rw [g_val] <;> simp [rN, rM, rE, rT, rV] <;> omega

/-- The rest's steps. -/
def restCost (n cr k KT ZT Tf : ℕ) : ℕ :=
  (18 * n + 3) + 1 + (StarNums.starCost n cr 0 + 1 + ((18 * n + 3) + 1 + ((30 * k + 10) + 1 + (4 * KT + 1 +
    ((18 * n + 3) + 1 + (4 * 2 + 1 + (ZT * (60 * (Tf + 1) * (n + 2 + 1) + 1) + 1 + (rsC.length * (3 * (n + 2) + 2) + 1 +
    ((18 * Tf + 3) + 1 + (5 * Tf + 1))))))))))

theorem sb_ne (j : Fin 20) : starBlk j ≠ rN ∧ starBlk j ≠ rM ∧ starBlk j ≠ rE ∧ starBlk j ≠ rT :=
  let h := rsC_roles (starBlk j) ((mem_rsC _).2 (Or.inl ⟨j, rfl⟩)); ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem g_ne (j : Fin 10) : g j ≠ rN ∧ g j ≠ rM ∧ g j ≠ rE ∧ g j ≠ rT :=
  let h := rsC_roles (g j) ((mem_rsC _).2 (Or.inr ⟨j, rfl⟩)); ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem sb_g (i : Fin 20) (j : Fin 10) : starBlk i ≠ g j := vne (by rw [starBlk_val, g_val]; have := j.isLt; omega)

theorem sb_inj {i j : Fin 20} (h : i ≠ j) : starBlk i ≠ starBlk j := starBlk.injective.ne h

theorem g_inj {i j : Fin 10} (h : i ≠ j) : g i ≠ g j := vne (by rw [g_val, g_val]; exact fun e => h (Fin.ext (by omega)))

section Star
variable {ns nr : ℕ}

/-- `starOut` changes the block only. -/
theorem starOut_off (σ : WState ns nr) (S : Fin 20 ↪ Fin nr) (P : Shared.StarParams) (fe : ℕ) (q : Fin nr)
    (hq : ∀ j, q ≠ S j) : (StarNums.starOut σ S P fe).val q = σ.val q := by
  unfold StarNums.starOut
  simp [hq]

theorem starOut_st (σ : WState ns nr) (S : Fin 20 ↪ Fin nr) (P : Shared.StarParams) (fe : ℕ) :
    (StarNums.starOut σ S P fe).st = σ.st ∧ (StarNums.starOut σ S P fe).sh = σ.sh ∧
      (StarNums.starOut σ S P fe).cell = σ.cell := by
  unfold StarNums.starOut; simp

theorem starOut_k (σ : WState ns nr) (S : Fin 20 ↪ Fin nr) (P : Shared.StarParams) (fe : ℕ) :
    (StarNums.starOut σ S P fe).val (S 9) = P.k := by
  unfold StarNums.starOut
  simp [S.injective.ne (show (9 : Fin 20) ≠ 10 by decide)]

/-- Every block value of `starOut` is at most `n + 2` (from a block holding `n` and zeros). -/
theorem starOut_small (σ : WState ns nr) (S : Fin 20 ↪ Fin nr) (P : Shared.StarParams)
    (h0 : σ.val (S 0) = P.n) (hz : ∀ i : Fin 20, i ≠ 0 → σ.val (S i) = 0) (j : Fin 20) :
    (StarNums.starOut σ S P 0).val (S j) ≤ P.n + 2 := by
  have hk : P.k ≤ P.n := NumsX.rs_le P
  have hs : P.s ≤ P.k := by
    show P.s ≤ P.r * P.s
    exact Nat.le_mul_of_pos_left _ P.r_pos
  have hb : P.b ≤ P.n := (Nat.le_mul_of_pos_left _ P.r_pos).trans P.r_mul_b_le
  have hr : P.r ≤ P.n := by have := P.four_r_le_n; omega
  have hsr : P.s * (P.r / 2) ≤ P.k := by
    show P.s * (P.r / 2) ≤ P.r * P.s
    calc P.s * (P.r / 2) ≤ P.s * P.r := Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
      _ = P.r * P.s := Nat.mul_comm _ _
  have hL : Nat.clog 2 (P.n + 2) ≤ P.n + 2 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  unfold StarNums.starOut
  simp only [WState.setv_val, Function.update_apply]
  have hne : ∀ {a b : Fin 20}, a ≠ b → S a ≠ S b := fun h => S.injective.ne h
  by_cases h0' : j = 0
  · subst h0'
    simp [hne (show (0 : Fin 20) ≠ 10 by decide), hne (show (0 : Fin 20) ≠ 9 by decide),
      hne (show (0 : Fin 20) ≠ 8 by decide), hne (show (0 : Fin 20) ≠ 7 by decide),
      hne (show (0 : Fin 20) ≠ 6 by decide), hne (show (0 : Fin 20) ≠ 5 by decide),
      hne (show (0 : Fin 20) ≠ 4 by decide), hne (show (0 : Fin 20) ≠ 3 by decide),
      hne (show (0 : Fin 20) ≠ 1 by decide), h0]
  · have hzj := hz j h0'
    split_ifs <;> omega

end Star

/-- **The rest of phase (c)'s program** (after reading `n` and the mode bit). -/
def restProg (x cr KT ZT : ℕ) : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR rN (starBlk 0) (g 4))
  (.seq (StarNums.starNumsM cr 0 starBlk)
  (.seq (FinalPass.Hash4.wcopyR rN rE (g 4))
  (.seq (UnaryArith.subW RS)
  (.seq (StarNums.incN rT KT)
  (.seq (FinalPass.Hash4.wcopyR rN (g 6) (g 4))
  (.seq (StarNums.incN (g 6) 2)
  (.seq (powN R6 ZT)
  (.seq (clearL rsC)
  (.seq (FinalPass.Hash4.wcopyR rT (g 8) (g 4))
  (WM.rewind (sIn x) (g 8)))))))))))

theorem cProg_eq (x cr KT ZT : ℕ) : cProg x cr KT ZT =
    .seq (ParseNat.readNatM true (sIn x) (g 0) (g 1) rN (g 2) (g 3))
      (.seq (.fwd (sIn x)) (.seq (.ifs (sIn x) (.inc rM) .skip) (restProg x cr KT ZT))) := rfl

end NearCubicWires.WireExponent3_5.UnionMachine.NumsC
