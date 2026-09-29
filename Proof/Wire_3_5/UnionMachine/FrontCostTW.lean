import Proof.Wire_3_5.UnionMachine.FrontCostRest

/-! # C6 front, the time (4): the table writer's cost (P3:3485-3491, 3669-3691)

With every register value, literal and `2^{cb}` at most `n`, the table writer's cost is at most a fixed numeral
times a fixed power of `n` (**`twCost_le`**): each block's four levels (`lvlCost_le`, `blockCost_le`), each magnitude's
block (`mbCost_le`), the three passes' per-clause costs (the position registers `posRegs`, `muRegs` stay below
`n² + n`), the literals' reads.

Paper quantity of the main type: the table writer's time against the input length. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCostTW
open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCostKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTW

theorem lvlCost_le (f : FrontTableRef.FK) (s zX zY rc c : ℕ) :
    lvlCost f s zX zY rc c ≤ (s + 1) * (rc + c + 24) + 21 * s + 21 * (zX + zY) + 20 + c := by
  have e : (s + 1) * (rc + c + 24) = s * (rc + c + 20 + 4) + (rc + c + 24) := by ring
  cases f <;> simp only [lvlCost, sCost] <;> omega

/-- The level bound. -/
def LB (s zX zY rc c : ℕ) : ℕ := (s + 1) * (rc + c + 24) + 21 * s + 21 * (zX + zY) + 20 + c

theorem LB_mono {s zX zY rc c c' : ℕ} (h : c ≤ c') : LB s zX zY rc c ≤ LB s zX zY rc c' := by
  unfold LB
  have := Nat.mul_le_mul_left (s + 1) (show rc + c + 24 ≤ rc + c' + 24 by omega)
  omega

theorem blockCost_le (B M s zX zY : ℕ) (pat : Fin 4 → FrontTableRef.FK) :
    blockCost B M s zX zY pat ≤ LB s zX zY (rsCost B) (LB s zX zY (rsCost B) (LB s zX zY (rsCost B)
      (LB s zX zY (rsCost B) (emitCost B M)))) := by
  unfold blockCost
  have h0 := lvlCost_le (pat 0) s zX zY (rsCost B) (emitCost B M)
  have h1 := (lvlCost_le (pat 1) s zX zY (rsCost B) _).trans (LB_mono h0)
  have h2 := (lvlCost_le (pat 2) s zX zY (rsCost B) _).trans (LB_mono h1)
  exact (lvlCost_le (pat 3) s zX zY (rsCost B) _).trans (LB_mono h2)

section Regs
variable {n : ℕ}

theorem mbCost_le (hn : 1 ≤ n) (B : ℕ) (v : Fin NR → ℕ) (Mx : Fin NR) (pat : Fin 4 → FrontTableRef.FK) (hB : B ≤ n)
    (hv : ∀ r, v r ≤ n) : mbCost B v Mx pat ≤ 10 ^ 12 * n ^ 12 := by
  have h1 := hv Mx
  have h2 := hv rSS
  have h3 := hv rXS
  have h4 := hv rYS
  have hb := blockCost_le B (v Mx) (v rSS) (v rXS) (v rYS) pat
  unfold mbCost
  unfold LB rsCost emitCost at hb
  exact np_fin hn (by c6np) (by norm_num) (by norm_num)

theorem costV_le (hn : 1 ≤ n) (B : ℕ) (v : Fin NR → ℕ) (hB : B ≤ n) (hv : ∀ r, v r ≤ n) :
    costV B v ≤ 10 ^ 14 * n ^ 12 := by
  have := fun Mx pat => mbCost_le hn B v Mx pat hB hv
  unfold costV
  have a1 := this rMb (FrontTableRef.patV true 0)
  have a2 := this rMc (FrontTableRef.patV true 1)
  have a3 := this rMa (FrontTableRef.patV true 2)
  have a4 := this rMb (FrontTableRef.patV false 0)
  have a5 := this rMd (FrontTableRef.patV false 1)
  have a6 := this rMe (FrontTableRef.patV false 2)
  exact np_fin hn (by c6np) (by norm_num) (by norm_num)

theorem costMu_le (hn : 1 ≤ n) (B : ℕ) (v : Fin NR → ℕ) (hB : B ≤ n) (hv : ∀ r, v r ≤ n) :
    costMu B v ≤ 10 ^ 14 * n ^ 12 := by
  have := fun Mx pat => mbCost_le hn B v Mx pat hB hv
  unfold costMu
  have a1 := this rMa (FrontTableRef.patMu 0)
  have a2 := this rMf (FrontTableRef.patMu 1)
  have a3 := this rMf (FrontTableRef.patMu 2)
  have a4 := this rMb (FrontTableRef.patMu 3)
  exact np_fin hn (by c6np) (by norm_num) (by norm_num)

end Regs

/-- Updated registers stay within a common bound. -/
theorem update_le (v : Fin NR → ℕ) (Z : ℕ) (hv : ∀ r, v r ≤ Z) (r0 : Fin NR) (a : ℕ) (ha : a ≤ Z) :
    ∀ r, Function.update v r0 a r ≤ Z := by
  intro r
  by_cases h : r = r0
  · subst h; simp; exact ha
  · rw [Function.update_of_ne h]; exact hv r

theorem posRegs_le (v : Fin NR → ℕ) (Z : ℕ) (hZ : 1 ≤ Z) (hv : ∀ r, v r ≤ Z) : ∀ r, posRegs v r ≤ Z * Z + Z := by
  have hv' : ∀ r, v r ≤ Z * Z + Z := fun r => (hv r).trans (by nlinarith)
  have hl := hv rLIT
  have hs := hv rSS
  have hd : v rLIT / 2 ≤ Z := (Nat.div_le_self _ _).trans hl
  have hZZ : 1 ≤ Z * Z := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hm : v rLIT % 2 ≤ Z * Z + Z := by have := Nat.mod_lt (v rLIT) (show 0 < 2 by norm_num); omega
  have hp : v rLIT / 2 * v rSS ≤ Z * Z := Nat.mul_le_mul hd hs
  unfold posRegs
  refine update_le _ _ (update_le _ _ (update_le _ _ (update_le _ _ (update_le _ _ (update_le _ _ hv' _ _ ?_) _ _ hm)
    _ _ (by omega)) _ _ (by nlinarith)) _ _ (by omega)) _ _ ?_
  · nlinarith
  · split_ifs <;> omega

theorem muRegs_le (v : Fin NR → ℕ) (Z : ℕ) (hZ : 1 ≤ Z) (hv : ∀ r, v r ≤ Z) (a b : ℕ) (ha : a ≤ Z) (hb : b ≤ Z) :
    ∀ r, muRegs v a b r ≤ Z * Z + Z := by
  have hv' : ∀ r, v r ≤ Z * Z + Z := fun r => (hv r).trans (by nlinarith)
  have hs := hv rSS
  have ha2 : a / 2 ≤ Z := (Nat.div_le_self _ _).trans ha
  have hb2 : b / 2 ≤ Z := (Nat.div_le_self _ _).trans hb
  have hZZ : 1 ≤ Z * Z := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hma : a % 2 ≤ Z * Z + Z := by have := Nat.mod_lt a (show 0 < 2 by norm_num); omega
  have hmb : b % 2 ≤ Z * Z + Z := by have := Nat.mod_lt b (show 0 < 2 by norm_num); omega
  have hpa : a / 2 * v rSS ≤ Z * Z := Nat.mul_le_mul ha2 hs
  have hpb : b / 2 * v rSS ≤ Z * Z := Nat.mul_le_mul hb2 hs
  unfold muRegs
  exact update_le _ _ (update_le _ _ (update_le _ _ (update_le _ _ (update_le _ _ (update_le _ _ hv' _ _
    (by nlinarith)) _ _ hma) _ _ (by omega)) _ _ (by nlinarith)) _ _ hmb) _ _ (by omega)

theorem getD_le (l : List ℕ) (n i : ℕ) (hl : ∀ x ∈ l, x ≤ n) : l.getD i 0 ≤ n := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simp
  | some x => simp only [Option.getD_some]; exact hl x (List.mem_of_getElem? h)

theorem rdCost_le (x : ℕ) : rdCost x ≤ (x + 3) * (80 * x + 120) := by
  unfold rdCost
  have h1 := FrontSemEv.nbl_le_self x
  have h2 := C1Cnt.pow_nbl_le x
  calc (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ (x + 3) * (40 * (2 * x + 2) + 40) :=
        Nat.mul_le_mul (by omega) (by omega)
    _ = (x + 3) * (80 * x + 120) := by ring

section Clauses
variable {n : ℕ} (hn : 1 ≤ n) (Bn : ℕ) (v0 : Fin NR → ℕ) (lits : List ℕ) (hB : Bn ≤ n) (hv : ∀ r, v0 r ≤ n)
  (hl : ∀ x ∈ lits, x ≤ n)
include hn hB hv hl

theorem cVf_le (i : ℕ) : FrontSemTW.cVf Bn v0 lits i ≤ 10 ^ 18 * n ^ 26 := by
  have ha : litA lits i ≤ n := getD_le lits n (2 * i) hl
  have hb : litB lits i ≤ n := getD_le lits n (2 * i + 1) hl
  have hs := hv rSS
  have hy := hv rSYS
  have hm1 : 1 ≤ n * n + n := by nlinarith
  have hB' : Bn ≤ n * n + n := hB.trans (by nlinarith)
  have hr1 := posRegs_le (Function.update (Function.update v0 rL1 (litB lits i)) rLIT (litA lits i)) n hn
    (update_le _ n (update_le v0 n hv rL1 (litB lits i) hb) rLIT (litA lits i) ha)
  have hr2 := posRegs_le (Function.update v0 rLIT (litB lits i)) n hn (update_le v0 n hv rLIT (litB lits i) hb)
  have c1 := costV_le hm1 Bn (posRegs (Function.update (Function.update v0 rL1 (litB lits i)) rLIT (litA lits i))) hB'
    hr1
  have c2 := costV_le hm1 Bn (posRegs (Function.update v0 rLIT (litB lits i))) hB' hr2
  have hnn : n * n + n ≤ 2 * n ^ 2 := by nlinarith
  unfold FrontSemTW.cVf
  exact np_fin hn (by c6np) (by norm_num) (by norm_num)

theorem cQf_le (i : ℕ) : FrontSemTW.cQf Bn v0 lits i ≤ 10 ^ 18 * n ^ 26 := by
  have ha : litA lits i ≤ n := getD_le lits n (2 * i) hl
  have hb : litB lits i ≤ n := getD_le lits n (2 * i + 1) hl
  have hs := hv rSS
  have hy := hv rSYS
  have hm1 : 1 ≤ n * n + n := by nlinarith
  have hB' : Bn ≤ n * n + n := hB.trans (by nlinarith)
  have hr1 := posRegs_le (Function.update (Function.update v0 rL1 (litB lits i)) rLIT (litA lits i)) n hn
    (update_le _ n (update_le v0 n hv rL1 (litB lits i) hb) rLIT (litA lits i) ha)
  have hr2 := posRegs_le (Function.update v0 rLIT (litB lits i)) n hn (update_le v0 n hv rLIT (litB lits i) hb)
  have c1 := mbCost_le hm1 Bn (posRegs (Function.update (Function.update v0 rL1 (litB lits i)) rLIT (litA lits i))) rMb
    (FrontTableRef.patQ 0) hB' hr1
  have c2 := mbCost_le hm1 Bn (posRegs (Function.update v0 rLIT (litB lits i))) rMb (FrontTableRef.patQ 0) hB' hr2
  have hnn : n * n + n ≤ 2 * n ^ 2 := by nlinarith
  unfold FrontSemTW.cQf
  exact np_fin hn (by c6np) (by norm_num) (by norm_num)

theorem cMf_le (i : ℕ) : FrontSemTW.cMf Bn v0 lits i ≤ 10 ^ 18 * n ^ 26 := by
  have ha : litA lits i ≤ n := getD_le lits n (2 * i) hl
  have hb : litB lits i ≤ n := getD_le lits n (2 * i + 1) hl
  have hs := hv rSS
  have hm1 : 1 ≤ n * n + n := by nlinarith
  have hB' : Bn ≤ n * n + n := hB.trans (by nlinarith)
  have hr := muRegs_le v0 n hn hv (litA lits i) (litB lits i) ha hb
  have c1 := costMu_le hm1 Bn (muRegs v0 (litA lits i) (litB lits i)) hB' hr
  have hnn : n * n + n ≤ 2 * n ^ 2 := by nlinarith
  unfold FrontSemTW.cMf
  exact np_fin hn (by c6np) (by norm_num) (by norm_num)

/-- **The table writer's cost.** -/
theorem twCost_le (cb : ℕ) (hcb : 2 ^ cb ≤ n) : FrontSemTW.twCost Bn v0 lits cb ≤ 10 ^ 22 * n ^ 28 := by
  have hbig := hv rBIG
  have s1 : FrontSemTW.supR (FrontSemTW.cVf Bn v0 lits) (2 ^ cb) ≤ 10 ^ 18 * n ^ 26 :=
    FrontSemFold.supR_le _ _ _ (fun i _ => cVf_le hn Bn v0 lits hB hv hl i)
  have s2 : FrontSemTW.supR (FrontSemTW.cQf Bn v0 lits) (2 ^ cb) ≤ 10 ^ 18 * n ^ 26 :=
    FrontSemFold.supR_le _ _ _ (fun i _ => cQf_le hn Bn v0 lits hB hv hl i)
  have s3 : FrontSemTW.supR (FrontSemTW.cMf Bn v0 lits) (2 ^ cb) ≤ 10 ^ 18 * n ^ 26 :=
    FrontSemFold.supR_le _ _ _ (fun i _ => cMf_le hn Bn v0 lits hB hv hl i)
  have s4 : (lits.map rdCost).foldr max 0 ≤ (n + 3) * (80 * n + 120) := by
    refine FrontSemFold.foldr_max_le _ _ (fun x hx => ?_)
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have := hl y hy
    exact (rdCost_le y).trans (Nat.mul_le_mul (by omega) (by omega))
  have hnn : n ≤ n := le_rfl
  unfold FrontSemTW.twCost
  exact np_fin hn (by c6np) (by norm_num) (by norm_num)

end Clauses

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCostTW
