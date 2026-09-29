import Proof.Wire_3_5.Selection.GatePre7

/-! # C1.4: the gate routine (P3:1339-1358)

Paper: "Enumerate its `2^k` error rows. For each gate and row, the four threshold predicates have integer scores of
the form `a_j(z_L) + b_j(z_R)` [...] Enumerate each half's score vectors. For each of the sixteen corner patterns,
count pairs satisfying its four weak inequalities [...] Sum its exact count" (P3:1339-1358). The gate routine
`gateW`: the preamble (`pre`), the one-dimensional phase (`ACC := Yh − Yl`), the level phase (`ACC := accFold …`, the
gate's row count at the coset by `gateRows_total`), `TX := TX + ACC`, the preamble's registers back to `0` (`gClr`).
Main declarations: `gateW`, `slW`, `gateNeed`, `gateCost`, **`gateW_spec`**: the routine meets C1.4's interface
`GateSpec`. Paper quantity: a gate's row counts at a coset. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat

variable {ns nr : ℕ}

/-! ## The preamble's registers back to zero -/

/-- The preamble's registers back to `0`. -/
def gClr (R : Fin 48 → Fin nr) : WM ns nr :=
  .seq (WM.clear (R 15)) (.seq (WM.clear (R 21)) (.seq (WM.clear (R 23)) (.seq (WM.clear (R 24))
    (.seq (WM.clear (R 25)) (.seq (WM.clear (R 26)) (.seq (WM.clear (R 31)) (.seq (WM.clear (R 32))
      (WM.clear (R 35)))))))))

/-- The state after `gClr`. -/
def gClrSt (R : Fin 48 → Fin nr) (τ : WState ns nr) : WState ns nr :=
  ((((((((τ.setv (R 15) 0).setv (R 21) 0).setv (R 23) 0).setv (R 24) 0).setv (R 25) 0).setv (R 26) 0).setv (R 31)
    0).setv (R 32) 0).setv (R 35) 0

/-- The cost of `gClr` at the registers' values. -/
def gClrCost (a15 a21 a23 a24 a25 a26 a31 a32 a35 : ℕ) : ℕ :=
  3 * a15 + 1 + 1 + (3 * a21 + 1 + 1 + (3 * a23 + 1 + 1 + (3 * a24 + 1 + 1 + (3 * a25 + 1 + 1 + (3 * a26 + 1 + 1 +
    (3 * a31 + 1 + 1 + (3 * a32 + 1 + 1 + (3 * a35 + 1))))))))

theorem gClr_spec (R : Fin 48 → Fin nr) (hR : Function.Injective R) (cap : ℕ) (τ : WState ns nr)
    (a15 a21 a23 a24 a25 a26 a31 a32 a35 : ℕ) (h15 : τ.val (R 15) = a15) (h21 : τ.val (R 21) = a21)
    (h23 : τ.val (R 23) = a23) (h24 : τ.val (R 24) = a24) (h25 : τ.val (R 25) = a25) (h26 : τ.val (R 26) = a26)
    (h31 : τ.val (R 31) = a31) (h32 : τ.val (R 32) = a32) (h35 : τ.val (R 35) = a35)
    (c15 : a15 ≤ cap) (c21 : a21 ≤ cap) (c23 : a23 ≤ cap) (c24 : a24 ≤ cap) (c25 : a25 ≤ cap) (c26 : a26 ≤ cap)
    (c31 : a31 ≤ cap) (c32 : a32 ≤ cap) (c35 : a35 ≤ cap) :
    WExec cap (gClr R) τ (gClrSt R τ) (gClrCost a15 a21 a23 a24 a25 a26 a31 a32 a35) := by
  have e1 := wclear_spec cap (R 15) a15 τ h15 (by rw [h15]; exact c15)
  have q2 : (τ.setv (R 15) 0).val (R 21) = a21 := by simp [Function.update_apply, hR.eq_iff, h21]
  have e2 := wclear_spec cap (R 21) a21 (τ.setv (R 15) 0) q2 (by rw [q2]; exact c21)
  have q3 : ((τ.setv (R 15) 0).setv (R 21) 0).val (R 23) = a23 := by simp [Function.update_apply, hR.eq_iff, h23]
  have e3 := wclear_spec cap (R 23) a23 ((τ.setv (R 15) 0).setv (R 21) 0) q3 (by rw [q3]; exact c23)
  have q4 : (((τ.setv (R 15) 0).setv (R 21) 0).setv (R 23) 0).val (R 24) = a24 := by simp [Function.update_apply,
      hR.eq_iff, h24]
  have e4 := wclear_spec cap (R 24) a24 (((τ.setv (R 15) 0).setv (R 21) 0).setv (R 23) 0) q4 (by rw [q4]; exact c24)
  have q5 : ((((τ.setv (R 15) 0).setv (R 21) 0).setv (R 23) 0).setv (R 24) 0).val (R 25) = a25 := by
      simp [Function.update_apply, hR.eq_iff, h25]
  have e5 := wclear_spec cap (R 25) a25 ((((τ.setv (R 15) 0).setv (R 21) 0).setv (R 23) 0).setv (R 24) 0) q5 (by
      rw [q5]; exact c25)
  have q6 : (((((τ.setv (R 15) 0).setv (R 21) 0).setv (R 23) 0).setv (R 24) 0).setv (R 25) 0).val (R 26) = a26 := by
      simp [Function.update_apply, hR.eq_iff, h26]
  have e6 := wclear_spec cap (R 26) a26 (((((τ.setv (R 15) 0).setv (R 21) 0).setv (R 23) 0).setv (R 24) 0).setv (R
      25) 0) q6 (by rw [q6]; exact c26)
  have q7 : ((((((τ.setv (R 15) 0).setv (R 21) 0).setv (R 23) 0).setv (R 24) 0).setv (R 25) 0).setv (R 26) 0).val (R
      31) = a31 := by simp [Function.update_apply, hR.eq_iff, h31]
  have e7 := wclear_spec cap (R 31) a31 ((((((τ.setv (R 15) 0).setv (R 21) 0).setv (R 23) 0).setv (R 24) 0).setv (R
      25) 0).setv (R 26) 0) q7 (by rw [q7]; exact c31)
  have q8 : (((((((τ.setv (R 15) 0).setv (R 21) 0).setv (R 23) 0).setv (R 24) 0).setv (R 25) 0).setv (R 26) 0).setv
      (R 31) 0).val (R 32) = a32 := by simp [Function.update_apply, hR.eq_iff, h32]
  have e8 := wclear_spec cap (R 32) a32 (((((((τ.setv (R 15) 0).setv (R 21) 0).setv (R 23) 0).setv (R 24) 0).setv (R
      25) 0).setv (R 26) 0).setv (R 31) 0) q8 (by rw [q8]; exact c32)
  have q9 : ((((((((τ.setv (R 15) 0).setv (R 21) 0).setv (R 23) 0).setv (R 24) 0).setv (R 25) 0).setv (R 26) 0).setv
      (R 31) 0).setv (R 32) 0).val (R 35) = a35 := by simp [Function.update_apply, hR.eq_iff, h35]
  have e9 := wclear_spec cap (R 35) a35 ((((((((τ.setv (R 15) 0).setv (R 21) 0).setv (R 23) 0).setv (R 24) 0).setv
      (R 25) 0).setv (R 26) 0).setv (R 31) 0).setv (R 32) 0) q9 (by rw [q9]; exact c35)
  unfold gClr gClrSt gClrCost
  exact WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7 (WExec.seq
      e8 (e9))))))))

/-! ## The working lengths -/

/-- The one-dimensional joins' key count. -/
def keysY (P : StarParams) : ℕ := 2 * (2 ^ (P.s * hh P) * 2 ^ rw P) + 2 ^ (P.s * hh P) * 2 ^ lw P

/-- A level join's key count. -/
def keysL (P : StarParams) : ℕ := 2 ^ (P.s * hh P) * 2 ^ rw P + 2 ^ (P.s * hh P) * 2 ^ lw P

/-- The scratch stream `G j`'s working length. -/
def wlen (P : StarParams) (W : ℕ) (j : Fin 28) : ℕ :=
  if j.val = 4 ∨ j.val = 14 then 2 * (lw P + 1) + 1 else if j.val = 5 ∨ j.val = 15 then 2 * (P.s * hh P + 1) + 1
  else if j.val = 6 then lw P * (2 * W + 2) else if j.val = 7 then rw P * (2 * W + 2)
  else if j.val = 8 ∨ j.val = 9 then 2 * P.s + 1 else if j.val = 18 ∨ j.val = 19 then keysY P * (2 * W + 1) + 1
  else if j.val = 20 ∨ j.val = 21 then keysL P * (2 * W + 1) + 1 else if 26 ≤ j.val then 0 else 2 * W + 1

/-- **The working lengths** on the streams (`0` off the map). -/
def slW (G : Fin 28 → Fin (ns + 1)) (P : StarParams) (W : ℕ) (i : Fin (ns + 1)) : ℕ :=
  match (List.finRange 28).find? (fun j => decide (G j = i)) with
  | some j => wlen P W j
  | none => 0

theorem slW_G (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (P : StarParams) (W : ℕ) (j : Fin 28) :
    slW G P W (G j) = wlen P W j := by
  unfold slW
  cases h : (List.finRange 28).find? (fun j' => decide (G j' = G j)) with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd (by simp) (h j (List.mem_finRange j))
  | some j' =>
    have := List.find?_some h
    simp only [decide_eq_true_eq] at this
    dsimp only
    rw [hG this]

theorem mem_scS (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (j : Fin 28) (hj : 4 ≤ j.val) :
    G j ∈ (gateLayout G R).scS := by
  simp only [gateLayout, List.mem_map, List.mem_finRange, true_and]
  exact ⟨⟨j.val - 4, by omega⟩, congrArg G (Fin.ext (by show j.val - 4 + 4 = j.val; omega))⟩

theorem mem_scS_inv (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (i : Fin (ns + 1))
    (hi : i ∈ (gateLayout G R).scS) : ∃ j : Fin 28, 4 ≤ j.val ∧ G j = i := by
  simp only [gateLayout, List.mem_map, List.mem_finRange, true_and] at hi
  obtain ⟨a, rfl⟩ := hi
  exact ⟨⟨a.val + 4, by omega⟩, by show 4 ≤ a.val + 4; omega, rfl⟩

theorem mem_scR (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (j : Fin 48) (hj : 6 ≤ j.val) :
    R j ∈ (gateLayout G R).scR := by
  simp only [gateLayout, List.mem_map, List.mem_finRange, true_and]
  exact ⟨⟨j.val - 6, by omega⟩, congrArg R (Fin.ext (by show j.val - 6 + 6 = j.val; omega))⟩

/-! ## The ready state after the preamble -/

theorem wsets_self (σ : WState ns nr) (i : Fin (ns + 1)) (l : List Bool) (h : σ.st i = l) : σ.sets i l = σ := by
  apply WState.eq
  · rfl
  · funext j
    simp only [WState.sets_st, Function.update_apply]
    split_ifs with hj
    · subst hj; exact h.symm
    · rfl
  · rfl
  · rfl

theorem jst_self (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (W : ℕ) (σ0 : WState ns nr)
    (h17 : σ0.st (G 17) = frame (binary W 2)) (h23 : σ0.st (G 23) = frame (binary W 0))
    (h24 : σ0.st (G 24) = frame (binary W 0)) (h25 : σ0.st (G 25) = frame (binary W 0)) (h19 : σ0.val (R 19) = 0) :
    jst G R W σ0 (σ0.st (G 18)) (σ0.st (G 19)) (σ0.st (G 20)) (σ0.st (G 21)) 0 0 0 0 = σ0 := by
  unfold jst
  rw [wsets_self σ0 (G 18) _ rfl, wsets_self σ0 (G 19) _ rfl, wsets_self σ0 (G 20) _ rfl, wsets_self σ0 (G 21) _ rfl,
    wsets_self σ0 (G 23) _ h23, wsets_self σ0 (G 24) _ h24, wsets_self σ0 (G 25) _ h25, wsetv_zero σ0 (R 19) h19,
    wsets_self σ0 (G 17) _ (by simp [h17])]

theorem preSt_val (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (hR : Function.Injective R) (σ : WState ns nr)
    (P : StarParams) (W V : ℕ) (g : NormalizedThresholdGate P.n) (i : Fin 48) :
    (preSt G R σ P W V g).val (R i) =
      if i = 43 ∨ i = 42 then 0 else (constSt R σ W V (hh P) P.b P.s (fL P) (fR P)).val (R i) := by
  simp only [preSt, WState.setv_val, WState.sets_val, zwsSt_val, Function.update_apply, hR.eq_iff]
  by_cases h43 : i = 43
  · simp [h43]
  · by_cases h42 : i = 42
    · simp [h42]
    · simp [h43, h42]

set_option maxHeartbeats 1000000 in
/-- **The preamble's state is the joins' ready state.** -/
theorem preSt_ready (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr)
    (hR : Function.Injective R) (P : StarParams) (N W V : ℕ) (g : NormalizedThresholdGate P.n) (σ : WState ns nr)
    (hNS : σ.st (G 0) = frame (binary (P.r * P.s) N)) (hOF : σ.st (G 2) = frame (binary W (2 ^ V)))
    (hsh : ∀ i : Fin 28, σ.sh (G i) = 0) (r0 : σ.val (R 0) = hh P) (r1 : σ.val (R 1) = P.b) (r2 : σ.val (R 2) = P.s)
    (r3 : σ.val (R 3) = fL P) (r4 : σ.val (R 4) = fR P) (r5 : σ.val (R 5) = V + 1)
    (hz : ∀ i : Fin 48, 6 ≤ i.val → σ.val (R i) = 0) (hW : 2 * V + 3 ≤ W) :
    WReady G R P N W V g (preSt G R σ P W V g) := by
  obtain ⟨-, -, -, -, -, sz6, sz7, -⟩ := size_facts P
  have v := preSt_val G R hR σ P W V g
  have c := constSt_val R hR σ W V (hh P) P.b P.s (fL P) (fR P)
  exact {
    x0 := by simp [preSt, zwsSt, Function.update_apply, hG.eq_iff, sz6]
    u0 := by simp [preSt, zwsSt, Function.update_apply, hG.eq_iff, Nat.mul_comm (hh P) P.s]
    ci0 := by simp [preSt, zwsSt, Function.update_apply, hG.eq_iff]
    sy0 := by simp [preSt, zwsSt, Function.update_apply, hG.eq_iff]
    ac0 := by simp [preSt, zwsSt, Function.update_apply, hG.eq_iff]
    ac0' := by simp [preSt, zwsSt, Function.update_apply, hG.eq_iff]
    wv0 := by simp [preSt, zwsSt, Function.update_apply, hG.eq_iff]
    xp := ⟨0, by simp [preSt, zwsSt, Function.update_apply, hG.eq_iff, sz6]⟩
    up := ⟨0, by simp [preSt, zwsSt, Function.update_apply, hG.eq_iff, Nat.mul_comm (hh P) P.s]⟩
    ns := by simp [preSt, zwsSt, constSt_st, Function.update_apply, hG.eq_iff, hNS]
    wtl := by simp [preSt, zwsSt, constSt_st, Function.update_apply, hG.eq_iff]
    wtr := by simp [preSt, zwsSt, constSt_st, Function.update_apply, hG.eq_iff]
    tk := by simp [preSt, zwsSt, constSt_st, Function.update_apply, hG.eq_iff]
    ofs := by simp [preSt, zwsSt, constSt_st, Function.update_apply, hG.eq_iff, hOF]
    ht := by simp [preSt, zwsSt, Function.update_apply, hG.eq_iff]
    cnt := by simp [preSt, zwsSt, Function.update_apply, hG.eq_iff]
    heads := fun i => by simp [preSt, zwsSt_sh, constSt_sh, hsh i]
    rh := by rw [v, c]; simp [r0]
    rb := by rw [v, c]; simp [r1]
    rs := by rw [v, c]; simp [r2]
    rfL := by rw [v, c]; simp [r3]
    rfR := by rw [v, c]; simp [r4]
    rv := by rw [v, c]; simp [r5]
    ro := by rw [v, c]; simp
    rq := by rw [v, c]; simp <;> omega
    rW := by rw [v, c]; simp
    rW1 := by rw [v, c]; simp
    rs1 := by rw [v, c]; simp <;> omega
    rs0 := by rw [v, c]; simp <;> omega
    pxl := by rw [v, c]; simp [sz6]
    pu := by rw [v, c]; simp [Nat.mul_comm (hh P) P.s]
    pxr := by rw [v, c]; simp [sz7]
    zr := fun i hi => by
      have h6 : 6 ≤ i.val := by revert hi; revert i; decide
      have hn : i ≠ 15 ∧ i ≠ 21 ∧ i ≠ 23 ∧ i ≠ 24 ∧ i ≠ 25 ∧ i ≠ 26 ∧ i ≠ 31 ∧ i ≠ 32 ∧ i ≠ 35 := by
        revert hi; revert i; decide
      obtain ⟨n15, n21, n23, n24, n25, n26, n31, n32, n35⟩ := hn
      rw [v]
      by_cases h : i = 43 ∨ i = 42
      · rw [if_pos h]
      · rw [if_neg h, c]
        rw [not_or] at h
        simp [h.1, h.2, n15, n21, n23, n24, n25, n26, n31, n32, n35, hz i h6] }

/-! ## The state after the phases -/

/-- The state after the level phase and `TX := TX + ACC`. -/
def endSt (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (W V : ℕ) (σ0 : WState ns nr) (ky ky' kl kl' : List Bool)
    (a : ℕ) (t : List Bool) : WState ns nr :=
  ((jst G R W σ0 ky ky' kl kl' 0 a 0 (V + 1)).setv (R 19) 0).sets (G 3) t

section End
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (σ : WState ns nr) (P : StarParams) (W V : ℕ) (g : NormalizedThresholdGate P.n) (ky ky' kl kl' : List Bool)
variable (a : ℕ) (t : List Bool)

include hR in
theorem endSt_val (σ0 : WState ns nr) (i : Fin 48) :
    (endSt G R W V σ0 ky ky' kl kl' a t).val (R i) = if i = 19 then 0 else σ0.val (R i) := by
  by_cases h : i = 19 <;> simp [endSt, jst, Function.update_apply, hR.eq_iff, h]

theorem gate_st3 : (gClrSt R (endSt G R W V (preSt G R σ P W V g) ky ky' kl kl' a t)).st (G 3) = t := by
  simp [gClrSt, endSt]

theorem gate_st_other (i : Fin (ns + 1)) (hi : ∀ j : Fin 28, 3 ≤ j.val → i ≠ G j) :
    (gClrSt R (endSt G R W V (preSt G R σ P W V g) ky ky' kl kl' a t)).st i = σ.st i := by
  have n : ∀ j : Fin 28, 3 ≤ j.val → (i = G j) = False := fun j hj => eq_false (hi j hj)
  simp [gClrSt, endSt, jst, preSt, zwsSt, constSt_st, Function.update_apply, n 3 (by decide), n 4 (by decide), n 5
      (by decide), n 6 (by decide), n 7 (by decide), n 8 (by decide), n 9 (by decide), n 10 (by decide), n 11 (by
      decide), n 12 (by decide), n 13 (by decide), n 14 (by decide), n 15 (by decide), n 16 (by decide), n 17 (by
      decide), n 18 (by decide), n 19 (by decide), n 20 (by decide), n 21 (by decide), n 22 (by decide), n 23 (by
      decide), n 24 (by decide), n 25 (by decide)]

theorem gate_sh : (gClrSt R (endSt G R W V (preSt G R σ P W V g) ky ky' kl kl' a t)).sh = σ.sh := by
  simp [gClrSt, endSt, jst, preSt, zwsSt_sh, constSt_sh]

theorem gate_cell : (gClrSt R (endSt G R W V (preSt G R σ P W V g) ky ky' kl kl' a t)).cell = σ.cell := by
  simp [gClrSt, endSt, jst, preSt, zwsSt, constSt]

include hR in
theorem gate_val (hz : ∀ i : Fin 48, 6 ≤ i.val → σ.val (R i) = 0) :
    (gClrSt R (endSt G R W V (preSt G R σ P W V g) ky ky' kl kl' a t)).val = σ.val := by
  funext r
  by_cases hr : ∃ i : Fin 48, R i = r
  · obtain ⟨i, rfl⟩ := hr
    by_cases hs : i = 15 ∨ i = 21 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 31 ∨ i = 32 ∨ i = 35 ∨ i = 19 ∨ i = 42 ∨
        i = 43
    · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [gClrSt, endSt, jst, preSt, constSt, zwsSt_val, Function.update_apply, hR.eq_iff, hz]
    · simp only [not_or] at hs
      obtain ⟨n15, n21, n23, n24, n25, n26, n31, n32, n35, n19, n42, n43⟩ := hs
      simp [gClrSt, endSt, jst, preSt, constSt, zwsSt_val, Function.update_apply, hR.eq_iff, n15, n21, n23, n24, n25,
        n26, n31, n32, n35, n19, n42, n43]
  · have n : ∀ i : Fin 48, (r = R i) = False := fun i => eq_false (fun h => hr ⟨i, h.symm⟩)
    simp [gClrSt, endSt, jst, preSt, constSt, zwsSt_val, Function.update_apply, n]

set_option maxHeartbeats 1000000 in
include hG in
theorem gate_len (hky : ky.length = keysY P * (2 * W + 1) + 1) (hky' : ky'.length = keysY P * (2 * W + 1) + 1)
    (hkl : kl.length = keysL P * (2 * W + 1) + 1) (hkl' : kl'.length = keysL P * (2 * W + 1) + 1)
    (h26 : (σ.st (G 26)).length = 0) (h27 : (σ.st (G 27)).length = 0) (j : Fin 28) (hj : 4 ≤ j.val) :
    ((gClrSt R (endSt G R W V (preSt G R σ P W V g) ky ky' kl kl' a t)).st (G j)).length = wlen P W j := by
  obtain ⟨-, -, -, -, -, sz6, -, -⟩ := size_facts P
  have e : j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨
      j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 :=
      by revert hj; revert j; decide
  rcases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [gClrSt, endSt, jst, preSt, zwsSt, constSt_st, Function.update_apply, hG.eq_iff, wlen,
        RepairOrdinary.frame_length,
      tbl_length, recsL_length, recsR_length, hky, hky', hkl, hkl', h26, h27, sz6, Nat.mul_comm (hh P) P.s]

end End

/-! ## The routine -/

/-- **The gate routine**: the preamble, the two phases, `TX := TX + ACC`, the registers back. -/
def gateW (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) : WM ns nr :=
  .seq (pre G R) (.seq (phY G R) (.seq (phL G R) (.seq (addB (G 3) (G 24) (R 6) (R 7)) (gClr R))))

/-- The routine's cost. -/
def gateCost (P : StarParams) (W V : ℕ) : ℕ :=
  preCost P W V + 1 + (phYCost P W (keysY P) + 1 + (phLCost P W V (keysL P) + 1 + (41 * W + 3 + 1 +
    gClrCost (hh P) (W - (V + 1) - 1) W (W - 1) (2 * (V + 1) + 1) (W - (2 * (V + 1) + 1)) (1 * 2 ^ (hh P * P.b + fL P))
      (1 * 2 ^ (hh P * P.s)) (1 * 2 ^ (hh P * P.b + fR P)))))

/-- The routine's space need. -/
def gateNeed (P : StarParams) (W V : ℕ) : ℕ :=
  capKW P W + (2 * W + 4 * V + 2 ^ (hh P * P.b + fL P + 1) + 2 ^ (hh P * P.b + fR P + 1) + 2 ^ (hh P * P.s + 1) +
    hh P * P.b + hh P * P.s + hh P + P.b + P.s + fL P + fR P + 10) + ((P.n + 1) * (2 * W + 2) + 3) +
    (2 * (hh P * P.b + fL P + 1) + 2 * (hh P * P.s + 1) + 2 * P.s + 2 * W + 2) + (keysY P * (2 * W + 1) + 3) +
    (keysL P * (2 * W + 1) + 3) + (V + 2)

set_option maxHeartbeats 4000000 in
/-- **The gate routine meets C1.4's interface** (`GateSpec`): at a coset `N`, `TX` gains the gate's row count
`gateRows P σ g`; the scratch streams end at their working lengths; the heads, registers and cell come back. -/
theorem gateW_spec (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr)
    (hR : Function.Injective R) (cap : ℕ) :
    GateSpec cap (gateW G R) (gateLayout G R) (slW G) gateNeed gateCost := by
  intro σ P N W V g tx _hN hrd hTX hKB hW hnk hfit hcap
  unfold GateReady at hrd
  obtain ⟨hNS, hNSh, hGA, hGAh, hOF, r0, r1, r2, r3, r4, r5, hsc, hscR⟩ := hrd
  have hNS' : σ.st (G 0) = frame (binary (P.r * P.s) N) := hNS
  have hGA' : σ.st (G 1) = gateRec W g := hGA
  have hOF1 : σ.st (G 2) = frame (binary W (2 ^ V)) := hOF.1
  have hTX1 : σ.st (G 3) = frame (binary W tx) := hTX.1
  have r0' : σ.val (R 0) = hh P := r0
  have r1' : σ.val (R 1) = P.b := r1
  have r2' : σ.val (R 2) = P.s := r2
  have r3' : σ.val (R 3) = fL P := r3
  have r4' : σ.val (R 4) = fR P := r4
  have r5' : σ.val (R 5) = V + 1 := r5
  obtain ⟨sz1, sz2, sz3, sz4, sz5, sz6, sz7, sz8⟩ := size_facts P
  have hW1 : 1 ≤ W := by omega
  have hsh : ∀ i : Fin 28, σ.sh (G i) = 0 := by
    intro i
    have e : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i.val := by revert i; decide
    rcases e with rfl | rfl | rfl | rfl | h4
    · exact hNSh
    · exact hGAh
    · exact hOF.2
    · exact hTX.2
    · exact (hsc _ (mem_scS G R i h4)).2
  have hlen : ∀ j : Fin 28, 4 ≤ j.val → (σ.st (G j)).length ≤ wlen P W j := by
    intro j hj
    have h := (hsc _ (mem_scS G R j hj)).1
    rw [slW_G G hG] at h
    rcases h with h | h
    · rw [h]; exact Nat.zero_le _
    · exact h.le
  have hz : ∀ i : Fin 48, 6 ≤ i.val → σ.val (R i) = 0 := fun i hi => hscR _ (mem_scR G R i hi)
  have hθ : g.threshold.natAbs < 2 ^ V := by unfold KeyBound at hKB; omega
  unfold gateNeed at hcap
  have nn1 := Nat.zero_le (hh P * P.s)
  have nn2 := Nat.zero_le (hh P * P.b)
  have nn3 := Nat.zero_le ((P.n + 1) * (2 * W + 2))
  have nn4 := Nat.zero_le (keysY P * (2 * W + 1))
  have nn5 := Nat.zero_le (keysL P * (2 * W + 1))
  have nn6 := Nat.zero_le (2 ^ (hh P * P.b + fL P))
  have nn7 := Nat.zero_le (2 ^ (hh P * P.b + fR P))
  have nn8 := Nat.zero_le (2 ^ (hh P * P.s))
  have hmY : (lYh P g V N).length = keysY P := (lY_length P g V N).1
  have hmL : (lK1 P g V N 0).length = keysL P := (lK_length P g V N 0).1
  have hcapB : capKW P W ≤ cap := by omega
  -- the preamble
  have x1 := pre_spec G hG R hR P W V g cap σ hGA' hOF1 hsh r0' r1' r2' r3' r4' r5' hz
    (by simpa [wlen] using hlen 6 (by decide)) (by simpa [wlen] using hlen 7 (by decide))
    (fun i hi => by
      rcases hi with rfl | rfl <;> exact (hlen _ (by decide)).trans (le_of_eq (by simp [wlen, sz6])))
    (fun i hi => by
      rcases hi with rfl | rfl <;>
        exact (hlen _ (by decide)).trans (le_of_eq (by simp [wlen, Nat.mul_comm (hh P) P.s])))
    (fun i hi => by rcases hi with rfl | rfl <;> exact (hlen _ (by decide)).trans (le_of_eq (by simp [wlen])))
    (fun i hi => by
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact (hlen _ (by decide)).trans (le_of_eq (by simp [wlen])))
    hθ (by omega) (by omega) (by omega) (by omega)
  have hw := preSt_ready G hG R hR P N W V g σ hNS' hOF1 hsh r0' r1' r2' r3' r4' r5' hz hW
  have v0 := preSt_val G R hR σ P W V g
  have c0 := constSt_val R hR σ W V (hh P) P.b P.s (fL P) (fR P)
  have h19 : (preSt G R σ P W V g).val (R 19) = 0 := by rw [v0, c0]; simp [hz 19 (by decide)]
  have h46 : (preSt G R σ P W V g).val (R 46) = 0 := by rw [v0, c0]; simp [hz 46 (by decide)]
  have e0 := jst_self G R W (preSt G R σ P W V g) (by simp [preSt])
    (by simp [preSt, zwsSt, Function.update_apply, hG.eq_iff])
    (by simp [preSt, zwsSt, Function.update_apply, hG.eq_iff])
    (by simp [preSt, zwsSt, Function.update_apply, hG.eq_iff]) h19
  have st18 : ∀ j : Fin 28, (j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21) →
      (preSt G R σ P W V g).st (G j) = σ.st (G j) := by
    intro j hj
    rcases hj with rfl | rfl | rfl | rfl <;> simp [preSt, zwsSt, constSt_st, Function.update_apply, hG.eq_iff]
  -- the one-dimensional phase
  obtain ⟨ky2, ky2', hk1, hk2, x2⟩ := phY_spec G hG R hR P N W V g cap (preSt G R σ P W V g) hw hW hKB hcapB hnk
    ((preSt G R σ P W V g).st (G 18)) ((preSt G R σ P W V g).st (G 19)) ((preSt G R σ P W V g).st (G 20))
    ((preSt G R σ P W V g).st (G 21)) 0
    (by rw [st18 18 (by decide), keyStream_length W hW1, hmY]; simpa [wlen] using hlen 18 (by decide))
    (by rw [st18 19 (by decide), keyStream_length W hW1, hmY]; simpa [wlen] using hlen 19 (by decide))
    (by rw [keyStream_length W hW1, hmY]; omega)
  rw [e0] at x2
  -- the level phase
  have hyh := (Y_bounds G hG R hR P N W V g cap (preSt G R σ P W V g) hw hW hKB hcapB hnk).2.1
  obtain ⟨kl2, kl2', hk3, hk4, x3⟩ := phL_spec G hG R hR P N W V g cap (preSt G R σ P W V g) hw hW hKB hcapB hnk
    ky2 ky2' ((preSt G R σ P W V g).st (G 20)) ((preSt G R σ P W V g).st (G 21)) (Yh P g V N) (Yl P g V N) hyh
    (by rw [st18 20 (by decide), keyStream_length W hW1, hmL]; simpa [wlen] using hlen 20 (by decide))
    (by rw [st18 21 (by decide), keyStream_length W hW1, hmL]; simpa [wlen] using hlen 21 (by decide))
    h46 (by rw [keyStream_length W hW1, hmL]; omega) (by omega)
  have hgr := gateRows_total P g V N hKB
  -- TX := TX + ACC
  have x4 := addB_spec cap W (A := G 3) (B := G 24) (F := R 6) (R := R 7) (hG.ne (by decide)) (hR.ne (by decide))
    ((jst G R W (preSt G R σ P W V g) ky2 ky2' kl2 kl2' 0 (accFold (Yh P g V N) (Yl P g V N) (fun ℓ => cK3 P g V N ℓ
        - cK1 P g V N ℓ) (V + 1)) 0 (V + 1)).setv (R 19) 0) tx (accFold (Yh P g V N) (Yl P g V N) (fun ℓ => cK3 P g
        V N ℓ - cK1 P g V N ℓ) (V + 1))
    ⟨by simp [jst, preSt, zwsSt, constSt_st, Function.update_apply, hG.eq_iff, hTX1],
      by simp [jst, preSt, zwsSt_sh, constSt_sh, hsh 3]⟩
    ⟨by simp [jst, Function.update_apply, hG.eq_iff], by simp [jst, preSt, zwsSt_sh, constSt_sh, hsh 24]⟩
    (by simp [jst, Function.update_apply, hR.eq_iff, v0, c0, hz 6 (by decide)])
    (by simp [jst, Function.update_apply, hR.eq_iff, v0, c0, hz 7 (by decide)])
    (by rw [← hgr]; exact hfit) (by omega)
  -- the registers back
  have ev := endSt_val G R hR W V ky2 ky2' kl2 kl2' (accFold (Yh P g V N) (Yl P g V N) (fun ℓ => cK3 P g V N ℓ - cK1
      P g V N ℓ) (V + 1)) (frame (binary W (tx + (accFold (Yh P g V N) (Yl P g V N) (fun ℓ => cK3 P g V N ℓ - cK1 P
      g V N ℓ) (V + 1))))) (preSt G R σ P W V g)
  have p31 : 2 ^ (hh P * P.b + fL P) ≤ 2 ^ (hh P * P.b + fL P + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have p32 : 2 ^ (hh P * P.s) ≤ 2 ^ (hh P * P.s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have p35 : 2 ^ (hh P * P.b + fR P) ≤ 2 ^ (hh P * P.b + fR P + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have x5 := gClr_spec R hR cap (endSt G R W V (preSt G R σ P W V g) ky2 ky2' kl2 kl2' (accFold (Yh P g V N) (Yl P g
      V N) (fun ℓ => cK3 P g V N ℓ - cK1 P g V N ℓ) (V + 1)) (frame (binary W (tx + (accFold (Yh P g V N) (Yl P g V
      N) (fun ℓ => cK3 P g V N ℓ - cK1 P g V N ℓ) (V + 1))))))
    (hh P) (W - (V + 1) - 1) W (W - 1) (2 * (V + 1) + 1) (W - (2 * (V + 1) + 1)) (1 * 2 ^ (hh P * P.b + fL P))
    (1 * 2 ^ (hh P * P.s)) (1 * 2 ^ (hh P * P.b + fR P))
    (by rw [ev, v0, c0]; simp) (by rw [ev, v0, c0]; simp) (by rw [ev, v0, c0]; simp) (by rw [ev, v0, c0]; simp)
    (by rw [ev, v0, c0]; simp) (by rw [ev, v0, c0]; simp) (by rw [ev, v0, c0]; simp) (by rw [ev, v0, c0]; simp)
    (by rw [ev, v0, c0]; simp)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have h26 : (σ.st (G 26)).length = 0 := Nat.le_zero.mp (by simpa [wlen] using hlen 26 (by decide))
  have h27 : (σ.st (G 27)).length = 0 := Nat.le_zero.mp (by simpa [wlen] using hlen 27 (by decide))
  refine ⟨gClrSt R (endSt G R W V (preSt G R σ P W V g) ky2 ky2' kl2 kl2' (accFold (Yh P g V N) (Yl P g V N) (fun ℓ
      => cK3 P g V N ℓ - cK1 P g V N ℓ) (V + 1)) (frame (binary W (tx + (accFold (Yh P g V N) (Yl P g V N) (fun ℓ =>
      cK3 P g V N ℓ - cK1 P g V N ℓ) (V + 1)))))),
    WExec.cast cap (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 x5)))) rfl
      (le_of_eq (by unfold gateCost; rw [hmY, hmL])), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgr]
    exact gate_st3 G R σ P W V g ky2 ky2' kl2 kl2' (accFold (Yh P g V N) (Yl P g V N) (fun ℓ => cK3 P g V N ℓ - cK1
        P g V N ℓ) (V + 1)) _
  · intro i hi1 hi2
    apply gate_st_other G R σ P W V g ky2 ky2' kl2 kl2' (accFold (Yh P g V N) (Yl P g V N) (fun ℓ => cK3 P g V N ℓ -
        cK1 P g V N ℓ) (V + 1)) _ i
    intro j hj h
    by_cases h4 : 4 ≤ j.val
    · exact hi2 (by rw [h]; exact mem_scS G R j h4)
    · have e3 : j = 3 := Fin.ext (by show j.val = 3; omega)
      subst e3
      exact hi1 h
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := mem_scS_inv G R i hi
    rw [slW_G G hG]
    exact gate_len G hG R σ P W V g ky2 ky2' kl2 kl2' (accFold (Yh P g V N) (Yl P g V N) (fun ℓ => cK3 P g V N ℓ -
        cK1 P g V N ℓ) (V + 1)) _ (by rw [hk1, keyStream_length W hW1, hmY])
      (by rw [hk2, keyStream_length W hW1, hmY]) (by rw [hk3, keyStream_length W hW1, hmL])
      (by rw [hk4, keyStream_length W hW1, hmL]) h26 h27 j hj
  · exact gate_sh G R σ P W V g ky2 ky2' kl2 kl2' (accFold (Yh P g V N) (Yl P g V N) (fun ℓ => cK3 P g V N ℓ - cK1 P
      g V N ℓ) (V + 1)) _
  · exact gate_val G R hR σ P W V g ky2 ky2' kl2 kl2' (accFold (Yh P g V N) (Yl P g V N) (fun ℓ => cK3 P g V N ℓ -
      cK1 P g V N ℓ) (V + 1)) _ hz
  · exact gate_cell G R σ P W V g ky2 ky2' kl2 kl2' (accFold (Yh P g V N) (Yl P g V N) (fun ℓ => cK3 P g V N ℓ - cK1
      P g V N ℓ) (V + 1)) _

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
