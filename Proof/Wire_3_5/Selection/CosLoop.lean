import Proof.Wire_3_5.Selection.CosBody

/-! # C1.5: the loop over the candidate cosets (P3:1358-1360)

Paper: "There are 2^k candidate cosets, so the total is bounded as claimed. Select a minimum objective" (P3:1358-1360).
The machine runs the coset body (`cosetB`) for `N = 0, 1, …, 2^k − 1`, the counter word `NS` stepped by C6's `incB`
and the rounds counted down in a register `C` outside the gate routine's map. The best key starts at the sentinel
`(1, 0)`, which every exact key beats (its denominator is positive), so after the round `N` the word `BEST` holds the
running first minimizer `argminIdx ratLt keyAt (N + 1)` (the counter fold) and `(BN, BD)` its key. After the last
round, `BEST = argminIdx ratLt keyAt 2^k`, the counter value of the selected coset (`selArgmin_eq_fold`).
Main declarations: `bestKey`, `argminIdx_succ`, `best_step`, `LInv`, `cosetL`, `iterCost`, **`cosetL_spec`**. Paper
quantity: the selected coset's counter value. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat

variable {ns nr : ℕ}

/-! ## The running minimum -/

/-- The best key before the round `N`: the sentinel `(1, 0)` before the first round, then the running minimizer's. -/
def bestKey (R : SelectionReq) (h : ParamsOk R) (N : ℕ) : RegRat :=
  if N = 0 then (1, 0) else keyAt R h (argminIdx ratLt (keyAt R h) N)

theorem argminIdx_succ {κ : Type} (lt : κ → κ → Bool) (key : ℕ → κ) (N : ℕ) :
    argminIdx lt key (N + 1) = if lt (key N) (key (argminIdx lt key N)) then N else argminIdx lt key N := by
  unfold argminIdx
  rw [List.range_succ, List.foldl_append]
  rfl

theorem argminIdx_one {κ : Type} (lt : κ → κ → Bool) (key : ℕ → κ) : argminIdx lt key 1 = 0 := by
  rw [argminIdx_succ]
  simp [argminIdx]

theorem argminIdx_lt {κ : Type} (lt : κ → κ → Bool) (key : ℕ → κ) : ∀ N : ℕ, argminIdx lt key (N + 1) < N + 1
  | 0 => by rw [argminIdx_one]; omega
  | N + 1 => by
    rw [argminIdx_succ]
    have := argminIdx_lt lt key N
    split_ifs <;> omega

theorem keyAt_den_pos (R : SelectionReq) (h : ParamsOk R) (N : ℕ) : 0 < (keyAt R h N).2 := by
  unfold keyAt objKey
  refine (Objective.ratAcc_val _ ?_).1
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨X, _, rfl⟩ := hx
  exact X.2.den_pos

/-- **One round of the running minimum**: the machine's update is `argminIdx`'s step and its key. -/
theorem best_step (R : SelectionReq) (h : ParamsOk R) (N : ℕ) :
    (if ratLt (keyAt R h N) (bestKey R h N) then N else argminIdx ratLt (keyAt R h) N) =
        argminIdx ratLt (keyAt R h) (N + 1) ∧
      (if ratLt (keyAt R h N) (bestKey R h N) then keyAt R h N else bestKey R h N) = bestKey R h (N + 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hf : ratLt (keyAt R h 0) (bestKey R h 0) = true := by
      simp [bestKey, ratLt, keyAt_den_pos R h 0]
    rw [hf, if_pos rfl, if_pos rfl, argminIdx_one]
    simp [bestKey, argminIdx_one]
  · have hb : bestKey R h N = keyAt R h (argminIdx ratLt (keyAt R h) N) := by simp [bestKey, hN.ne']
    rw [hb, argminIdx_succ]
    refine ⟨rfl, ?_⟩
    simp only [bestKey, Nat.add_one_ne_zero, if_false, argminIdx_succ]
    split_ifs <;> rfl

/-! ## The standing state across rounds -/

section BaseX
variable {S : Fin 50 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 64 → Fin nr} (hQ : Function.Injective Q)
variable {R : SelectionReq} {h : ParamsOk R} {W V N : ℕ}
include hS hQ

/-- The counter word may be replaced (the standing state at the new counter value). -/
theorem Base.setN {σ : WState ns nr} (b : Base S Q R h W V N σ) (N' : ℕ) :
    Base S Q R h W V N' (σ.sets (S 0) (frame (binary (R.r * R.s) N'))) := by
  have ne : ∀ m : Fin 50, m ≠ 0 → S m ≠ S 0 := fun m hm => hS.ne hm
  refine ⟨?_, b.gth, ?_, numOn_sets_other _ _ _ _ _ _ (ne 32 (by decide)) b.ng,
    numOn_sets_other _ _ _ _ _ _ (ne 2 (by decide)) b.of, numOn_sets_self _ _ _ _ b.nsw.2, ?_, b.gah, ?_, b.r0, b.r1,
    b.r2, b.r3, b.r4, b.r5, b.zr, b.nr1, b.np, b.ptl, b.tmp⟩
  · simp [ne 30 (by decide), b.gt]
  · simp [ne 31 (by decide), b.pt]
  · simp [ne 1 (by decide), b.ga]
  · intro j hj
    have hne := gG_ne hS hQ 0 (by decide) j hj
    simpa [hne] using b.sc j hj

/-- A register outside the loop's map may change. -/
theorem Base.setvX {σ : WState ns nr} (b : Base S Q R h W V N σ) (r : Fin nr) (hr : ∀ j, Q j ≠ r) (x : ℕ) :
    Base S Q R h W V N (σ.setv r x) := by
  have ne : ∀ j, Q j ≠ r := hr
  refine ⟨b.gt, b.gth, b.pt, numOn_setv _ _ _ _ _ _ b.ng, numOn_setv _ _ _ _ _ _ b.of,
    numOn_setv _ _ _ _ _ _ b.nsw, b.ga, b.gah, b.sc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ne 0, b.r0]
  · simp [ne 1, b.r1]
  · simp [ne 2, b.r2]
  · simp [ne 3, b.r3]
  · simp [ne 4, b.r4]
  · simp [ne 5, b.r5]
  · intro j hj
    have : gR Q j ≠ r := ne _
    simp [this, b.zr j hj]
  · simp [ne 60, b.nr1]
  · simp [ne 59, b.np]
  · simp [ne 58, b.ptl]
  · intro j hj
    simp [ne j, b.tmp j hj]

end BaseX

/-- **The loop's invariant before the round `N`**: the standing state, the table's head home, the words, the best key
and its counter value, the flags at `0`, and `C + N = 2^k`. -/
structure LInv (S : Fin 50 → Fin (ns + 1)) (Q : Fin 64 → Fin nr) (R : SelectionReq) (h : ParamsOk R) (W V : ℕ)
    (C : Fin nr) (N : ℕ) (σ : WState ns nr) : Prop where
  base : Base S Q R h W V N σ
  pth : σ.sh (S 31) = 0
  wd : Words S σ W
  an : ∃ v, NumOn σ (S 35) W v
  ad : ∃ v, NumOn σ (S 36) W v
  bn : NumOn σ (S 41) W (bestKey R h N).1
  bd : NumOn σ (S 42) W (bestKey R h N).2
  be : NumOn σ (S 43) (R.r * R.s) (argminIdx ratLt (keyAt R h) N)
  q52 : σ.val (Q 52) = 0
  q53 : σ.val (Q 53) = 0
  q57 : σ.val (Q 57) = 0
  cnt : σ.val C + N = 2 ^ (R.r * R.s)

/-- **The loop over the cosets**: `C` rounds of the coset body, the counter word stepped between rounds. -/
def cosetL (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (Q : Fin 64 → Fin nr)
    (hQ : Function.Injective Q) (C : Fin nr) : WM ns nr :=
  .whr C (.seq (.dec C) (.seq (cosetB S hS Q hQ) (.ifr C (incB (S 0) (S 43) (Q 61) (Q 62)) .skip)))

/-- One round's cost. -/
def iterCost (P : StarParams) (n W V g k np tl : ℕ) (ps : List (List ℕ × ℚ)) : ℕ :=
  1 + 1 + (cosetBCost P n W V g k np tl ps + 1 + (41 * k + 7 + 1))

/-- **The loop over the cosets**: from the invariant before the round `N` with `C = 2^k − N ≥ 1` rounds left, the
loop ends with `BEST = argminIdx ratLt keyAt 2^k` (the selected coset's counter value), the standing state at the last
counter value, `C = 0`, every other register, every head and the cell as they were. -/
theorem cosetL_spec (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (Q : Fin 64 → Fin nr)
    (hQ : Function.Injective Q) (C : Fin nr) (hC : ∀ j, Q j ≠ C) (cap : ℕ) (R : SelectionReq) (h : ParamsOk R)
    (W V : ℕ) (hng : R.gates.length < 2 ^ W) (hKB : ∀ g ∈ R.gates, KeyBound (gateOf g) V) (hW : 2 * V + 3 ≤ W)
    (hnk : R.n + (starParamsOf R h).k + 4 ≤ W) (hcap : gateNeed (starParamsOf R h) W V ≤ cap)
    (hcap2 : 2 * W + 1 ≤ cap) (hcapG : R.gates.length * (R.n + 1) * (2 * W + 2) + 2 < cap)
    (hcapk : 2 * (R.r * R.s) + 1 ≤ cap) (hcapP : R.pops.length ≤ cap) (hcapT : (popTable W R).length ≤ cap)
    (hcapC : 2 ^ (R.r * R.s) ≤ cap) (hW1 : 1 ≤ W)
    (hfit : ∀ N < 2 ^ (R.r * R.s), PopsFit R h N W cap (0, 1) R.pops)
    (hkey : ∀ N < 2 ^ (R.r * R.s), ∀ M < 2 ^ (R.r * R.s),
      (keyAt R h N).1 * (keyAt R h M).2 < 2 ^ W ∧ (keyAt R h M).1 * (keyAt R h N).2 < 2 ^ W)
    (hden : ∀ N < 2 ^ (R.r * R.s), (keyAt R h N).2 < 2 ^ W) :
    ∀ (m N : ℕ) (σ : WState ns nr), LInv S Q R h W V C N σ → σ.val C = m + 1 →
      ∃ τ : WState ns nr, WExec cap (cosetL S hS Q hQ C) σ τ
          ((m + 1) * (iterCost (starParamsOf R h) R.n W V R.gates.length (R.r * R.s) R.pops.length
            (popTable W R).length R.pops + 2) + 1) ∧
        Base S Q R h W V (2 ^ (R.r * R.s) - 1) τ ∧
        NumOn τ (S 43) (R.r * R.s) (argminIdx ratLt (keyAt R h) (2 ^ (R.r * R.s))) ∧ τ.val C = 0 ∧
        (∀ r : Fin nr, r ≠ C → τ.val r = σ.val r) ∧ (∀ k : Fin 50, τ.sh (S k) = σ.sh (S k)) ∧
        (∀ k : Fin 50, 28 ≤ k.val → k.val ≠ 46 → (k.val < 33 ∨ 44 < k.val) → τ.st (S k) = σ.st (S k)) ∧
        τ.cell = σ.cell
  | m, N, σ, inv, hCm => by
    have sne : ∀ a c : Fin 50, a ≠ c → S a ≠ S c := fun a c h => hS.ne h
    have hNk : N < 2 ^ (R.r * R.s) := by have := inv.cnt; omega
    have hne : σ.val C ≠ 0 := by rw [hCm]; omega
    have d := WExec.dec (cap := cap) C σ (by have := inv.cnt; omega)
    set σ1 := σ.setv C (σ.val C - 1) with hσ1
    have hC1 : σ1.val C = m := by simp [hσ1, hCm]
    have vQ : ∀ j, σ1.val (Q j) = σ.val (Q j) := fun j => by simp [hσ1, hC j]
    -- the best key's widths at this round
    have hb := inv.base.setvX hS hQ C hC (σ.val C - 1)
    have hl : (keyAt R h N).1 * (bestKey R h N).2 < 2 ^ W ∧ (bestKey R h N).1 * (keyAt R h N).2 < 2 ^ W ∧
        (keyAt R h N).2 < 2 ^ W ∧ (bestKey R h N).2 < 2 ^ W := by
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · subst h0
        simp only [bestKey, if_true, Nat.mul_zero, Nat.one_mul]
        exact ⟨Nat.two_pow_pos W, hden 0 hNk, hden 0 hNk, Nat.two_pow_pos W⟩
      · have hM : argminIdx ratLt (keyAt R h) N < 2 ^ (R.r * R.s) := by
          have := argminIdx_lt ratLt (keyAt R h) (N - 1)
          rw [Nat.sub_add_cancel hpos] at this
          omega
        simp only [bestKey, hpos.ne', if_false]
        exact ⟨(hkey N hNk _ hM).1, (hkey N hNk _ hM).2, hden N hNk, hden _ hM⟩
    obtain ⟨τ1, x1, b1, pth1, wd1, an1, ad1, bn1, bd1, be1, st1, sh1, val1, cell1⟩ :=
      cosetB_spec S hS Q hQ cap R h W V N hng hNk hKB hW hnk hcap hcap2 hcapG hcapk hcapP hcapT hW1 σ1
        (bestKey R h N).1 (bestKey R h N).2 (argminIdx ratLt (keyAt R h) N) hb (by simp [hσ1, inv.pth])
        (words_setv S σ W _ _ inv.wd)
        (by obtain ⟨v, hv⟩ := inv.an; exact ⟨v, numOn_setv _ _ _ _ _ _ hv⟩)
        (by obtain ⟨v, hv⟩ := inv.ad; exact ⟨v, numOn_setv _ _ _ _ _ _ hv⟩)
        (numOn_setv _ _ _ _ _ _ inv.bn) (numOn_setv _ _ _ _ _ _ inv.bd) (numOn_setv _ _ _ _ _ _ inv.be)
        (by rw [vQ, inv.q52]) (by rw [vQ, inv.q53]) (by rw [vQ, inv.q57]) (hfit N hNk)
        hl.1 hl.2.1 hl.2.2.1 hl.2.2.2
    obtain ⟨hstepB, hstepK⟩ := best_step R h N
    rw [show (bestKey R h N).1 = (bestKey R h N).1 from rfl] at bn1
    have bn1' : NumOn τ1 (S 41) W (bestKey R h (N + 1)).1 := by
      rw [← hstepK]; split_ifs with hf <;> simpa [hf] using bn1
    have bd1' : NumOn τ1 (S 42) W (bestKey R h (N + 1)).2 := by
      rw [← hstepK]; split_ifs with hf <;> simpa [hf] using bd1
    have be1' : NumOn τ1 (S 43) (R.r * R.s) (argminIdx ratLt (keyAt R h) (N + 1)) := by
      rw [← hstepB]; exact be1
    have hCτ1 : τ1.val C = m := by rw [val1, hC1]
    have v1 : ∀ r : Fin nr, r ≠ C → τ1.val r = σ.val r := by
      intro r hr; rw [val1]; simp [hσ1, Function.update_apply, hr]
    have iterEq : iterCost (starParamsOf R h) R.n W V R.gates.length (R.r * R.s) R.pops.length
        (popTable W R).length R.pops = 1 + 1 + (cosetBCost (starParamsOf R h) R.n W V R.gates.length (R.r * R.s)
          R.pops.length (popTable W R).length R.pops + 1 + (41 * (R.r * R.s) + 7 + 1)) := rfl
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- the last round
      subst hm0
      have hlast : N + 1 = 2 ^ (R.r * R.s) := by have := inv.cnt; omega
      have x2 : WExec cap (.ifr C (incB (S 0) (S 43) (Q 61) (Q 62)) .skip) τ1 τ1 (41 * (R.r * R.s) + 7 + 1) :=
        WExec.mono (WExec.ifrF hCτ1 (WExec.skip τ1)) (by omega)
      refine ⟨τ1, ?_, ?_, ?_, hCτ1, v1, ?_, ?_, cell1⟩
      · refine WExec.cast cap (WExec.whrT hne (WExec.seq d (WExec.seq x1 x2)) (WExec.whrF hCτ1)) rfl ?_
        rw [iterEq]; omega
      · rw [show 2 ^ (R.r * R.s) - 1 = N by omega]; exact b1
      · rw [← hlast]; exact be1'
      · intro k; rw [sh1 k]; rfl
      · intro k hk h46 hk2; rw [st1 k hk h46 hk2]; rfl
    · -- a further round
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hN1 : N + 1 < 2 ^ (R.r * R.s) := by have := inv.cnt; omega
      have q61 : τ1.val (Q 61) = 0 := by rw [v1 _ (hC 61)]; exact inv.base.tmp 61 (by decide)
      have q62 : τ1.val (Q 62) = 0 := by rw [v1 _ (hC 62)]; exact inv.base.tmp 62 (by decide)
      have x2 := incB_spec cap (R.r * R.s) (A := S 0) (B := S 43) (F := Q 61) (R := Q 62) (sne 0 43 (by decide))
        (hQ.ne (by decide)) τ1 N (argminIdx ratLt (keyAt R h) (N + 1)) b1.nsw be1' q61 q62 hN1 hcapk
      set τ2 := τ1.sets (S 0) (frame (binary (R.r * R.s) (N + 1))) with hτ2
      have inv2 : LInv S Q R h W V C (N + 1) τ2 := by
        refine ⟨b1.setN hS hQ (N + 1), by simp [hτ2, sne 31 0 (by decide), pth1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_⟩
        · intro k hk
          obtain ⟨v, hv⟩ := wd1 k hk
          have k0 : S k ≠ S 0 := sne k 0 (by
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          exact ⟨v, numOn_sets_other _ _ _ _ _ _ k0 hv⟩
        · obtain ⟨v, hv⟩ := an1; exact ⟨v, numOn_sets_other _ _ _ _ _ _ (sne 35 0 (by decide)) hv⟩
        · obtain ⟨v, hv⟩ := ad1; exact ⟨v, numOn_sets_other _ _ _ _ _ _ (sne 36 0 (by decide)) hv⟩
        · exact numOn_sets_other _ _ _ _ _ _ (sne 41 0 (by decide)) bn1'
        · exact numOn_sets_other _ _ _ _ _ _ (sne 42 0 (by decide)) bd1'
        · exact numOn_sets_other _ _ _ _ _ _ (sne 43 0 (by decide)) be1'
        · simp [hτ2, v1 _ (hC 52), inv.q52]
        · simp [hτ2, v1 _ (hC 53), inv.q53]
        · simp [hτ2, v1 _ (hC 57), inv.q57]
        · simp [hτ2, hCτ1]; have := inv.cnt; omega
      obtain ⟨τ, x3, bτ, beτ, hCτ, vτ, shτ, stτ, cellτ⟩ :=
        cosetL_spec S hS Q hQ C hC cap R h W V hng hKB hW hnk hcap hcap2 hcapG hcapk hcapP hcapT hcapC hW1 hfit
          hkey hden m' (N + 1) τ2 inv2 (by simp [hτ2, hCτ1])
      refine ⟨τ, ?_, bτ, beτ, hCτ, ?_, ?_, ?_, ?_⟩
      · have hne1 : τ1.val C ≠ 0 := by rw [hCτ1]; omega
        refine WExec.cast cap (WExec.whrT hne (WExec.seq d (WExec.seq x1 (WExec.ifrT hne1 x2))) x3) rfl
          (le_of_eq ?_)
        rw [iterEq]; ring
      · intro r hr; rw [vτ r hr]; simp [hτ2, v1 r hr]
      · intro k; rw [shτ k]; simp [hτ2, sh1 k, hσ1]
      · intro k hk h46 hk2
        rw [stτ k hk h46 hk2]
        have k0 : S k ≠ S 0 := sne k 0 (fun e => by subst e; simp at hk)
        simp [hτ2, k0, st1 k hk h46 hk2, hσ1]
      · rw [cellτ]; simp [hτ2, cell1, hσ1]

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
