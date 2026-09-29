import Proof.Wire_3_5.Selection.GatePre6

/-! # C1.4: the gate routine's preamble (P3:1339-1358)

Paper: "Enumerate its `2^k` error rows. For each gate and row [...] Enumerate each half's score vectors" (P3:1339-1345).
The preamble: the constants (`consts`), the two weight tables in machine order (`tabLP`, `tabRP`), the zero words
(`zws`), the threshold's key `TK = θ + 2^V` (`tkP`), the level word `PW = 2` (`pwP`), and the widths' registers back to
`0`. Main declarations: `pwP_spec`, `pre`, `preSt`, `preCost`, **`pre_spec`**. Paper quantity: none (the machine's
setup of one gate). -/

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

/-- `PW := 2`. -/
def pwP (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) : WM ns nr :=
  .seq (oneB (G 17) (G 24) (R 6) (R 7)) (shlB (G 17) (G 24) (R 6) (R 7))

theorem pwP_spec (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr)
    (hR : Function.Injective R) (cap W : ℕ) (σ : WState ns nr) (hPW : NumOn σ (G 17) W 0) (hACC : NumOn σ (G 24) W 0)
    (r6 : σ.val (R 6) = 0) (r7 : σ.val (R 7) = 0) (hW : 1 ≤ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (pwP G R) σ (σ.sets (G 17) (frame (binary W 2))) (41 * W + 7 + 1 + (41 * W + 8)) := by
  have h1 := oneB_spec cap W (A := G 17) (B := G 24) (F := R 6) (R := R 7) (hG.ne (by decide)) (hR.ne (by decide)) σ 0 0
    hPW hACC r6 r7 hW hcap
  have h2 := shlB_spec cap W (A := G 17) (B := G 24) (F := R 6) (R := R 7) (hG.ne (by decide)) (hR.ne (by decide))
    (σ.sets (G 17) (frame (binary W 1))) 1 0 ⟨by simp, by simp [hPW.2]⟩
    ⟨by simp [Function.update_apply, hG.eq_iff, hACC.1], by simp [hACC.2]⟩ (by simp [r6]) (by simp [r7]) hcap
  have e : (σ.sets (G 17) (frame (binary W 1))).sets (G 17) (frame (binary W (2 * 1))) = σ.sets (G 17) (frame (binary W 2)) := by
    apply WState.eq
    · rfl
    · funext j; simp only [WState.sets_st, Function.update_apply]; split_ifs <;> rfl
    · rfl
    · rfl
  rw [e] at h2
  exact WExec.seq h1 h2

/-- **The preamble.** -/
def pre (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) : WM ns nr :=
  .seq (consts G R) (.seq (tabLP G R) (.seq (tabRP G R) (.seq (zws G R) (.seq (tkP G R) (.seq (pwP G R)
    (.seq (WM.clear (R 42)) (WM.clear (R 43))))))))

/-- The preamble's result. -/
def preSt (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (σ : WState ns nr) (P : StarParams) (W V : ℕ)
    (g : NormalizedThresholdGate P.n) : WState ns nr :=
  ((((zwsSt G (((constSt R σ W V (hh P) P.b P.s (fL P) (fR P)).sets (G 6) (tbl W (recsL P g))).sets (G 7)
    (tbl W (recsR P g))) (hh P * P.b + fL P + 1) (hh P * P.s + 1) P.s W).sets (G 13)
    (frame (binary W (keyOf V g.threshold)))).sets (G 17) (frame (binary W 2))).setv (R 42) 0).setv (R 43) 0

/-- The preamble's cost. -/
def preCost (P : StarParams) (W V : ℕ) : ℕ :=
  constsCost W V (hh P) P.b P.s (fL P) (fR P) + 1 + (tabLCost P W + 1 + (tabRCost P W + 1 +
    (zwsCost (hh P * P.b + fL P + 1) (hh P * P.s + 1) P.s W + 1 + (tkCost P W + 1 + (41 * W + 7 + 1 + (41 * W + 8) + 1 +
      (3 * (hh P * P.b + fL P + 1) + 1 + 1 + (3 * (hh P * P.s + 1) + 1)))))))

theorem constSt_st (R : Fin 48 → Fin nr) (σ : WState ns nr) (W V hh b s fL fR : ℕ) :
    (constSt R σ W V hh b s fL fR).st = σ.st := by simp only [constSt, WState.setv_st]
theorem constSt_sh (R : Fin 48 → Fin nr) (σ : WState ns nr) (W V hh b s fL fR : ℕ) :
    (constSt R σ W V hh b s fL fR).sh = σ.sh := by simp only [constSt, WState.setv_sh]
theorem constSt_val (R : Fin 48 → Fin nr) (hR : Function.Injective R) (σ : WState ns nr) (W V hh b s fL fR : ℕ)
    (i : Fin 48) : (constSt R σ W V hh b s fL fR).val (R i) =
      if i = 43 then hh * s + 1 else if i = 42 then hh * b + fL + 1 else if i = 32 then 1 * 2 ^ (hh * s) else
      if i = 35 then 1 * 2 ^ (hh * b + fR) else if i = 31 then 1 * 2 ^ (hh * b + fL) else if i = 15 then hh else
      if i = 26 then W - (2 * (V + 1) + 1) else if i = 25 then 2 * (V + 1) + 1 else if i = 21 then W - (V + 1) - 1 else
      if i = 24 then W - 1 else if i = 23 then W else σ.val (R i) := by
  simp only [constSt, WState.setv_val, Function.update_apply, hR.eq_iff]

theorem zwsSt_val (G : Fin 28 → Fin (ns + 1)) (σ : WState ns nr) (lx ux s W : ℕ) :
    (zwsSt G σ lx ux s W).val = σ.val := by simp only [zwsSt, WState.sets_val]
theorem zwsSt_sh (G : Fin 28 → Fin (ns + 1)) (σ : WState ns nr) (lx ux s W : ℕ) :
    (zwsSt G σ lx ux s W).sh = σ.sh := by simp only [zwsSt, WState.sets_sh]

section Pre
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (P : StarParams) (W V : ℕ) (g : NormalizedThresholdGate P.n) (cap : ℕ)
include hG hR

set_option maxHeartbeats 8000000 in
/-- **The preamble.** -/
theorem pre_spec (σ : WState ns nr) (hGA : σ.st (G 1) = gateRec W g) (hOF : σ.st (G 2) = frame (binary W (2 ^ V)))
    (hsh : ∀ i : Fin 28, σ.sh (G i) = 0) (r0 : σ.val (R 0) = hh P) (r1 : σ.val (R 1) = P.b) (r2 : σ.val (R 2) = P.s)
    (r3 : σ.val (R 3) = fL P) (r4 : σ.val (R 4) = fR P) (r5 : σ.val (R 5) = V + 1)
    (hz : ∀ i : Fin 48, 6 ≤ i.val → σ.val (R i) = 0)
    (hl6 : (σ.st (G 6)).length ≤ lw P * (2 * W + 2)) (hl7 : (σ.st (G 7)).length ≤ rw P * (2 * W + 2))
    (hlx : ∀ i : Fin 28, (i = 4 ∨ i = 14) → (σ.st (G i)).length ≤ 2 * (hh P * P.b + fL P + 1) + 1)
    (hlu : ∀ i : Fin 28, (i = 5 ∨ i = 15) → (σ.st (G i)).length ≤ 2 * (hh P * P.s + 1) + 1)
    (hls : ∀ i : Fin 28, (i = 8 ∨ i = 9) → (σ.st (G i)).length ≤ 2 * P.s + 1)
    (hlw : ∀ i : Fin 28, (i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 16 ∨ i = 17 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25) →
      (σ.st (G i)).length ≤ 2 * W + 1)
    (hθ : g.threshold.natAbs < 2 ^ V) (hVW : V + 2 ≤ W)
    (hcap1 : 2 * W + 4 * V + 2 ^ (hh P * P.b + fL P + 1) + 2 ^ (hh P * P.b + fR P + 1) + 2 ^ (hh P * P.s + 1) +
      hh P * P.b + hh P * P.s + hh P + P.b + P.s + fL P + fR P + 10 ≤ cap)
    (hcap2 : (P.n + 1) * (2 * W + 2) + 2 < cap)
    (hcap3 : 2 * (hh P * P.b + fL P + 1) + 2 * (hh P * P.s + 1) + 2 * P.s + 2 * W + 2 ≤ cap) :
    WExec cap (pre G R) σ (preSt G R σ P W V g) (preCost P W V) := by
  obtain ⟨sz1, sz2, sz3, sz4, sz5, sz6, sz7, sz8⟩ := size_facts P
  have z : ∀ i : Fin 48, 6 ≤ i.val → σ.val (R i) = 0 := hz
  have x1 := consts_spec cap G R hR σ W V (hh P) P.b P.s (fL P) (fR P) hOF (hsh 2) r0 r1 r2 r3 r4 r5
    (z 15 (by decide)) (z 21 (by decide)) (z 23 (by decide)) (z 24 (by decide)) (z 25 (by decide)) (z 26 (by decide))
    (z 31 (by decide)) (z 32 (by decide)) (z 35 (by decide)) (z 37 (by decide)) (z 38 (by decide)) (z 39 (by decide))
    (z 40 (by decide)) (z 41 (by decide)) (z 42 (by decide)) (z 43 (by decide)) (z 44 (by decide)) hcap1
  have v1 := constSt_val R hR σ W V (hh P) P.b P.s (fL P) (fR P)
  set σ1 := constSt R σ W V (hh P) P.b P.s (fL P) (fR P) with hσ1
  have x2 := tabL_spec G hG R hR P W g cap σ1 hGA (hsh 1) (hsh 6) (by rw [v1]; simp [r0]) (by rw [v1]; simp [r1])
    (by rw [v1]; simp [r3]) (by rw [v1]; simp [z 37 (by decide)]) (by rw [v1]; simp [z 38 (by decide)])
    (by rw [v1]; simp [z 39 (by decide)]) (by rw [v1]; simp [z 40 (by decide)]) (by rw [v1]; simp [z 41 (by decide)])
    hl6 hcap2
  set σ2 := σ1.sets (G 6) (tbl W (recsL P g)) with hσ2
  have x3 := tabR_spec G hG R hR P W g cap σ2 (by simp [hσ2, hσ1, constSt_st, Function.update_apply, hG.eq_iff, hGA])
    (hsh 1) (hsh 7) (by simp [hσ2, v1, r0]) (by simp [hσ2, v1, r1]) (by simp [hσ2, v1, r3]) (by simp [hσ2, v1, r4])
    (by simp [hσ2, v1]) (by simp [hσ2, v1, z 37 (by decide)]) (by simp [hσ2, v1, z 38 (by decide)])
    (by simp [hσ2, v1, z 39 (by decide)]) (by simp [hσ2, v1, z 40 (by decide)]) (by simp [hσ2, v1, z 41 (by decide)])
    (by simp [hσ2, hσ1, constSt_st, Function.update_apply, hG.eq_iff]; exact hl7) hcap2
  set σ3 := σ2.sets (G 7) (tbl W (recsR P g)) with hσ3
  have st3 : ∀ i : Fin 28, i ≠ 6 → i ≠ 7 → σ3.st (G i) = σ.st (G i) := fun i h6 h7 => by
    simp [hσ3, hσ2, hσ1, constSt_st, Function.update_apply, hG.eq_iff, h6, h7]
  have x4 := zws_spec G hG R hR cap σ3 (hh P * P.b + fL P + 1) (hh P * P.s + 1) P.s W (fun i => hsh i)
    (by simp [hσ3, hσ2, v1, z 40 (by decide)]) (by simp [hσ3, hσ2, v1, z 44 (by decide)])
    (by simp [hσ3, hσ2, v1, z 37 (by decide)]) (by simp [hσ3, hσ2, v1]) (by simp [hσ3, hσ2, v1])
    (by simp [hσ3, hσ2, v1, r2]) (by simp [hσ3, hσ2, v1])
    (by rw [st3 4 (by decide) (by decide)]; exact hlx 4 (Or.inl rfl))
    (by rw [st3 14 (by decide) (by decide)]; exact hlx 14 (Or.inr rfl))
    (by rw [st3 5 (by decide) (by decide)]; exact hlu 5 (Or.inl rfl))
    (by rw [st3 15 (by decide) (by decide)]; exact hlu 15 (Or.inr rfl))
    (by rw [st3 8 (by decide) (by decide)]; exact hls 8 (Or.inl rfl))
    (by rw [st3 9 (by decide) (by decide)]; exact hls 9 (Or.inr rfl))
    (by rw [st3 10 (by decide) (by decide)]; exact hlw 10 (by decide))
    (by rw [st3 11 (by decide) (by decide)]; exact hlw 11 (by decide))
    (by rw [st3 12 (by decide) (by decide)]; exact hlw 12 (by decide))
    (by rw [st3 13 (by decide) (by decide)]; exact hlw 13 (by decide))
    (by rw [st3 16 (by decide) (by decide)]; exact hlw 16 (by decide))
    (by rw [st3 17 (by decide) (by decide)]; exact hlw 17 (by decide))
    (by rw [st3 22 (by decide) (by decide)]; exact hlw 22 (by decide))
    (by rw [st3 23 (by decide) (by decide)]; exact hlw 23 (by decide))
    (by rw [st3 24 (by decide) (by decide)]; exact hlw 24 (by decide))
    (by rw [st3 25 (by decide) (by decide)]; exact hlw 25 (by decide)) hcap3
  set σ4 := zwsSt G σ3 (hh P * P.b + fL P + 1) (hh P * P.s + 1) P.s W with hσ4
  have st4 : ∀ (i : Fin 28) (n : ℕ), (i = 10 ∨ i = 12 ∨ i = 13 ∨ i = 17 ∨ i = 24) → σ4.st (G i) = frame (binary W 0) := by
    intro i n hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [hσ4, zwsSt, Function.update_apply, hG.eq_iff]
  have v4 : ∀ i : Fin 48, σ4.val (R i) = σ1.val (R i) := fun i => by simp only [hσ4, zwsSt_val, hσ3, hσ2, WState.sets_val]
  have x5 := tkP_spec G hG R hR P W V g cap σ4
    (by simp [hσ4, zwsSt, hσ3, hσ2, hσ1, constSt_st, Function.update_apply, hG.eq_iff, hGA]) (fun i => hsh i)
    (by simp [hσ4, zwsSt, hσ3, hσ2, hσ1, constSt_st, Function.update_apply, hG.eq_iff, hOF])
    (st4 13 0 (by decide)) (st4 12 0 (by decide)) (st4 10 0 (by decide))
    (by rw [v4, v1]; simp [r0]) (by rw [v4, v1]; simp [r1]) (by rw [v4, v1]; simp [r3]) (by rw [v4, v1]; simp [r4])
    (by rw [v4, v1]; simp [z 6 (by decide)]) (by rw [v4, v1]; simp [z 7 (by decide)])
    (by rw [v4, v1]; simp [z 10 (by decide)]) (by rw [v4, v1]; simp [z 37 (by decide)])
    (by rw [v4, v1]; simp [z 38 (by decide)]) (by rw [v4, v1]; simp [z 40 (by decide)])
    (by rw [v4, v1]; simp [z 41 (by decide)]) hθ (by omega) hcap2
  set σ5 := σ4.sets (G 13) (frame (binary W (keyOf V g.threshold))) with hσ5
  have x6 := pwP_spec G hG R hR cap W σ5
    ⟨by simp [hσ5, st4 17 0 (by decide), Function.update_apply, hG.eq_iff], by simp [hσ5, hσ4, zwsSt_sh, hσ3, hσ2, hσ1, constSt_sh, hsh 17]⟩
    ⟨by simp [hσ5, st4 24 0 (by decide), Function.update_apply, hG.eq_iff], by simp [hσ5, hσ4, zwsSt_sh, hσ3, hσ2, hσ1, constSt_sh, hsh 24]⟩
    (by simp [hσ5, v4, v1, z 6 (by decide)]) (by simp [hσ5, v4, v1, z 7 (by decide)]) (by omega) (by omega)
  set σ6 := σ5.sets (G 17) (frame (binary W 2)) with hσ6
  have x7 := wclear_spec cap (R 42) (hh P * P.b + fL P + 1) σ6 (by simp [hσ6, hσ5, v4, v1])
    (by simp [hσ6, hσ5, v4, v1]; omega)
  have v6 : (σ6.setv (R 42) 0).val (R 43) = hh P * P.s + 1 := by
    simp [hσ6, hσ5, v4, v1, Function.update_apply, hR.eq_iff]
  have x8 := wclear_spec cap (R 43) (hh P * P.s + 1) (σ6.setv (R 42) 0) v6 (by rw [v6]; omega)
  unfold pre preSt preCost
  exact WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5 (WExec.seq x6 (WExec.seq x7 x8))))))

end Pre

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
