import Proof.Wire_3_5.Selection.GatePre3

/-! # C1.4: building the weight tables (P3:1339-1344, 1195-1197)

Paper: "Enumerate each half's score vectors" (P3:1344-1345). The left table: for `t = 0, …, h − 1` (the counted loop
leaves `h − 1 − t` in `Rh`), skip `(h − 1 − t)·b` records of the gate record, copy `b` records negated, return; then skip
`2h·b = r·b` records and copy the `fL` free records negated. The right table: skip `h·b + (h − 1 − t)·b`, copy `b`; then
skip `r·b + fL`, copy `fR`. Main declarations: `skipNN_rst`, `rewB_rst`, `tabLP`, **`tabL_spec`**, `tabRP`,
**`tabR_spec`**. Paper quantity: a half's weights in the machine's order. -/

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
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit (cloop cloop_spec)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

variable {ns nr : ℕ}

section Runs2
variable (cap : ℕ) (σ0 : WState ns nr) {A B : Fin (ns + 1)} {CA CB : Fin nr} (L : List Bool)
variable (hAB : A ≠ B) (hC : CA ≠ CB)
include hAB hC

/-- **Skip `k1·k2` records** (nested counted loops) from record `s0`. -/
theorem skipNN_rst (K1 T1 K2 T2 : Fin nr) (hd : [K1, T1, K2, T2, CA, CB].Nodup) (W : ℕ) (recs : List (Bool × ℕ))
    (post : List Bool) (hA : σ0.st A = tbl W recs ++ post) (s0 k1 k2 : ℕ) (out : List Bool) (hK1 : σ0.val K1 = k1)
    (hT1 : σ0.val T1 = 0) (hK2 : σ0.val K2 = k2) (hT2 : σ0.val T2 = 0) (hjk : s0 + k1 * k2 ≤ recs.length)
    (hcap : recs.length * (2 * W + 2) + 2 < cap) (hk1 : k1 ≤ cap) :
    WExec cap (cloop K1 T1 (cloop K2 T2 (skipRec A CA))) (rst σ0 A B CA CB L (s0 * (2 * W + 2)) out)
      (rst σ0 A B CA CB L ((s0 + k1 * k2) * (2 * W + 2)) out)
      (k1 * (k2 * (13 * W + 13 + 8) + 1 + 1 + (7 * k2 + 1) + 8) + 1 + 1 + (7 * k1 + 1)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3⟩, ⟨d1, d2⟩, e1, -⟩ := hd
  have hl := Point.cloopM cap K1 T1 a1 (cloop K2 T2 (skipRec A CA))
    (fun σ i => rst σ A B CA CB L ((s0 + i * k2) * (2 * W + 2)) out)
    (fun σ i v w => rst_setv2 σ L hAB hC K1 T1 v w a4 a5 b3 b4 _ _) σ0 k1 _ hK1 hT1 hk1
    (by
      intro i hi v w
      have hik : s0 + i * k2 + k2 ≤ recs.length := by
        have := Nat.mul_le_mul_right k2 (show i + 1 ≤ k1 by omega); rw [add_one_mul] at this; omega
      have h := skipN_rst cap ((σ0.setv K1 v).setv T1 w) L hAB hC K2 T2 c1 c2 c3 d1 d2 W recs post
        (by simp [hA]) (s0 + i * k2) k2 out (by simp [Function.update_apply, Ne.symm a2, Ne.symm b1, hK2])
        (by simp [Function.update_apply, Ne.symm a3, Ne.symm b2, hT2]) hik hcap
      refine WExec.cast cap h ?_ le_rfl
      congr 1; ring)
  simpa using hl

/-- Return the output's head: the output stream holds `overlay out L`. -/
theorem rewB_rst (hA0 : σ0.sh A = 0) (hCA0 : σ0.val CA = 0) (hB0 : σ0.sh B = 0) (hCB0 : σ0.val CB = 0)
    (out : List Bool) (hq : out.length ≤ cap) :
    WExec cap (WM.rewind B CB) (rst σ0 A B CA CB L 0 out) (σ0.sets B (overlay out L)) (5 * out.length + 1) := by
  have h := wrewind_spec cap B CB out.length (rst σ0 A B CA CB L 0 out) (by simp [rst]) (by simp [rst]; exact hq)
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · funext j; simp only [rst, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · funext j; simp only [rst, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
  · funext j; simp only [rst, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl

end Runs2

/-- **The counted loop over a family, the count visible**: round `j` runs with `K = n − j − 1`, `T = j + 1`. -/
theorem cloopMK (cap : ℕ) (K T : Fin nr) (hKT : K ≠ T) (body : WM ns nr) (M : WState ns nr → ℕ → WState ns nr)
    (hM : ∀ σ j v w, ((M σ j).setv K v).setv T w = M ((σ.setv K v).setv T w) j) (σ0 : WState ns nr) (n c : ℕ)
    (hK : σ0.val K = n) (hT : σ0.val T = 0) (hcap : n ≤ cap)
    (hbody : ∀ j < n, WExec cap body (M ((σ0.setv K (n - j - 1)).setv T (j + 1)) j)
      (M ((σ0.setv K (n - j - 1)).setv T (j + 1)) (j + 1)) c) :
    WExec cap (cloop K T body) (M σ0 0) (M σ0 n) (n * (c + 8) + 1 + 1 + (7 * n + 1)) := by
  have h := cloop_spec cap K T hKT body n c (fun j => M σ0 j) hcap (fun j hj => by rw [hM, hM]; exact hbody j hj)
  have e : (σ0.setv K n).setv T 0 = σ0 := by rw [← hK, wsetv_same, ← hT, wsetv_same]
  simp only [hM, e] at h
  exact h

theorem rst_self (σ : WState ns nr) {A B : Fin (ns + 1)} {CA CB : Fin nr} (hAB : A ≠ B) (hC : CA ≠ CB)
    (hA : σ.sh A = 0) (hCA : σ.val CA = 0) (hB : σ.sh B = 0) (hCB : σ.val CB = 0) :
    rst σ A B CA CB (σ.st B) 0 [] = σ := by
  rw [rst_kst σ (σ.st B) hAB hC hA hCA, kst_nil σ B CB hB hCB]

/-- One block of a table: `b` records from record `j`, signs xor `neg`. -/
def blkRecs (b W j : ℕ) (CR : List (Bool × ℕ)) (neg : Bool) : List Bool :=
  (List.range b).flatMap (fun i => recBits W (xor (recAt CR (j + i)).1 neg, (recAt CR (j + i)).2))

theorem blkRecs_length (b W j : ℕ) (CR : List (Bool × ℕ)) (neg : Bool) :
    (blkRecs b W j CR neg).length = b * (2 * W + 2) := by
  unfold blkRecs; rw [List.length_flatMap]; simp [recBits_length, List.sum_replicate]

/-- **The blocks' loop** of a table: round `t` skips `skip0 + (h − 1 − t)·b` records, copies `b`, and returns. -/
def tabBlocks (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (pre : WM ns nr) (neg : Bool) (dst : Fin 28) :
    WM ns nr :=
  cloop (R 0) (R 37) (.seq pre (.seq (cloop (R 0) (R 38) (cloop (R 1) (R 39) (skipRec (G 1) (R 40))))
    (.seq (cloop (R 1) (R 38) (copyRec neg (G 1) (G dst) (R 40) (R 41))) (WM.rewind (G 1) (R 40)))))

/-- The blocks' loop's cost. -/
def tabBlocksCost (cpre W hh b nl : ℕ) : ℕ :=
  hh * ((cpre + 1 + ((hh - 0) * ((b * (13 * W + 13 + 8) + 1 + 1 + (7 * b + 1)) + 8) + 1 + 1 + (7 * hh + 1)) + 1 +
    (b * (40 * W + 40 + 8) + 1 + 1 + (7 * b + 1) + 1 + (5 * ((nl + 1) * (2 * W + 2)) + 1))) + 8) + 1 + 1 + (7 * hh + 1)

section Blocks
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (cap W hh b : ℕ) (CR : List (Bool × ℕ)) (post : List Bool)
include hG hR

set_option maxHeartbeats 4000000 in
/-- **The blocks' loop**: from the start, the destination gains block `skip0/b + (h − 1 − t)` for `t = 0, …, h − 1`;
`pre` moves the source head from `0` to record `skip0` (the right table's extra skip), or does nothing. -/
theorem tabBlocks_spec (pre : WM ns nr) (neg : Bool) (dst : Fin 28) (hdst : dst ≠ 1) (skip0 cpre : ℕ)
    (σ : WState ns nr) (hA : σ.st (G 1) = tbl W CR ++ post) (h1 : σ.sh (G 1) = 0) (hd : σ.sh (G dst) = 0)
    (r0 : σ.val (R 0) = hh) (r1 : σ.val (R 1) = b) (r37 : σ.val (R 37) = 0) (r38 : σ.val (R 38) = 0)
    (r39 : σ.val (R 39) = 0) (r40 : σ.val (R 40) = 0) (r41 : σ.val (R 41) = 0)
    (hpre : ∀ (σ' : WState ns nr) (out : List Bool), σ'.st = σ.st → σ'.sh = σ.sh →
      (∀ i : Fin 48, i ≠ 0 → i ≠ 37 → σ'.val (R i) = σ.val (R i)) →
      WExec cap pre (rst σ' (G 1) (G dst) (R 40) (R 41) (σ.st (G dst)) 0 out)
        (rst σ' (G 1) (G dst) (R 40) (R 41) (σ.st (G dst)) (skip0 * (2 * W + 2)) out) cpre)
    (hsz : skip0 + hh * b ≤ CR.length) (hcap : (CR.length + 1) * (2 * W + 2) + 2 < cap) (hh_cap : hh ≤ cap) :
    WExec cap (tabBlocks G R pre neg dst) σ (rst σ (G 1) (G dst) (R 40) (R 41) (σ.st (G dst)) 0
      ((List.range hh).flatMap (fun t => blkRecs b W (skip0 + (hh - 1 - t) * b) CR neg)))
      (tabBlocksCost cpre W hh b CR.length) := by
  have hAB : G 1 ≠ G dst := hG.ne (Ne.symm hdst)
  have hC : R 40 ≠ R 41 := hR.ne (by decide)
  have rne : ∀ a b : Fin 48, a ≠ b → R a ≠ R b := fun a b h => hR.ne h
  set L := σ.st (G dst) with hL
  have hcapn : CR.length * (2 * W + 2) + 2 < cap := by nlinarith
  let M : WState ns nr → ℕ → WState ns nr := fun σ' t => rst σ' (G 1) (G dst) (R 40) (R 41) L 0
    ((List.range t).flatMap (fun t' => blkRecs b W (skip0 + (hh - 1 - t') * b) CR neg))
  have loop := cloopMK cap (R 0) (R 37) (rne _ _ (by decide)) _ M
    (fun σ' j v w => rst_setv2 σ' L hAB hC (R 0) (R 37) v w (rne _ _ (by decide)) (rne _ _ (by decide))
      (rne _ _ (by decide)) (rne _ _ (by decide)) _ _) σ hh
    (cpre + 1 + ((hh - 0) * ((b * (13 * W + 13 + 8) + 1 + 1 + (7 * b + 1)) + 8) + 1 + 1 + (7 * hh + 1)) + 1 +
      (b * (40 * W + 40 + 8) + 1 + 1 + (7 * b + 1) + 1 + (5 * ((CR.length + 1) * (2 * W + 2)) + 1))) r0 r37 hh_cap (by
      intro t ht
      set σt := (σ.setv (R 0) (hh - t - 1)).setv (R 37) (t + 1) with hσt
      have v0 : σt.val (R 0) = hh - 1 - t := by simp [hσt, Function.update_apply, hR.eq_iff]; omega
      have vr : ∀ i : Fin 48, i ≠ 0 → i ≠ 37 → σt.val (R i) = σ.val (R i) := fun i a c => by
        simp [hσt, Function.update_apply, hR.eq_iff, a, c]
      set out := (List.range t).flatMap (fun t' => blkRecs b W (skip0 + (hh - 1 - t') * b) CR neg) with hout
      have hol : out.length = t * (b * (2 * W + 2)) := by
        rw [hout, List.length_flatMap]; simp [blkRecs_length, List.sum_replicate]
      have p0 := hpre σt out rfl rfl vr
      have jt : skip0 + (hh - 1 - t) * b + b ≤ CR.length := by
        have := Nat.mul_le_mul_right b (show hh - 1 - t + 1 ≤ hh by omega); rw [add_one_mul] at this; omega
      have sk := skipNN_rst cap σt L hAB hC (R 0) (R 38) (R 1) (R 39)
        (by have := List.Nodup.map hR (show ([0, 38, 1, 39, 40, 41] : List (Fin 48)).Nodup by decide); simpa using this)
        W CR post (by simp [hσt, hA]) skip0 (hh - 1 - t) b out v0 (by rw [vr 38 (by decide) (by decide)]; exact r38)
        (by rw [vr 1 (by decide) (by decide)]; exact r1) (by rw [vr 39 (by decide) (by decide)]; exact r39)
        (by omega) hcapn (by omega)
      have cp := copyN_rst cap σt L hAB hC neg (R 1) (R 38) (rne _ _ (by decide)) (rne _ _ (by decide))
        (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide)) W CR post (by simp [hσt, hA])
        (skip0 + (hh - 1 - t) * b) b out (by rw [vr 1 (by decide) (by decide)]; exact r1)
        (by rw [vr 38 (by decide) (by decide)]; exact r38) jt hcapn (by
          rw [hol]
          have := Nat.mul_le_mul_right (b * (2 * W + 2)) (show t + 1 ≤ hh by omega)
          have h2 : hh * b ≤ CR.length := by omega
          have := Nat.mul_le_mul_right (2 * W + 2) h2
          nlinarith)
      have rw1 := rewA_rst cap σt L hAB hC ((skip0 + (hh - 1 - t) * b + b) * (2 * W + 2))
        (out ++ blkRecs b W (skip0 + (hh - 1 - t) * b) CR neg)
        (by have := Nat.mul_le_mul_right (2 * W + 2) jt; nlinarith)
      have hall := WExec.seq p0 (WExec.seq sk (WExec.seq cp rw1))
      refine WExec.cast cap hall ?_ ?_
      · simp only [M, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rfl
      · have h5 : 5 * ((skip0 + (hh - 1 - t) * b + b) * (2 * W + 2)) + 1 ≤
            5 * ((CR.length + 1) * (2 * W + 2)) + 1 := by
          have := Nat.mul_le_mul_right (2 * W + 2) jt; nlinarith
        have hk : (hh - 1 - t) * (b * (13 * W + 13 + 8) + 1 + 1 + (7 * b + 1) + 8) ≤
            hh * (b * (13 * W + 13 + 8) + 1 + 1 + (7 * b + 1) + 8) := Nat.mul_le_mul_right _ (by omega)
        simp only [Nat.sub_zero]; omega)
  simp only [M, List.range_zero, List.flatMap_nil] at loop
  rw [rst_self σ hAB hC h1 r40 hd r41] at loop
  exact loop

end Blocks

/-- **The left table's program.** -/
def tabLP (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) : WM ns nr :=
  .seq (tabBlocks G R .skip true 6) (.seq (cloop (R 0) (R 37) (cloop (R 1) (R 38) (skipRec (G 1) (R 40))))
    (.seq (cloop (R 0) (R 37) (cloop (R 1) (R 38) (skipRec (G 1) (R 40))))
    (.seq (cloop (R 3) (R 37) (copyRec true (G 1) (G 6) (R 40) (R 41)))
    (.seq (WM.rewind (G 1) (R 40)) (WM.rewind (G 6) (R 41))))))

/-- **The right table's program.** -/
def tabRP (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) : WM ns nr :=
  .seq (tabBlocks G R (cloop (R 15) (R 38) (cloop (R 1) (R 39) (skipRec (G 1) (R 40)))) false 7)
    (.seq (cloop (R 0) (R 37) (cloop (R 1) (R 38) (skipRec (G 1) (R 40))))
    (.seq (cloop (R 0) (R 37) (cloop (R 1) (R 38) (skipRec (G 1) (R 40))))
    (.seq (cloop (R 3) (R 37) (skipRec (G 1) (R 40)))
    (.seq (cloop (R 4) (R 37) (copyRec false (G 1) (G 7) (R 40) (R 41)))
    (.seq (WM.rewind (G 1) (R 40)) (WM.rewind (G 7) (R 41)))))))

/-- The left table's cost. -/
def tabLCost (P : StarParams) (W : ℕ) : ℕ :=
  tabBlocksCost 0 W (hh P) P.b P.n + 1 + ((hh P * (P.b * (13 * W + 13 + 8) + 1 + 1 + (7 * P.b + 1) + 8) + 1 + 1 +
    (7 * hh P + 1)) + 1 + ((hh P * (P.b * (13 * W + 13 + 8) + 1 + 1 + (7 * P.b + 1) + 8) + 1 + 1 + (7 * hh P + 1)) + 1 +
    ((fL P * (40 * W + 40 + 8) + 1 + 1 + (7 * fL P + 1)) + 1 + ((5 * ((P.r * P.b + fL P) * (2 * W + 2)) + 1) + 1 +
    (5 * (lw P * (2 * W + 2)) + 1)))))

/-- The right table's cost. -/
def tabRCost (P : StarParams) (W : ℕ) : ℕ :=
  tabBlocksCost (hh P * (P.b * (13 * W + 13 + 8) + 1 + 1 + (7 * P.b + 1) + 8) + 1 + 1 + (7 * hh P + 1)) W (hh P) P.b P.n +
    1 + ((hh P * (P.b * (13 * W + 13 + 8) + 1 + 1 + (7 * P.b + 1) + 8) + 1 + 1 + (7 * hh P + 1)) + 1 +
    ((hh P * (P.b * (13 * W + 13 + 8) + 1 + 1 + (7 * P.b + 1) + 8) + 1 + 1 + (7 * hh P + 1)) + 1 +
    ((fL P * (13 * W + 13 + 8) + 1 + 1 + (7 * fL P + 1)) + 1 + ((fR P * (40 * W + 40 + 8) + 1 + 1 + (7 * fR P + 1)) + 1 +
    ((5 * ((P.r * P.b + fL P + fR P) * (2 * W + 2)) + 1) + 1 + (5 * (rw P * (2 * W + 2)) + 1))))))

section Tabs
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (P : StarParams) (W : ℕ) (g : NormalizedThresholdGate P.n) (cap : ℕ)
include hG hR

set_option maxHeartbeats 4000000 in
/-- **The left table**: `WTL := tbl W (recsL P g)` over its old contents. -/
theorem tabL_spec (σ : WState ns nr) (hGA : σ.st (G 1) = gateRec W g) (h1 : σ.sh (G 1) = 0) (h6 : σ.sh (G 6) = 0)
    (r0 : σ.val (R 0) = hh P) (r1 : σ.val (R 1) = P.b) (r3 : σ.val (R 3) = fL P) (r37 : σ.val (R 37) = 0)
    (r38 : σ.val (R 38) = 0) (r39 : σ.val (R 39) = 0) (r40 : σ.val (R 40) = 0) (r41 : σ.val (R 41) = 0)
    (hlen : (σ.st (G 6)).length ≤ lw P * (2 * W + 2)) (hcap : (P.n + 1) * (2 * W + 2) + 2 < cap) :
    WExec cap (tabLP G R) σ (σ.sets (G 6) (tbl W (recsL P g))) (tabLCost P W) := by
  obtain ⟨sz1, -, sz3, sz4, sz5, sz6, -, sz8⟩ := size_facts P
  have hAB : G 1 ≠ G 6 := hG.ne (by decide)
  have hC : R 40 ≠ R 41 := hR.ne (by decide)
  have rne : ∀ a b : Fin 48, a ≠ b → R a ≠ R b := fun a b h => hR.ne h
  set CR := coordRecs g with hCR
  have hA : σ.st (G 1) = tbl W CR ++ recBits W (decide (g.threshold < 0), g.threshold.natAbs) := by
    rw [hGA, gateRec_eq]
  have hn : CR.length = P.n := coordRecs_length g
  have hcapn : CR.length * (2 * W + 2) + 2 < cap := by rw [hn]; nlinarith
  have hfL : P.r * P.b + fL P ≤ P.n := by have := fL_fR P; have := rb_le P; omega
  have hncap : P.n + 1 ≤ cap := by nlinarith
  have hb2' := hb2 P
  have hrb := rb_le P
  have x1 := tabBlocks_spec G hG R hR cap W (hh P) P.b CR _ .skip true 6 (by decide) 0 0 σ hA h1 h6 r0 r1 r37
    r38 r39 r40 r41 (fun σ' out _ _ _ => by simpa using WExec.skip (cap := cap) _) (by rw [hn]; omega)
    (by rw [hn]; nlinarith) (by omega)
  set blocks := (List.range (hh P)).flatMap (fun t => blkRecs P.b W (0 + (hh P - 1 - t) * P.b) CR true) with hblocks
  have hbl : blocks.length = hh P * (P.b * (2 * W + 2)) := by
    rw [hblocks, List.length_flatMap]; simp [blkRecs_length, List.sum_replicate]
  have x2 := skipNN_rst cap σ (σ.st (G 6)) hAB hC (R 0) (R 37) (R 1) (R 38)
    (by have := List.Nodup.map hR (show ([0, 37, 1, 38, 40, 41] : List (Fin 48)).Nodup by decide); simpa using this)
    W CR _ hA 0 (hh P) P.b blocks r0 r37 r1 r38 (by rw [hn]; omega) hcapn (by omega)
  rw [Nat.zero_mul] at x2
  have x3 := skipNN_rst cap σ (σ.st (G 6)) hAB hC (R 0) (R 37) (R 1) (R 38)
    (by have := List.Nodup.map hR (show ([0, 37, 1, 38, 40, 41] : List (Fin 48)).Nodup by decide); simpa using this)
    W CR _ hA (0 + hh P * P.b) (hh P) P.b blocks r0 r37 r1 r38 (by rw [hn]; omega) hcapn (by omega)
  have e2 : 0 + hh P * P.b + hh P * P.b = P.r * P.b := by rw [← hb2 P]; ring
  rw [e2] at x3
  have x4 := copyN_rst cap σ (σ.st (G 6)) hAB hC true (R 3) (R 37) (rne _ _ (by decide)) (rne _ _ (by decide))
    (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide)) W CR _ hA (P.r * P.b) (fL P) blocks r3 r37
    (by rw [hn]; exact hfL) hcapn (by
      rw [hbl]
      have : hh P * P.b + fL P ≤ P.n := by omega
      have := Nat.mul_le_mul_right (2 * W + 2) this; nlinarith)
  set all := blocks ++ (List.range (fL P)).flatMap (fun i => recBits W (xor (recAt CR (P.r * P.b + i)).1 true,
    (recAt CR (P.r * P.b + i)).2)) with hall
  have x5 := rewA_rst cap σ (σ.st (G 6)) hAB hC ((P.r * P.b + fL P) * (2 * W + 2)) all
    (by have := Nat.mul_le_mul_right (2 * W + 2) hfL; nlinarith)
  have htbl : all = tbl W (recsL P g) := by
    rw [hall, hblocks, tblL_eq P g W]; simp [blkRecs, hCR]
  have hall_len : all.length ≤ cap := by
    rw [htbl, tbl_length, recsL_length]; unfold lw; nlinarith
  have x6 := rewB_rst cap σ (σ.st (G 6)) hAB hC h1 r40 h6 r41 all hall_len
  have eout : σ.sets (G 6) (overlay all (σ.st (G 6))) = σ.sets (G 6) (tbl W (recsL P g)) := by
    rw [overlay_full _ _ (by rw [htbl, tbl_length, recsL_length]; exact hlen), htbl]
  have hlw : all.length = lw P * (2 * W + 2) := by rw [htbl, tbl_length, recsL_length]
  rw [hn] at x1
  unfold tabLCost
  exact WExec.cast cap (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5 x6))))) eout
    (by rw [hlw])

set_option maxHeartbeats 4000000 in
/-- **The right table**: `WTR := tbl W (recsR P g)` over its old contents. -/
theorem tabR_spec (σ : WState ns nr) (hGA : σ.st (G 1) = gateRec W g) (h1 : σ.sh (G 1) = 0) (h7 : σ.sh (G 7) = 0)
    (r0 : σ.val (R 0) = hh P) (r1 : σ.val (R 1) = P.b) (r3 : σ.val (R 3) = fL P) (r4 : σ.val (R 4) = fR P)
    (r15 : σ.val (R 15) = hh P) (r37 : σ.val (R 37) = 0)
    (r38 : σ.val (R 38) = 0) (r39 : σ.val (R 39) = 0) (r40 : σ.val (R 40) = 0) (r41 : σ.val (R 41) = 0)
    (hlen : (σ.st (G 7)).length ≤ rw P * (2 * W + 2)) (hcap : (P.n + 1) * (2 * W + 2) + 2 < cap) :
    WExec cap (tabRP G R) σ (σ.sets (G 7) (tbl W (recsR P g))) (tabRCost P W) := by
  obtain ⟨sz1, sz2, sz3, sz4, sz5, sz6, sz7, sz8⟩ := size_facts P
  have hAB : G 1 ≠ G 7 := hG.ne (by decide)
  have hC : R 40 ≠ R 41 := hR.ne (by decide)
  have rne : ∀ a b : Fin 48, a ≠ b → R a ≠ R b := fun a b h => hR.ne h
  set CR := coordRecs g with hCR
  have hA : σ.st (G 1) = tbl W CR ++ recBits W (decide (g.threshold < 0), g.threshold.natAbs) := by
    rw [hGA, gateRec_eq]
  have hn : CR.length = P.n := coordRecs_length g
  have hcapn : CR.length * (2 * W + 2) + 2 < cap := by rw [hn]; nlinarith
  have hfLR := fL_fR P
  have hrb := rb_le P
  have hb2' := hb2 P
  have hncap : P.n + 1 ≤ cap := by nlinarith
  have x1 := tabBlocks_spec G hG R hR cap W (hh P) P.b CR _
    (cloop (R 15) (R 38) (cloop (R 1) (R 39) (skipRec (G 1) (R 40)))) false 7 (by decide) (hh P * P.b)
    (hh P * (P.b * (13 * W + 13 + 8) + 1 + 1 + (7 * P.b + 1) + 8) + 1 + 1 + (7 * hh P + 1)) σ hA h1 h7 r0 r1
    r37 r38 r39 r40 r41 (fun σ' out hst hsh hv => by
      have h := skipNN_rst cap σ' (σ.st (G 7)) hAB hC (R 15) (R 38) (R 1) (R 39)
        (by have := List.Nodup.map hR (show ([15, 38, 1, 39, 40, 41] : List (Fin 48)).Nodup by decide); simpa using this)
        W CR _ (by rw [hst]; exact hA) 0 (hh P) P.b out (by rw [hv 15 (by decide) (by decide)]; exact r15)
        (by rw [hv 38 (by decide) (by decide)]; exact r38) (by rw [hv 1 (by decide) (by decide)]; exact r1)
        (by rw [hv 39 (by decide) (by decide)]; exact r39) (by rw [hn]; omega) hcapn (by omega)
      simpa using h) (by rw [hn]; omega) (by rw [hn]; nlinarith) (by omega)
  set blocks := (List.range (hh P)).flatMap (fun t => blkRecs P.b W (hh P * P.b + (hh P - 1 - t) * P.b) CR false)
    with hblocks
  have hbl : blocks.length = hh P * (P.b * (2 * W + 2)) := by
    rw [hblocks, List.length_flatMap]; simp [blkRecs_length, List.sum_replicate]
  have x2 := skipNN_rst cap σ (σ.st (G 7)) hAB hC (R 0) (R 37) (R 1) (R 38)
    (by have := List.Nodup.map hR (show ([0, 37, 1, 38, 40, 41] : List (Fin 48)).Nodup by decide); simpa using this)
    W CR _ hA 0 (hh P) P.b blocks r0 r37 r1 r38 (by rw [hn]; omega) hcapn (by omega)
  rw [Nat.zero_mul] at x2
  have x3 := skipNN_rst cap σ (σ.st (G 7)) hAB hC (R 0) (R 37) (R 1) (R 38)
    (by have := List.Nodup.map hR (show ([0, 37, 1, 38, 40, 41] : List (Fin 48)).Nodup by decide); simpa using this)
    W CR _ hA (0 + hh P * P.b) (hh P) P.b blocks r0 r37 r1 r38 (by rw [hn]; omega) hcapn (by omega)
  have e2 : 0 + hh P * P.b + hh P * P.b = P.r * P.b := by rw [← hb2']; ring
  rw [e2] at x3
  have x4 := skipN_rst cap σ (σ.st (G 7)) hAB hC (R 3) (R 37) (rne _ _ (by decide)) (rne _ _ (by decide))
    (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide)) W CR _ hA (P.r * P.b) (fL P) blocks r3 r37
    (by rw [hn]; omega) hcapn
  have x5 := copyN_rst cap σ (σ.st (G 7)) hAB hC false (R 4) (R 37) (rne _ _ (by decide)) (rne _ _ (by decide))
    (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide)) W CR _ hA (P.r * P.b + fL P) (fR P) blocks r4 r37
    (by rw [hn]; omega) hcapn (by
      rw [hbl]
      have : hh P * P.b + fR P ≤ P.n := by omega
      have := Nat.mul_le_mul_right (2 * W + 2) this; nlinarith)
  set all := blocks ++ (List.range (fR P)).flatMap (fun i => recBits W (xor (recAt CR (P.r * P.b + fL P + i)).1 false,
    (recAt CR (P.r * P.b + fL P + i)).2)) with hall
  have x6 := rewA_rst cap σ (σ.st (G 7)) hAB hC ((P.r * P.b + fL P + fR P) * (2 * W + 2)) all
    (by have := Nat.mul_le_mul_right (2 * W + 2) (show P.r * P.b + fL P + fR P ≤ P.n by omega); nlinarith)
  have htbl : all = tbl W (recsR P g) := by
    rw [hall, hblocks, tblR_eq P g W]
    simp only [blkRecs, hCR, add_mul]
  have hall_len : all.length ≤ cap := by
    rw [htbl, tbl_length, recsR_length]; unfold rw; nlinarith
  have x7 := rewB_rst cap σ (σ.st (G 7)) hAB hC h1 r40 h7 r41 all hall_len
  have eout : σ.sets (G 7) (overlay all (σ.st (G 7))) = σ.sets (G 7) (tbl W (recsR P g)) := by
    rw [overlay_full _ _ (by rw [htbl, tbl_length, recsR_length]; exact hlen), htbl]
  have hrw : all.length = rw P * (2 * W + 2) := by rw [htbl, tbl_length, recsR_length]
  rw [hn] at x1
  unfold tabRCost
  exact WExec.cast cap (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5 (WExec.seq x6 x7))))))
    eout (by rw [hrw])

end Tabs

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
