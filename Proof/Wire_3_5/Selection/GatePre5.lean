import Proof.Wire_3_5.Selection.GatePre4

/-! # C1.4: the gate routine's zero words, key offset and level word (P3:1339-1358)

Paper: "For each gate and row, the four threshold predicates have integer scores of the form `a_j(z_L) + b_j(z_R)`"
(P3:1341-1342). The routine's words start at `0` (`zws`: the counters `X`, `U` and partners, `CI`, `SY`, the key and
magnitude words, the join words), the left words' offset is `TK = θ + 2^V` (`tkP`: `TK := 2^V`, then the threshold
record, at record `n` of the gate record, is added), and the level word is `PW = 2` (`pwP`). Main declarations:
`zwG`, **`tkP_spec`**, **`pwP_spec`**. Paper quantity: the threshold's key `θ + 2^V`. -/

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
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit (cloop cloop_spec)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

variable {ns nr : ℕ}

/-- A zero word's cost. -/
def zwCost (n : ℕ) : ℕ := n * (15 + 8) + 1 + 1 + (7 * n + 1) + 1 + (5 * (2 * n) + 14)

section Z
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (cap : ℕ)
include hG hR

/-- **A zero word on the gate layout**: `G z := frame (binary n 0)`, `n` in `R nr'`. -/
theorem zwG (z : Fin 28) (hz : z.val ≠ 2) (nr' : Fin 48) (hnr : nr'.val ≠ 37 ∧ nr'.val ≠ 40 ∧ nr'.val ≠ 44) (n : ℕ)
    (σ : WState ns nr) (hsh : ∀ i : Fin 28, σ.sh (G i) = 0) (h40 : σ.val (R 40) = 0) (h44 : σ.val (R 44) = 0)
    (h37 : σ.val (R 37) = 0) (hN : σ.val (R nr') = n) (hlen : (σ.st (G z)).length ≤ 2 * n + 1)
    (hcap : 2 * n + 2 ≤ cap) :
    WExec cap (zw (G z) (R 44) (R nr') (R 37)) σ (σ.sets (G z) (frame (binary n 0))) (zwCost n) := by
  have rne : ∀ a b : Fin 48, a.val ≠ b.val → R a ≠ R b := fun a b h => hR.ne (fun e => h (congrArg Fin.val e))
  exact zw_spec cap σ (A := G 2) (Z := G z) (CA := R 40) (CZ := R 44) (N := R nr') (T := R 37)
    (hG.ne (fun e => hz (congrArg Fin.val e).symm)) (rne _ _ (by decide)) (rne _ _ (by omega)) (rne _ _ (by omega))
    (rne _ _ (by omega)) (rne _ _ (by decide)) (rne _ _ (by decide)) n (hsh 2) h40 (hsh z) h44 hN h37 hlen hcap

end Z

theorem rst_nil (σ : WState ns nr) {A B : Fin (ns + 1)} {CA CB : Fin nr} (hAB : A ≠ B) (hC : CA ≠ CB)
    (hB : σ.sh B = 0) (hCB : σ.val CB = 0) (pA : ℕ) :
    rst σ A B CA CB (σ.st B) pA [] = (σ.seth A pA).setv CA pA := by
  apply WState.eq
  · funext j; simp only [rst, WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · funext j; simp only [rst, WState.setv_st, WState.seth_st, Function.update_apply]
    split_ifs with h
    · subst h; simp [overlay]
    · rfl
  · funext j; simp only [rst, WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl

/-- The key offset's program: `TK := 2^V`, then `+ θ` from the gate record's last record. -/
def tkP (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) : WM ns nr :=
  .seq (copyB (G 13) (G 2) (R 6) (R 7))
  (.seq (cloop (R 0) (R 37) (cloop (R 1) (R 38) (skipRec (G 1) (R 40))))
  (.seq (cloop (R 0) (R 37) (cloop (R 1) (R 38) (skipRec (G 1) (R 40))))
  (.seq (cloop (R 3) (R 37) (skipRec (G 1) (R 40)))
  (.seq (cloop (R 4) (R 37) (skipRec (G 1) (R 40)))
  (.seq (rdW (G 1) (G 12) (R 40) (R 10) (R 6) (R 7))
  (.seq (accW (G 13) (G 12) (R 10) (R 6) (R 7))
  (.seq (clrF (R 10))
  (.seq (zeroB (G 12) (G 10) (R 6) (R 7))
  (WM.rewind (G 1) (R 40))))))))))

/-- The key offset's cost. -/
def tkCost (P : StarParams) (W : ℕ) : ℕ :=
  41 * W + 3 + 1 + (hh P * (P.b * (13 * W + 13 + 8) + 1 + 1 + (7 * P.b + 1) + 8) + 1 + 1 + (7 * hh P + 1) + 1 + (hh P * (P.b * (13 * W + 13 + 8) + 1 + 1 + (7 * P.b + 1) + 8) + 1 + 1 + (7 * hh P + 1) + 1 + (fL P * (13 * W + 13 + 8) + 1 + 1 + (7 * fL P + 1) + 1 + (fR P * (13 * W + 13 + 8) + 1 + 1 + (7 * fR P + 1) + 1 + (54 * W + 23 + 1 + (41 * W + 10 + 1 + (2 + 1 + (41 * W + 3 + 1 + (5 * (P.n * (2 * W + 2) + 2 * W + 2) + 1)))))))))

section TK
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (P : StarParams) (W V : ℕ) (g : NormalizedThresholdGate P.n) (cap : ℕ)
include hG hR

set_option maxHeartbeats 4000000 in
/-- **The key offset**: `TK := θ + 2^V` (the threshold's key). -/
theorem tkP_spec (σ : WState ns nr) (hGA : σ.st (G 1) = gateRec W g) (hsh : ∀ i : Fin 28, σ.sh (G i) = 0)
    (hOF : σ.st (G 2) = frame (binary W (2 ^ V))) (hTK : σ.st (G 13) = frame (binary W 0))
    (hWV : σ.st (G 12) = frame (binary W 0)) (hAC : σ.st (G 10) = frame (binary W 0))
    (r0 : σ.val (R 0) = hh P) (r1 : σ.val (R 1) = P.b) (r3 : σ.val (R 3) = fL P) (r4 : σ.val (R 4) = fR P)
    (r6 : σ.val (R 6) = 0) (r7 : σ.val (R 7) = 0) (r10 : σ.val (R 10) = 0) (r37 : σ.val (R 37) = 0)
    (r38 : σ.val (R 38) = 0) (r40 : σ.val (R 40) = 0) (r41 : σ.val (R 41) = 0)
    (hθ : g.threshold.natAbs < 2 ^ V) (hVW : V + 1 < W) (hcap : (P.n + 1) * (2 * W + 2) + 2 < cap) :
    WExec cap (tkP G R) σ (σ.sets (G 13) (frame (binary W (keyOf V g.threshold)))) (tkCost P W) := by
  obtain ⟨sz1, sz2, sz3, sz4, sz5, sz6, sz7, sz8⟩ := size_facts P
  have hfLR := fL_fR P
  have hrb := rb_le P
  have hb2' := hb2 P
  have hncap : P.n + 1 ≤ cap := by nlinarith
  have hWcap : 2 * W + 2 < cap := by nlinarith
  have rne : ∀ a b : Fin 48, a ≠ b → R a ≠ R b := fun a b h => hR.ne h
  have gne : ∀ a b : Fin 28, a ≠ b → G a ≠ G b := fun a b h => hG.ne h
  have hAB : G 1 ≠ G 6 := gne _ _ (by decide)
  have hC : R 40 ≠ R 41 := rne _ _ (by decide)
  have hW2 : 2 ^ V < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- TK := 2^V
  have x1 := copyB_spec cap W (A := G 13) (B := G 2) (F := R 6) (R := R 7) (gne _ _ (by decide)) (rne _ _ (by decide))
    σ 0 (2 ^ V) ⟨hTK, hsh 13⟩ ⟨hOF, hsh 2⟩ r6 r7 (by omega)
  set σ1 := σ.sets (G 13) (frame (binary W (2 ^ V))) with hσ1
  set CR := coordRecs g with hCR
  have hA : σ1.st (G 1) = tbl W CR ++ recBits W (decide (g.threshold < 0), g.threshold.natAbs) := by
    rw [hσ1, WState.sets_st, Function.update_of_ne (gne _ _ (by decide)), hGA, gateRec_eq]
  have hn : CR.length = P.n := coordRecs_length g
  have hcapn : CR.length * (2 * W + 2) + 2 < cap := by rw [hn]; nlinarith
  -- GA's head to record n
  have e0 : rst σ1 (G 1) (G 6) (R 40) (R 41) (σ1.st (G 6)) (0 * (2 * W + 2)) [] = σ1 := by
    rw [Nat.zero_mul, rst_self σ1 hAB hC (hsh 1) r40 (hsh 6) r41]
  have x2 := skipNN_rst cap σ1 (σ1.st (G 6)) hAB hC (R 0) (R 37) (R 1) (R 38)
    (by have := List.Nodup.map hR (show ([0, 37, 1, 38, 40, 41] : List (Fin 48)).Nodup by decide); simpa using this)
    W CR _ hA 0 (hh P) P.b [] r0 r37 r1 r38 (by rw [hn]; omega) hcapn (by omega)
  rw [e0] at x2
  have x3 := skipNN_rst cap σ1 (σ1.st (G 6)) hAB hC (R 0) (R 37) (R 1) (R 38)
    (by have := List.Nodup.map hR (show ([0, 37, 1, 38, 40, 41] : List (Fin 48)).Nodup by decide); simpa using this)
    W CR _ hA (0 + hh P * P.b) (hh P) P.b [] r0 r37 r1 r38 (by rw [hn]; omega) hcapn (by omega)
  have e2 : 0 + hh P * P.b + hh P * P.b = P.r * P.b := by rw [← hb2']; ring
  rw [e2] at x3
  have x4 := skipN_rst cap σ1 (σ1.st (G 6)) hAB hC (R 3) (R 37) (rne _ _ (by decide)) (rne _ _ (by decide))
    (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide)) W CR _ hA (P.r * P.b) (fL P) [] r3 r37
    (by rw [hn]; omega) hcapn
  have x5 := skipN_rst cap σ1 (σ1.st (G 6)) hAB hC (R 4) (R 37) (rne _ _ (by decide)) (rne _ _ (by decide))
    (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide)) W CR _ hA (P.r * P.b + fL P) (fR P) [] r4 r37
    (by rw [hn]; omega) hcapn
  have en : P.r * P.b + fL P + fR P = P.n := by omega
  rw [en] at x5
  have x5' := WExec.cast cap x5 (rst_nil σ1 hAB hC (hsh 6) r41 _) le_rfl
  set pos := P.n * (2 * W + 2) with hpos
  -- read the threshold record
  have hlenT : (tbl W CR).length = pos := by rw [tbl_length, hn]
  have x6 := rdW_spec cap W (T := G 1) (V := G 12) (C := R 40) (SG := R 10) (F := R 6) (R := R 7)
    (gne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide))
    (rne _ _ (by decide)) (rne _ _ (by decide)) ((σ1.seth (G 1) pos).setv (R 40) pos) 0 g.threshold.natAbs
    (decide (g.threshold < 0)) (tbl W CR) []
    ⟨by simp [hσ1, Function.update_apply, hG.eq_iff, hWV], by simp [hσ1, Function.update_apply, hG.eq_iff, hsh 12]⟩
    (by simp [hA, recBits]) (by simp [hlenT]) (by simp [hlenT]) (by simp [hσ1, Function.update_apply, hR.eq_iff, r10])
    (by simp [hσ1, Function.update_apply, hR.eq_iff, r6]) (by simp [hσ1, Function.update_apply, hR.eq_iff, r7])
    (by rw [hlenT]; nlinarith)
  rw [hlenT] at x6
  set σ6 := (((((σ1.seth (G 1) pos).setv (R 40) pos).setv (R 10) (decide (g.threshold < 0)).toNat).sets (G 12)
    (frame (binary W g.threshold.natAbs))).seth (G 1) (pos + 2 * W + 2)).setv (R 40) (pos + 2 * W + 2) with hσ6
  -- TK := 2^V + θ
  have hsv : ((2 ^ V : ℕ) : ℤ) + sv (decide (g.threshold < 0)) g.threshold.natAbs = g.threshold + 2 ^ V := by
    rw [sv_pos]; push_cast; ring
  have hθ' : (g.threshold.natAbs : ℤ) < ((2 ^ V : ℕ) : ℤ) := by exact_mod_cast hθ
  have x7 := accR_spec cap W (A := G 13) (V := G 12) (SG := R 10) (F := R 6) (R := R 7) (gne _ _ (by decide))
    (rne _ _ (by decide)) σ6 (2 ^ V) g.threshold.natAbs (decide (g.threshold < 0))
    ⟨by simp [hσ6, hσ1, Function.update_apply, hG.eq_iff], by simp [hσ6, hσ1, Function.update_apply, hG.eq_iff, hsh 13]⟩
    ⟨by simp [hσ6, Function.update_apply, hG.eq_iff], by simp [hσ6, hσ1, Function.update_apply, hG.eq_iff, hsh 12]⟩
    (by simp [hσ6, Function.update_apply, hR.eq_iff])
    (by simp [hσ6, hσ1, Function.update_apply, hR.eq_iff, r6]) (by simp [hσ6, hσ1, Function.update_apply, hR.eq_iff, r7])
    (by rw [hsv]; rw [Int.natCast_natAbs] at hθ'; have := neg_abs_le g.threshold; push_cast at hθ' ⊢; linarith)
    (by rw [hsv]; rw [Int.natCast_natAbs] at hθ'; have := le_abs_self g.threshold;
        have h2 : ((2 : ℤ) ^ V) * 2 ≤ 2 ^ W := by
          rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
        push_cast at hθ' ⊢; linarith) hW2 (by omega)
  have hkey : ((((2 ^ V : ℕ) : ℤ) + sv (decide (g.threshold < 0)) g.threshold.natAbs)).toNat = keyOf V g.threshold := by
    rw [hsv]; unfold keyOf RepairOrdinary.SignedSortKey.shifted; push_cast; ring_nf
  rw [hkey] at x7
  set σ7 := σ6.sets (G 13) (frame (binary W (keyOf V g.threshold))) with hσ7
  -- SG := 0, WV := 0, GA's head back
  have x8 := clrF_spec cap (R 10) σ7 (by simp [hσ7, hσ6, Function.update_apply, hR.eq_iff]; cases decide (g.threshold < 0) <;> simp)
    (by omega)
  have x9 := zeroB_spec cap W (A := G 12) (B := G 10) (F := R 6) (R := R 7) (gne _ _ (by decide)) (rne _ _ (by decide))
    (σ7.setv (R 10) 0) g.threshold.natAbs 0
    ⟨by simp [hσ7, hσ6, Function.update_apply, hG.eq_iff], by simp [hσ7, hσ6, hσ1, Function.update_apply, hG.eq_iff, hsh 12]⟩
    ⟨by simp [hσ7, hσ6, hσ1, Function.update_apply, hG.eq_iff, hAC], by simp [hσ7, hσ6, hσ1, Function.update_apply,
      hG.eq_iff, hsh 10]⟩
    (by simp [hσ7, hσ6, hσ1, Function.update_apply, hR.eq_iff, r6])
    (by simp [hσ7, hσ6, hσ1, Function.update_apply, hR.eq_iff, r7])
    (by omega)
  have x10 := wrewind_spec cap (G 1) (R 40) (pos + 2 * W + 2) ((σ7.setv (R 10) 0).sets (G 12) (frame (binary W 0)))
    (by simp [hσ7, hσ6, Function.update_apply, hR.eq_iff]) (by simp [hσ7, hσ6, Function.update_apply, hR.eq_iff]; nlinarith)
  have efin : ((((σ7.setv (R 10) 0).sets (G 12) (frame (binary W 0))).setv (R 40) 0).seth (G 1)
      (((σ7.setv (R 10) 0).sets (G 12) (frame (binary W 0))).sh (G 1) - (pos + 2 * W + 2))) =
      σ.sets (G 13) (frame (binary W (keyOf V g.threshold))) := by
    apply WState.eq
    · funext j; simp only [hσ7, hσ6, hσ1, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext j; simp only [hσ7, hσ6, hσ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs with h1 h2 h3 <;> subst_vars <;> simp_all [hG.eq_iff]
    · funext j; simp only [hσ7, hσ6, hσ1, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [hR.eq_iff]
    · rfl
  rw [efin] at x10
  unfold tkP tkCost
  exact WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5' (WExec.seq x6 (WExec.seq x7 (WExec.seq x8
    (WExec.seq x9 x10))))))))

end TK

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
