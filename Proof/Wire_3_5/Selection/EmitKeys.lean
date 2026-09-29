import Proof.Wire_3_5.Selection.EmitLevel

/-! # C1.4: the six key writers of a point (P3:1345-1356)

Paper: "For each of the sixteen corner patterns, count pairs satisfying its four weak inequalities" (P3:1345-1346).
C1.1 turned the count into `2 + 2(V + 1)` `<`-joins (`gateJoin_tab`); each join's key stream is written point by point.
A point's two key words are `lo ≤ hi`; its tagged keys per join are:
* `Y`-joins: the right point's inner keys `2lo + 1`, `2hi + 1` (`EYR`); the left point's query `2hi` or `2lo` (`EY`);
* level `ℓ`: the left point's `lvlK1` query (`EK1`) and `lvlK3` query (`EK3`, from the word `hi + 2^(ℓ+1)`), the right
  point's `lvlK2` inner key (`EK2`, or the sentinel).
The emitters' registers are one injective map `E` (`0` the level `ℓ`, `1` the loop scratch, `2` `V + 1`, `3` `W − V − 2`,
`4` a zero, `5` `W`, `6` `W − 1`, `7` `2V + 3`, `8` `W − 2V − 3`, `9` the key stream's counter, `10`, `11` the pass
scratch, `12`, `13` the key words' counters). Main declarations: **`EK1_spec`**, **`EK2_spec`**, **`EK3_spec`**.
Paper quantity: a point's tagged level keys. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit (cloop cloop_spec)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.UnionMachine.Round (binary_succ)

variable {ns nr : ℕ}

/-- The level-`ℓ` query `lvlK1` (tagged `0`). -/
def EK1 (E : Fin 16 → Fin nr) (lo hi K : Fin (ns + 1)) (Clo Chi : Fin nr) : WM ns nr :=
  lvlE lo hi Clo Chi (E 0) (E 1) (cpB false lo hi K Clo Chi (E 9) (E 2) (E 3) (E 1)) (fxB hi K Chi (E 9) (E 4) (E 5) (E 1))

/-- The level-`ℓ` inner key `lvlK2` (tagged `1`), or the sentinel. -/
def EK2 (E : Fin 16 → Fin nr) (lo hi K : Fin (ns + 1)) (Clo Chi : Fin nr) : WM ns nr :=
  lvlE lo hi Clo Chi (E 0) (E 1) (fxB hi K Chi (E 9) (E 7) (E 8) (E 1)) (cpB true lo hi K Clo Chi (E 9) (E 2) (E 3) (E 1))

/-- The copying branch with a zero low part. -/
def cpZ (hi K : Fin (ns + 1)) (Chi CK N1 N2 T : Fin nr) : WM ns nr :=
  .seq (WM.fwdC hi Chi) (.seq (emitB K CK true) (.seq (emitB K CK false) (.seq (emitPairsN K CK N1 T false)
    (.seq (copyPairsN hi K Chi CK N2 T) (emitB K CK false)))))

/-- The level-`ℓ` query `lvlK3` (tagged `0`), from `HT := hi + 2^(ℓ+1)` (`PW` holds `2^(ℓ+1)`). -/
def EK3 (E : Fin 16 → Fin nr) (lo hi K HT PW : Fin (ns + 1)) (Clo CT : Fin nr) : WM ns nr :=
  .seq (copyB HT hi (E 10) (E 11)) (.seq (addB HT PW (E 10) (E 11))
    (.seq (lvlE lo HT Clo CT (E 0) (E 1) (cpZ HT K CT (E 9) (E 2) (E 3) (E 1)) (fxB HT K CT (E 9) (E 4) (E 5) (E 1)))
    (zeroB HT PW (E 10) (E 11))))

theorem frame_lvl0 (W V q : ℕ) (t : Bool) (hW : V + 2 ≤ W) :
    frame (binary W (2 * (q * 2 ^ (V + 1)) + t.toNat)) =
      [true, t] ++ frameP (binary (V + 1) 0) ++ frameP (binary (W - V - 2) q) ++ [false] := by
  have := frame_lvl W V q 0 t hW (Nat.two_pow_pos _)
  simpa using this

theorem kst_sets (σ : WState ns nr) (K i : Fin (ns + 1)) (CK : Fin nr) (L out l : List Bool) (hi : i ≠ K) :
    (kst σ K CK L out).sets i l = kst (σ.sets i l) K CK L out := by
  apply WState.eq
  · rfl
  · funext j; simp only [kst, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl
  · rfl

theorem kst_st (σ : WState ns nr) (K i : Fin (ns + 1)) (CK : Fin nr) (L out : List Bool) (hi : i ≠ K) :
    (kst σ K CK L out).st i = σ.st i := by simp [kst, hi]

theorem kst_sh (σ : WState ns nr) (K i : Fin (ns + 1)) (CK : Fin nr) (L out : List Bool) (hi : i ≠ K) :
    (kst σ K CK L out).sh i = σ.sh i := by simp [kst, hi]

theorem kst_val (σ : WState ns nr) (K : Fin (ns + 1)) (CK r : Fin nr) (L out : List Bool) (hr : r ≠ CK) :
    (kst σ K CK L out).val r = σ.val r := by simp [kst, hr]

section Zero
variable (cap : ℕ) (σ0 : WState ns nr) {lo hi K : Fin (ns + 1)} {Clo Chi CK T : Fin nr} (L : List Bool)
variable (h1 : lo ≠ hi) (h2 : lo ≠ K) (h3 : hi ≠ K) (c1 : Clo ≠ Chi) (c2 : Clo ≠ CK) (c3 : Chi ≠ CK)
variable (hT : T ≠ Clo ∧ T ≠ Chi ∧ T ≠ CK)
include h1 h2 h3 c1 c2 c3 hT

/-- **The copying branch with a zero low part.** -/
theorem cpZ_spec (N1 N2 : Fin nr) (hN1 : N1 ≠ Clo ∧ N1 ≠ Chi ∧ N1 ≠ CK ∧ N1 ≠ T)
    (hN2 : N2 ≠ Clo ∧ N2 ≠ Chi ∧ N2 ≠ CK ∧ N2 ≠ T) (n1 : ℕ) (bh preh resth : List Bool) (out : List Bool)
    (hhi : σ0.st hi = preh ++ frameP bh ++ resth)
    (hn1 : σ0.val N1 = n1) (hn2 : σ0.val N2 = bh.length) (hT0 : σ0.val T = 0)
    (hcap : out.length + 2 * n1 + 2 * bh.length + 3 ≤ cap) (hc1 : n1 ≤ cap)
    (hch : preh.length + 2 * bh.length ≤ cap) (hp : 1 ≤ preh.length) :
    WExec cap (cpZ hi K Chi CK N1 N2 T) (est σ0 lo hi K Clo Chi CK L 0 (preh.length - 1) out)
      (est σ0 lo hi K Clo Chi CK L 0 (preh.length + 2 * bh.length)
        (out ++ [true, false] ++ frameP (List.replicate n1 false) ++ frameP bh ++ [false]))
      (50 * n1 + 50 * bh.length + 40) := by
  have hsw := est_swap σ0 L h1 h2 h3 c1 c2 c3
  have f1 := fwdA_rst cap ((σ0.seth lo 0).setv Clo 0) L h3 c3 (preh.length - 1) out (by omega)
  rw [show preh.length - 1 + 1 = preh.length by omega] at f1
  rw [← hsw, ← hsw] at f1
  have e1 := emitB_rst cap ((σ0.seth hi preh.length).setv Chi preh.length) L h2 c2 0 out true (by omega)
  have e2 := emitB_rst cap ((σ0.seth hi preh.length).setv Chi preh.length) L h2 c2 0 (out ++ [true]) false
    (by simp; omega)
  have k1 := emitPairs_rst cap ((σ0.seth hi preh.length).setv Chi preh.length) L h2 c2 N1 T hN1.2.2.2 hN1.1
    hN1.2.2.1 hT.1 hT.2.2 false n1 0 (out ++ [true] ++ [false]) (by simp [Function.update_apply, hN1.2.1, hn1])
    (by simp [Function.update_apply, hT.2.1, hT0]) hc1 (by simp; omega)
  have k2 := copyPairs_rst cap ((σ0.seth lo 0).setv Clo 0) L h3 c3 N2 T hN2.2.2.2 hN2.2.1
    hN2.2.2.1 hT.2.1 hT.2.2 preh bh resth (out ++ [true] ++ [false] ++ frameP (List.replicate n1 false))
    (by simp [hhi, Ne.symm h1]) (by simp [Function.update_apply, hN2.1, hn2]) (by simp [Function.update_apply, hT.1, hT0])
    hch (by simp; omega)
  have k2' := WExec.cast cap k2 (hsw 0 (preh.length + 2 * bh.length) _).symm le_rfl
  have e3 := emitB_rst cap ((σ0.seth hi (preh.length + 2 * bh.length)).setv Chi (preh.length + 2 * bh.length)) L h2 c2
    0 (out ++ [true] ++ [false] ++ frameP (List.replicate n1 false) ++ frameP bh) false (by simp; omega)
  have k1' := WExec.cast cap k1 (hsw 0 preh.length _) le_rfl
  have hall := WExec.seq f1 (WExec.seq e1 (WExec.seq e2 (WExec.seq k1' (WExec.seq k2' e3))))
  unfold cpZ
  refine WExec.cast cap hall ?_ (by omega)
  simp [est, List.append_assoc]

end Zero

section Keys
variable (cap : ℕ) (σ0 : WState ns nr) {E : Fin 16 → Fin nr} (hE : Function.Injective E)
variable {lo hi K : Fin (ns + 1)} {Clo Chi : Fin nr} (L : List Bool)
variable (h1 : lo ≠ hi) (h2 : lo ≠ K) (h3 : hi ≠ K) (c1 : Clo ≠ Chi) (hClo : ∀ i, E i ≠ Clo) (hChi : ∀ i, E i ≠ Chi)
include hE h1 h2 h3 c1 hClo hChi

/-- **The `lvlK1` query of a point.** -/
theorem EK1_spec (W V ℓ vlo vhi : ℕ) (out : List Bool) (hW : 2 * V + 3 ≤ W) (hℓ : ℓ ≤ V) (hvlo : vlo < 2 ^ (V + 1))
    (hlo : σ0.st lo = frame (binary W vlo)) (hhi : σ0.st hi = frame (binary W vhi))
    (hlo0 : σ0.sh lo = 0) (hhi0 : σ0.sh hi = 0) (hClo0 : σ0.val Clo = 0) (hChi0 : σ0.val Chi = 0)
    (e0 : σ0.val (E 0) = ℓ) (e1 : σ0.val (E 1) = 0) (e2 : σ0.val (E 2) = V + 1) (e3 : σ0.val (E 3) = W - V - 2)
    (e4 : σ0.val (E 4) = 0) (e5 : σ0.val (E 5) = W) (hcap : out.length + 4 * W + 8 ≤ cap) :
    WExec cap (EK1 E lo hi K Clo Chi) (kst σ0 K (E 9) L out)
      (kst σ0 K (E 9) L (out ++ frame (binary W (2 * (if vhi.testBit ℓ then vhi / 2 ^ (ℓ + 1) * 2 ^ (V + 1) + vlo
        else 0) + (false).toNat)))) (200 * W + 200) := by
  have c2 : Clo ≠ E 9 := Ne.symm (hClo 9)
  have c3 : Chi ≠ E 9 := Ne.symm (hChi 9)
  have hT : E 1 ≠ Clo ∧ E 1 ≠ Chi ∧ E 1 ≠ E 9 := ⟨hClo 1, hChi 1, hE.ne (by decide)⟩
  have hLV : E 0 ≠ Clo ∧ E 0 ≠ Chi ∧ E 0 ≠ E 9 ∧ E 0 ≠ E 1 := ⟨hClo 0, hChi 0, hE.ne (by decide), hE.ne (by decide)⟩
  have hsplit := frame_seg W (ℓ + 1) (W - V - 2) vhi (by omega)
  by_cases hb : vhi.testBit ℓ = true
  · have hbr : WExec cap (.ifs hi (cpB false lo hi K Clo Chi (E 9) (E 2) (E 3) (E 1)) (fxB hi K Chi (E 9) (E 4) (E 5) (E 1)))
        (est σ0 lo hi K Clo Chi (E 9) L 0 (2 * ℓ + 1) out)
        (est σ0 lo hi K Clo Chi (E 9) L (2 * (V + 1)) (2 * (ℓ + 1) + 2 * (W - V - 2))
          (out ++ ([true, false] ++ frameP (binary (V + 1) vlo) ++ frameP (binary (W - V - 2) (vhi / 2 ^ (ℓ + 1))) ++
            [false]))) (50 * (V + 1) + 50 * (W - V - 2) + 41) := by
      have hbit : wbit (est σ0 lo hi K Clo Chi (E 9) L 0 (2 * ℓ + 1) out) hi = true := by
        rw [est_swap σ0 L h1 h2 h3 c1 c2 c3, rst_bitA _ L h3 c3]
        simp only [WState.setv_st, WState.seth_st, hhi]
        rw [rd_frame_bit W vhi ℓ (by omega)]; exact hb
      have h := cpB_spec cap σ0 L h1 h2 h3 c1 c2 c3 hT false (E 2) (E 3)
        ⟨hClo 2, hChi 2, hE.ne (by decide), hE.ne (by decide)⟩ ⟨hClo 3, hChi 3, hE.ne (by decide), hE.ne (by decide)⟩
        (binary (V + 1) vlo) (binary (W - V - 2) (vhi / 2 ^ (ℓ + 1))) (frameP (binary (ℓ + 1) vhi))
        (frameP (binary (W - (ℓ + 1) - (W - V - 2)) (vhi / 2 ^ (ℓ + 1) / 2 ^ (W - V - 2))) ++ [false])
        (frameP (binary (W - (V + 1)) (vlo / 2 ^ (V + 1))) ++ [false]) out
        (by rw [hlo]; exact frame_low W V vlo (by omega)) (by rw [hhi, hsplit])
        (by simp [e2]) (by simp [e3]) e1 (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega)
      simp only [frameP_length, binary_length, show 2 * (ℓ + 1) - 1 = 2 * ℓ + 1 by omega] at h
      refine WExec.cast cap (WExec.ifsT hbit h) ?_ (by omega)
      simp only [List.append_assoc]
    have hl := lvlE_spec cap σ0 L h1 h2 h3 c1 c2 c3 hT hLV _ _ ℓ _ _ _ out _ hlo0 hhi0 hClo0 hChi0 e0 e1 (by omega)
      (by omega) (by omega) hbr
    unfold EK1
    refine WExec.cast cap hl ?_ (by omega)
    rw [if_pos hb, frame_lvl W V _ vlo false (by omega) hvlo]
  · have hb' : vhi.testBit ℓ = false := by simpa using hb
    have hbr : WExec cap (.ifs hi (cpB false lo hi K Clo Chi (E 9) (E 2) (E 3) (E 1)) (fxB hi K Chi (E 9) (E 4) (E 5) (E 1)))
        (est σ0 lo hi K Clo Chi (E 9) L 0 (2 * ℓ + 1) out)
        (est σ0 lo hi K Clo Chi (E 9) L 0 (2 * ℓ + 1 + 1)
          (out ++ (frameP (List.replicate 0 true) ++ frameP (List.replicate W false) ++ [false])))
        (40 * 0 + 40 * W + 31) := by
      have hbit : wbit (est σ0 lo hi K Clo Chi (E 9) L 0 (2 * ℓ + 1) out) hi = false := by
        rw [est_swap σ0 L h1 h2 h3 c1 c2 c3, rst_bitA _ L h3 c3]
        simp only [WState.setv_st, WState.seth_st, hhi]
        rw [rd_frame_bit W vhi ℓ (by omega)]; exact hb'
      have h := fxB_spec cap σ0 L h1 h2 h3 c1 c2 c3 hT (E 4) (E 5)
        ⟨hClo 4, hChi 4, hE.ne (by decide), hE.ne (by decide)⟩ ⟨hClo 5, hChi 5, hE.ne (by decide), hE.ne (by decide)⟩
        0 W (2 * ℓ + 1) out e4 e5 e1 (by omega) (by omega) (by omega) (by omega)
      refine WExec.cast cap (WExec.ifsF hbit h) ?_ (by omega)
      simp only [List.append_assoc]
    have hl := lvlE_spec cap σ0 L h1 h2 h3 c1 c2 c3 hT hLV _ _ ℓ _ _ _ out _ hlo0 hhi0 hClo0 hChi0 e0 e1 (by omega)
      (by omega) (by omega) hbr
    unfold EK1
    refine WExec.cast cap hl ?_ (by omega)
    rw [if_neg hb]
    simp [frame_eq_frameP, binary_zero_rep]

set_option maxHeartbeats 1000000 in
/-- **The `lvlK2` inner key of a point** (or the sentinel `2^(2V+2) − 1`). -/
theorem EK2_spec (W V ℓ vlo vhi : ℕ) (out : List Bool) (hW : 2 * V + 3 ≤ W) (hℓ : ℓ ≤ V) (hvlo : vlo < 2 ^ (V + 1))
    (hlo : σ0.st lo = frame (binary W vlo)) (hhi : σ0.st hi = frame (binary W vhi))
    (hlo0 : σ0.sh lo = 0) (hhi0 : σ0.sh hi = 0) (hClo0 : σ0.val Clo = 0) (hChi0 : σ0.val Chi = 0)
    (e0 : σ0.val (E 0) = ℓ) (e1 : σ0.val (E 1) = 0) (e2 : σ0.val (E 2) = V + 1) (e3 : σ0.val (E 3) = W - V - 2)
    (e7 : σ0.val (E 7) = 2 * V + 3) (e8 : σ0.val (E 8) = W - (2 * V + 3)) (hcap : out.length + 4 * W + 8 ≤ cap) :
    WExec cap (EK2 E lo hi K Clo Chi) (kst σ0 K (E 9) L out)
      (kst σ0 K (E 9) L (out ++ frame (binary W (2 * (if vhi.testBit ℓ then 2 ^ (2 * (V + 1)) - 1
        else vhi / 2 ^ (ℓ + 1) * 2 ^ (V + 1) + vlo) + (true).toNat)))) (200 * W + 200) := by
  have c2 : Clo ≠ E 9 := Ne.symm (hClo 9)
  have c3 : Chi ≠ E 9 := Ne.symm (hChi 9)
  have hT : E 1 ≠ Clo ∧ E 1 ≠ Chi ∧ E 1 ≠ E 9 := ⟨hClo 1, hChi 1, hE.ne (by decide)⟩
  have hLV : E 0 ≠ Clo ∧ E 0 ≠ Chi ∧ E 0 ≠ E 9 ∧ E 0 ≠ E 1 := ⟨hClo 0, hChi 0, hE.ne (by decide), hE.ne (by decide)⟩
  have hsplit := frame_seg W (ℓ + 1) (W - V - 2) vhi (by omega)
  by_cases hb : vhi.testBit ℓ = true
  · have hbr : WExec cap (.ifs hi (fxB hi K Chi (E 9) (E 7) (E 8) (E 1))
        (cpB true lo hi K Clo Chi (E 9) (E 2) (E 3) (E 1)))
        (est σ0 lo hi K Clo Chi (E 9) L 0 (2 * ℓ + 1) out)
        (est σ0 lo hi K Clo Chi (E 9) L 0 (2 * ℓ + 1 + 1)
          (out ++ (frameP (List.replicate (2 * V + 3) true) ++ frameP (List.replicate (W - (2 * V + 3)) false) ++
            [false]))) (40 * (2 * V + 3) + 40 * (W - (2 * V + 3)) + 31) := by
      have hbit : wbit (est σ0 lo hi K Clo Chi (E 9) L 0 (2 * ℓ + 1) out) hi = true := by
        rw [est_swap σ0 L h1 h2 h3 c1 c2 c3, rst_bitA _ L h3 c3]
        simp only [WState.setv_st, WState.seth_st, hhi]
        rw [rd_frame_bit W vhi ℓ (by omega)]; exact hb
      have h := fxB_spec cap σ0 L h1 h2 h3 c1 c2 c3 hT (E 7) (E 8)
        ⟨hClo 7, hChi 7, hE.ne (by decide), hE.ne (by decide)⟩ ⟨hClo 8, hChi 8, hE.ne (by decide), hE.ne (by decide)⟩
        (2 * V + 3) (W - (2 * V + 3)) (2 * ℓ + 1) out e7 e8 e1 (by omega) (by omega) (by omega) (by omega)
      refine WExec.cast cap (WExec.ifsT hbit h) ?_ (by omega)
      simp only [List.append_assoc]
    have hl := lvlE_spec cap σ0 L h1 h2 h3 c1 c2 c3 hT hLV _ _ ℓ _ _ _ out _ hlo0 hhi0 hClo0 hChi0 e0 e1 (by omega)
      (by omega) (by omega) hbr
    unfold EK2
    refine WExec.cast cap hl ?_ (by omega)
    rw [if_pos hb]
    have e : 2 * (2 ^ (2 * (V + 1)) - 1) + (true).toNat = 2 ^ (2 * V + 3) - 1 := by
      have := Nat.one_le_two_pow (n := 2 * (V + 1))
      rw [show 2 * V + 3 = 2 * (V + 1) + 1 by ring, pow_succ]; simp; omega
    rw [e, frame_fix W (2 * V + 3) hW]
  · have hb' : vhi.testBit ℓ = false := by simpa using hb
    have hbr : WExec cap (.ifs hi (fxB hi K Chi (E 9) (E 7) (E 8) (E 1))
        (cpB true lo hi K Clo Chi (E 9) (E 2) (E 3) (E 1)))
        (est σ0 lo hi K Clo Chi (E 9) L 0 (2 * ℓ + 1) out)
        (est σ0 lo hi K Clo Chi (E 9) L (2 * (V + 1)) (2 * (ℓ + 1) + 2 * (W - V - 2))
          (out ++ ([true, true] ++ frameP (binary (V + 1) vlo) ++ frameP (binary (W - V - 2) (vhi / 2 ^ (ℓ + 1))) ++
            [false]))) (50 * (V + 1) + 50 * (W - V - 2) + 41) := by
      have hbit : wbit (est σ0 lo hi K Clo Chi (E 9) L 0 (2 * ℓ + 1) out) hi = false := by
        rw [est_swap σ0 L h1 h2 h3 c1 c2 c3, rst_bitA _ L h3 c3]
        simp only [WState.setv_st, WState.seth_st, hhi]
        rw [rd_frame_bit W vhi ℓ (by omega)]; exact hb'
      have h := cpB_spec cap σ0 L h1 h2 h3 c1 c2 c3 hT true (E 2) (E 3)
        ⟨hClo 2, hChi 2, hE.ne (by decide), hE.ne (by decide)⟩ ⟨hClo 3, hChi 3, hE.ne (by decide), hE.ne (by decide)⟩
        (binary (V + 1) vlo) (binary (W - V - 2) (vhi / 2 ^ (ℓ + 1))) (frameP (binary (ℓ + 1) vhi))
        (frameP (binary (W - (ℓ + 1) - (W - V - 2)) (vhi / 2 ^ (ℓ + 1) / 2 ^ (W - V - 2))) ++ [false])
        (frameP (binary (W - (V + 1)) (vlo / 2 ^ (V + 1))) ++ [false]) out
        (by rw [hlo]; exact frame_low W V vlo (by omega)) (by rw [hhi, hsplit])
        (by simp [e2]) (by simp [e3]) e1 (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega)
      simp only [frameP_length, binary_length, show 2 * (ℓ + 1) - 1 = 2 * ℓ + 1 by omega] at h
      refine WExec.cast cap (WExec.ifsF hbit h) ?_ (by omega)
      simp only [List.append_assoc]
    have hl := lvlE_spec cap σ0 L h1 h2 h3 c1 c2 c3 hT hLV _ _ ℓ _ _ _ out _ hlo0 hhi0 hClo0 hChi0 e0 e1 (by omega)
      (by omega) (by omega) hbr
    unfold EK2
    refine WExec.cast cap hl ?_ (by omega)
    rw [if_neg hb, frame_lvl W V _ vlo true (by omega) hvlo]

end Keys

section K3
variable (cap : ℕ) (σ0 : WState ns nr) {E : Fin 16 → Fin nr} (hE : Function.Injective E)
variable {lo hi K HT PW : Fin (ns + 1)} {Clo CT : Fin nr} (L : List Bool)
variable (h1 : lo ≠ HT) (h2 : lo ≠ K) (h3 : HT ≠ K) (h4 : hi ≠ HT) (h5 : HT ≠ PW) (h6 : PW ≠ K) (h7 : hi ≠ K)
  (c1 : Clo ≠ CT) (hClo : ∀ i, E i ≠ Clo) (hCT : ∀ i, E i ≠ CT)
include hE h1 h2 h3 h4 h5 h6 h7 c1 hClo hCT

set_option maxHeartbeats 1000000 in
/-- **The `lvlK3` query of a point**, through the word `HT = hi + 2^(ℓ+1)` (back to `0` after). -/
theorem EK3_spec (W V ℓ vhi : ℕ) (out : List Bool) (hW : 2 * V + 3 ≤ W) (hℓ : ℓ ≤ V) (hvhi : vhi < 2 ^ (V + 1))
    (hhi : NumOn σ0 hi W vhi) (hHT : NumOn σ0 HT W 0) (hPW : NumOn σ0 PW W (2 ^ (ℓ + 1)))
    (hlo0 : σ0.sh lo = 0) (hClo0 : σ0.val Clo = 0) (hCT0 : σ0.val CT = 0)
    (e0 : σ0.val (E 0) = ℓ) (e1 : σ0.val (E 1) = 0) (e2 : σ0.val (E 2) = V + 1) (e3 : σ0.val (E 3) = W - V - 2)
    (e4 : σ0.val (E 4) = 0) (e5 : σ0.val (E 5) = W) (e10 : σ0.val (E 10) = 0) (e11 : σ0.val (E 11) = 0)
    (hcap : out.length + 4 * W + 8 ≤ cap) :
    WExec cap (EK3 E lo hi K HT PW Clo CT) (kst σ0 K (E 9) L out)
      (kst σ0 K (E 9) L (out ++ frame (binary W (2 * (if vhi.testBit ℓ then (vhi / 2 ^ (ℓ + 1) + 1) * 2 ^ (V + 1)
        else 0) + (false).toNat)))) (400 * W + 300) := by
  have c2 : Clo ≠ E 9 := Ne.symm (hClo 9)
  have c3 : CT ≠ E 9 := Ne.symm (hCT 9)
  have hT : E 1 ≠ Clo ∧ E 1 ≠ CT ∧ E 1 ≠ E 9 := ⟨hClo 1, hCT 1, hE.ne (by decide)⟩
  have hLV : E 0 ≠ Clo ∧ E 0 ≠ CT ∧ E 0 ≠ E 9 ∧ E 0 ≠ E 1 := ⟨hClo 0, hCT 0, hE.ne (by decide), hE.ne (by decide)⟩
  have hp : 2 ^ (ℓ + 1) ≤ 2 ^ (V + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hV2 : 2 ^ (V + 2) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hV2' : 2 ^ (V + 2) = 2 ^ (V + 1) + 2 ^ (V + 1) := by rw [pow_succ]; ring
  set vht := vhi + 2 ^ (ℓ + 1) with hvht
  -- HT := hi, HT += 2^(ℓ+1)
  have x1 := copyB_spec cap W (A := HT) (B := hi) (F := E 10) (R := E 11) (Ne.symm h4) (hE.ne (by decide))
    (kst σ0 K (E 9) L out) 0 vhi
    ⟨by rw [kst_st _ _ _ _ _ _ h3]; exact hHT.1, by rw [kst_sh _ _ _ _ _ _ h3]; exact hHT.2⟩
    ⟨by rw [kst_st _ _ _ _ _ _ h7]; exact hhi.1, by rw [kst_sh _ _ _ _ _ _ h7]; exact hhi.2⟩
    (by rw [kst_val _ _ _ _ _ _ (hE.ne (by decide))]; exact e10) (by rw [kst_val _ _ _ _ _ _ (hE.ne (by decide))]; exact e11)
    (by omega)
  rw [kst_sets _ _ _ _ _ _ _ h3] at x1
  set σ1 := σ0.sets HT (frame (binary W vhi)) with hσ1
  have x2 := addB_spec cap W (A := HT) (B := PW) (F := E 10) (R := E 11) h5 (hE.ne (by decide))
    (kst σ1 K (E 9) L out) vhi (2 ^ (ℓ + 1))
    ⟨by rw [kst_st _ _ _ _ _ _ h3]; simp [hσ1], by rw [kst_sh _ _ _ _ _ _ h3]; simp [hσ1, hHT.2]⟩
    ⟨by rw [kst_st _ _ _ _ _ _ h6]; simp [hσ1, Ne.symm h5, hPW.1], by rw [kst_sh _ _ _ _ _ _ h6]; simp [hσ1, hPW.2]⟩
    (by rw [kst_val _ _ _ _ _ _ (hE.ne (by decide))]; simp [hσ1, e10])
    (by rw [kst_val _ _ _ _ _ _ (hE.ne (by decide))]; simp [hσ1, e11]) (by omega) (by omega)
  rw [kst_sets _ _ _ _ _ _ _ h3] at x2
  set σ2 := σ1.sets HT (frame (binary W vht)) with hσ2
  have hσ2st : σ2.st HT = frame (binary W vht) := by simp [hσ2]
  -- the level emitter on lo and HT
  have hsplit := frame_seg W (ℓ + 1) (W - V - 2) vht (by omega)
  have hbit_eq : vht.testBit ℓ = vhi.testBit ℓ := by
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hvht,
      show 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ by ring, Nat.add_mul_div_right _ _ (Nat.two_pow_pos ℓ), Nat.add_mod_right]
  have hq : vht / 2 ^ (ℓ + 1) = vhi / 2 ^ (ℓ + 1) + 1 := by
    rw [hvht, Nat.add_div_right _ (Nat.two_pow_pos _)]
  have hsh2 : σ2.sh HT = 0 := by simp [hσ2, hσ1, hHT.2]
  have hlo2 : σ2.sh lo = 0 := by simp [hσ2, hσ1, hlo0]
  by_cases hb : vhi.testBit ℓ = true
  · have hbr : WExec cap (.ifs HT (cpZ HT K CT (E 9) (E 2) (E 3) (E 1)) (fxB HT K CT (E 9) (E 4) (E 5) (E 1)))
        (est σ2 lo HT K Clo CT (E 9) L 0 (2 * ℓ + 1) out)
        (est σ2 lo HT K Clo CT (E 9) L 0 (2 * (ℓ + 1) + 2 * (W - V - 2))
          (out ++ ([true, false] ++ frameP (List.replicate (V + 1) false) ++
            frameP (binary (W - V - 2) (vht / 2 ^ (ℓ + 1))) ++ [false]))) (50 * (V + 1) + 50 * (W - V - 2) + 41) := by
      have hbit : wbit (est σ2 lo HT K Clo CT (E 9) L 0 (2 * ℓ + 1) out) HT = true := by
        rw [est_swap σ2 L h1 h2 h3 c1 c2 c3, rst_bitA _ L h3 c3]
        simp only [WState.setv_st, WState.seth_st, hσ2st]
        rw [rd_frame_bit W vht ℓ (by omega), hbit_eq]; exact hb
      have h := cpZ_spec cap σ2 L h1 h2 h3 c1 c2 c3 hT (E 2) (E 3)
        ⟨hClo 2, hCT 2, hE.ne (by decide), hE.ne (by decide)⟩ ⟨hClo 3, hCT 3, hE.ne (by decide), hE.ne (by decide)⟩
        (V + 1) (binary (W - V - 2) (vht / 2 ^ (ℓ + 1))) (frameP (binary (ℓ + 1) vht))
        (frameP (binary (W - (ℓ + 1) - (W - V - 2)) (vht / 2 ^ (ℓ + 1) / 2 ^ (W - V - 2))) ++ [false]) out
        (by rw [hσ2st, hsplit]) (by simp [hσ2, hσ1, e2]) (by simp [hσ2, hσ1, e3]) (by simp [hσ2, hσ1, e1])
        (by simp; omega) (by omega) (by simp; omega) (by simp; omega)
      simp only [frameP_length, binary_length, show 2 * (ℓ + 1) - 1 = 2 * ℓ + 1 by omega] at h
      refine WExec.cast cap (WExec.ifsT hbit h) ?_ (by omega)
      simp only [List.append_assoc]
    have hl := lvlE_spec cap σ2 L h1 h2 h3 c1 c2 c3 hT hLV _ _ ℓ _ _ _ out _ hlo2 hsh2 (by simp [hσ2, hσ1, hClo0])
      (by simp [hσ2, hσ1, hCT0]) (by simp [hσ2, hσ1, e0]) (by simp [hσ2, hσ1, e1]) (by omega) (by omega) (by omega) hbr
    have x4 := zeroB_spec cap W (A := HT) (B := PW) (F := E 10) (R := E 11) h5 (hE.ne (by decide))
      (kst σ2 K (E 9) L (out ++ ([true, false] ++ frameP (List.replicate (V + 1) false) ++
        frameP (binary (W - V - 2) (vht / 2 ^ (ℓ + 1))) ++ [false]))) vht (2 ^ (ℓ + 1))
      ⟨by rw [kst_st _ _ _ _ _ _ h3]; exact hσ2st, by rw [kst_sh _ _ _ _ _ _ h3]; exact hsh2⟩
      ⟨by rw [kst_st _ _ _ _ _ _ h6]; simp [hσ2, hσ1, Ne.symm h5, hPW.1], by rw [kst_sh _ _ _ _ _ _ h6]; simp [hσ2, hσ1, hPW.2]⟩
      (by rw [kst_val _ _ _ _ _ _ (hE.ne (by decide))]; simp [hσ2, hσ1, e10])
      (by rw [kst_val _ _ _ _ _ _ (hE.ne (by decide))]; simp [hσ2, hσ1, e11]) (by omega)
    rw [kst_sets _ _ _ _ _ _ _ h3] at x4
    have eback : σ2.sets HT (frame (binary W 0)) = σ0 := by
      apply WState.eq
      · rfl
      · funext j; simp only [hσ2, hσ1, WState.sets_st, Function.update_apply]
        split_ifs with h
        · subst h; exact hHT.1.symm
        · rfl
      · rfl
      · rfl
    rw [eback] at x4
    have hall := WExec.seq x1 (WExec.seq x2 (WExec.seq hl x4))
    unfold EK3
    refine WExec.cast cap hall ?_ (by omega)
    rw [if_pos hb, ← hq, frame_lvl0 W V _ false (by omega), binary_zero_rep]
  · have hb' : vhi.testBit ℓ = false := by simpa using hb
    have hbr : WExec cap (.ifs HT (cpZ HT K CT (E 9) (E 2) (E 3) (E 1)) (fxB HT K CT (E 9) (E 4) (E 5) (E 1)))
        (est σ2 lo HT K Clo CT (E 9) L 0 (2 * ℓ + 1) out)
        (est σ2 lo HT K Clo CT (E 9) L 0 (2 * ℓ + 1 + 1)
          (out ++ (frameP (List.replicate 0 true) ++ frameP (List.replicate W false) ++ [false])))
        (40 * 0 + 40 * W + 31) := by
      have hbit : wbit (est σ2 lo HT K Clo CT (E 9) L 0 (2 * ℓ + 1) out) HT = false := by
        rw [est_swap σ2 L h1 h2 h3 c1 c2 c3, rst_bitA _ L h3 c3]
        simp only [WState.setv_st, WState.seth_st, hσ2st]
        rw [rd_frame_bit W vht ℓ (by omega), hbit_eq]; exact hb'
      have h := fxB_spec cap σ2 L h1 h2 h3 c1 c2 c3 hT (E 4) (E 5)
        ⟨hClo 4, hCT 4, hE.ne (by decide), hE.ne (by decide)⟩ ⟨hClo 5, hCT 5, hE.ne (by decide), hE.ne (by decide)⟩
        0 W (2 * ℓ + 1) out (by simp [hσ2, hσ1, e4]) (by simp [hσ2, hσ1, e5]) (by simp [hσ2, hσ1, e1]) (by omega)
        (by omega) (by omega) (by omega)
      refine WExec.cast cap (WExec.ifsF hbit h) ?_ (by omega)
      simp only [List.append_assoc]
    have hl := lvlE_spec cap σ2 L h1 h2 h3 c1 c2 c3 hT hLV _ _ ℓ _ _ _ out _ hlo2 hsh2 (by simp [hσ2, hσ1, hClo0])
      (by simp [hσ2, hσ1, hCT0]) (by simp [hσ2, hσ1, e0]) (by simp [hσ2, hσ1, e1]) (by omega) (by omega) (by omega) hbr
    have x4 := zeroB_spec cap W (A := HT) (B := PW) (F := E 10) (R := E 11) h5 (hE.ne (by decide))
      (kst σ2 K (E 9) L (out ++ (frameP (List.replicate 0 true) ++ frameP (List.replicate W false) ++ [false]))) vht
      (2 ^ (ℓ + 1))
      ⟨by rw [kst_st _ _ _ _ _ _ h3]; exact hσ2st, by rw [kst_sh _ _ _ _ _ _ h3]; exact hsh2⟩
      ⟨by rw [kst_st _ _ _ _ _ _ h6]; simp [hσ2, hσ1, Ne.symm h5, hPW.1], by rw [kst_sh _ _ _ _ _ _ h6]; simp [hσ2, hσ1, hPW.2]⟩
      (by rw [kst_val _ _ _ _ _ _ (hE.ne (by decide))]; simp [hσ2, hσ1, e10])
      (by rw [kst_val _ _ _ _ _ _ (hE.ne (by decide))]; simp [hσ2, hσ1, e11]) (by omega)
    rw [kst_sets _ _ _ _ _ _ _ h3] at x4
    have eback : σ2.sets HT (frame (binary W 0)) = σ0 := by
      apply WState.eq
      · rfl
      · funext j; simp only [hσ2, hσ1, WState.sets_st, Function.update_apply]
        split_ifs with h
        · subst h; exact hHT.1.symm
        · rfl
      · rfl
      · rfl
    rw [eback] at x4
    have hall := WExec.seq x1 (WExec.seq x2 (WExec.seq hl x4))
    unfold EK3
    refine WExec.cast cap hall ?_ (by omega)
    rw [if_neg hb]
    simp [frame_eq_frameP, binary_zero_rep]

end K3

end NearCubicWires.WireExponent3_5.SelectionMachine.Point
