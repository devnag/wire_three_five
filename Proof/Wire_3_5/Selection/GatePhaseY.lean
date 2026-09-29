import Proof.Wire_3_5.Selection.GateJoin

/-! # C1.4: the one-dimensional joins of a gate (P3:1345-1358)

Paper: "Sum its exact count" (P3:1358). The two `Y`-joins: `Yh = J<(Y; hi)` and `Yl = J<(Y; lo)`, `Y` both keys of
every right point (C1.1's R5). The phase writes the scratch stream `KY'` once (to the stream's working length), the
key stream `KY` of `Yh`, joins it into `ACC`, rewrites `KY` for `Yl`, joins it into `JT`, and leaves
`ACC = Yh − Yl`, `JT = 0`. Every count is below `2|L||R| = 2^(n+k+1) < 2^W`. Main declarations: `phY`,
**`phY_spec`**. Paper quantity: the one-dimensional part of a gate's row count. -/

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

/-- The `Y`-joins' key lists. -/
def lYh (P : StarParams) (g : NormalizedThresholdGate P.n) (V N : ℕ) : List ℕ :=
  (innerY (tabR V (ptsR P g N))).map tagA ++ ((tabL V g.threshold (ptsL P g N)).map Prod.snd).map tagB
def lYl (P : StarParams) (g : NormalizedThresholdGate P.n) (V N : ℕ) : List ℕ :=
  (innerY (tabR V (ptsR P g N))).map tagA ++ ((tabL V g.threshold (ptsL P g N)).map Prod.fst).map tagB

/-- The `Y`-joins' counts. -/
def Yh (P : StarParams) (g : NormalizedThresholdGate P.n) (V N : ℕ) : ℕ :=
  joinLt (innerY (tabR V (ptsR P g N))) ((tabL V g.threshold (ptsL P g N)).map Prod.snd)
def Yl (P : StarParams) (g : NormalizedThresholdGate P.n) (V N : ℕ) : ℕ :=
  joinLt (innerY (tabR V (ptsR P g N))) ((tabL V g.threshold (ptsL P g N)).map Prod.fst)

/-- **The one-dimensional phase.** -/
def phY (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) : WM ns nr :=
  .seq (kw G R (emYR G R 19) (emYLh G R 19) 19) (.seq (kw G R (emYR G R 18) (emYLh G R 18) 18)
    (.seq (JW G R 18 19 24) (.seq (kw G R (emYR G R 18) (emYLl G R 18) 18) (.seq (JW G R 18 19 23)
      (.seq (satSub (G 24) (G 23) (R 6) (R 7)) (zeroB (G 23) (G 24) (R 6) (R 7)))))))

theorem innerY_length (T : List (ℕ × ℕ)) : (innerY T).length = 2 * T.length := by
  induction T with
  | nil => rfl
  | cons d T ih => simp [innerY] at ih ⊢; omega

section Sizes
variable (P : StarParams) (g : NormalizedThresholdGate P.n) (V N : ℕ)

theorem pairs_pow : 2 ^ (P.s * hh P) * 2 ^ rw P * (2 ^ (P.s * hh P) * 2 ^ lw P) = 2 ^ (P.n + P.k) := by
  obtain ⟨h1, -, -, -, -, h6, h7, h8⟩ := size_facts P
  have e1 : P.s * hh P + P.s * hh P = P.k := by unfold StarParams.k; rw [← Nat.mul_add, ← two_mul, h8, Nat.mul_comm]
  have e2 : lw P + rw P = P.n := by
    have := fL_fR P; have := rb_le P; have := hb2 P; rw [← h6, ← h7]; omega
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1; omega

theorem lY_length : (lYh P g V N).length = 2 * (2 ^ (P.s * hh P) * 2 ^ rw P) + 2 ^ (P.s * hh P) * 2 ^ lw P ∧
    (lYl P g V N).length = 2 * (2 ^ (P.s * hh P) * 2 ^ rw P) + 2 ^ (P.s * hh P) * 2 ^ lw P := by
  unfold lYh lYl
  simp [innerY_length, tabR, tabL, ptsR_length, ptsL_length]

end Sizes

theorem jst_get (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (W : ℕ)
    (σ0 : WState ns nr) (ky ky' kl kl' : List Bool) (jt acc ew ℓ : ℕ) :
    (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).st (G 18) = ky ∧ (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).st (G 19) = ky' ∧
    (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).st (G 20) = kl ∧ (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).st (G 21) = kl' ∧
    (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).st (G 23) = frame (binary W jt) ∧
    (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).st (G 24) = frame (binary W acc) ∧
    (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).st (G 25) = frame (binary W ew) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [jst, Function.update_apply, hG.eq_iff]

/-- The phase's cost. -/
def phYCost (P : StarParams) (W : ℕ) (m : ℕ) : ℕ :=
  kwCost P W (2 * (60 * W + 30) + 1) (60 * W + 30) + 1 + (kwCost P W (2 * (60 * W + 30) + 1) (60 * W + 30) + 1 +
    (joinCost W m + 1 + (kwCost P W (2 * (60 * W + 30) + 1) (60 * W + 30) + 1 + (joinCost W m + 1 +
      (130 * W + 30 + 1 + (41 * W + 3))))))

section Phase
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (P : StarParams) (N W V : ℕ) (g : NormalizedThresholdGate P.n) (cap : ℕ) (σ0 : WState ns nr)
  (hw : WReady G R P N W V g σ0) (hW : 2 * V + 3 ≤ W) (hKB : KeyBound g V) (hcapB : capKW P W ≤ cap)
  (hnk : P.n + P.k + 4 ≤ W)
include hG hR hw hW hKB hcapB hnk

theorem lY_lt : (∀ x ∈ lYh P g V N, x < 2 ^ W) ∧ (∀ x ∈ lYl P g V N, x < 2 ^ W) := by
  have hV : 2 ^ (V + 2) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hVV : 2 ^ (V + 2) = 2 * 2 ^ (V + 1) := by rw [pow_succ]; ring
  have hR' := tabR_lt P g V N hKB
  have hL' := tabL_lt P g V N hKB
  have hin : ∀ a ∈ innerY (tabR V (ptsR P g N)), a < 2 ^ (V + 1) := by
    intro a ha
    unfold innerY at ha
    obtain ⟨d, hd, ha⟩ := List.mem_flatMap.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact (hR' d hd).1
    · exact (hR' d hd).2
  constructor
  · intro x hx
    unfold lYh at hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h; have := hin a ha; unfold tagA; omega
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
      have := (hL' d hd).2; unfold tagB; omega
  · intro x hx
    unfold lYl at hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h; have := hin a ha; unfold tagA; omega
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
      have := (hL' d hd).1; unfold tagB; omega

theorem Y_bounds : (innerY (tabR V (ptsR P g N))).length < 2 ^ W ∧ Yh P g V N < 2 ^ W ∧ Yl P g V N < 2 ^ W ∧
    (innerY (tabR V (ptsR P g N))).length * (tabL V g.threshold (ptsL P g N)).length = 2 ^ (P.n + P.k + 1) := by
  have hp := pairs_pow P
  have hW' : 2 ^ (P.n + P.k + 1) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hprod : (innerY (tabR V (ptsR P g N))).length * (tabL V g.threshold (ptsL P g N)).length =
      2 ^ (P.n + P.k + 1) := by
    simp only [innerY_length, tabR, tabL, List.length_map, ptsR_length, ptsL_length]
    rw [pow_succ, ← hp]; ring
  have hTL : 1 ≤ (tabL V g.threshold (ptsL P g N)).length := by
    simp only [tabL, List.length_map, ptsL_length]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨?_, ?_, ?_, hprod⟩
  · calc (innerY (tabR V (ptsR P g N))).length
        ≤ (innerY (tabR V (ptsR P g N))).length * (tabL V g.threshold (ptsL P g N)).length := Nat.le_mul_of_pos_right _ hTL
      _ < 2 ^ W := by rw [hprod]; exact hW'
  · have := joinLt_le (innerY (tabR V (ptsR P g N))) ((tabL V g.threshold (ptsL P g N)).map Prod.snd)
    rw [List.length_map, hprod] at this; unfold Yh; omega
  · have := joinLt_le (innerY (tabR V (ptsR P g N))) ((tabL V g.threshold (ptsL P g N)).map Prod.fst)
    rw [List.length_map, hprod] at this; unfold Yl; omega

set_option maxHeartbeats 1000000 in
/-- **The one-dimensional phase**: `ACC := Yh − Yl`; the key streams `KY`, `KY'` end at their working length. -/
theorem phY_spec (ky ky' kl kl' : List Bool) (ℓ : ℕ)
    (hky : ky.length ≤ (keyStream W (lYh P g V N)).length) (hky' : ky'.length ≤ (keyStream W (lYh P g V N)).length)
    (hcapJ : (keyStream W (lYh P g V N)).length + 2 ≤ cap) :
    ∃ ky2 ky2' : List Bool, ky2.length = (keyStream W (lYh P g V N)).length ∧
      ky2'.length = (keyStream W (lYh P g V N)).length ∧
      WExec cap (phY G R) (jst G R W σ0 ky ky' kl kl' 0 0 0 ℓ)
        (jst G R W σ0 ky2 ky2' kl kl' 0 (Yh P g V N - Yl P g V N) 0 ℓ)
        (phYCost P W (lYh P g V N).length) := by
  have hW1 : 1 ≤ W := by omega
  have hsh : ∀ (ky ky' kl kl' : List Bool) (jt acc ew ℓ : ℕ) (i : Fin 28),
      (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).sh (G i) = 0 := fun _ _ _ _ _ _ _ _ i => hw.heads i
  have hzr : ∀ (ky ky' kl kl' : List Bool) (jt acc ew ℓ : ℕ) (i : Fin 48), zeroReg i = true →
      (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).val (R i) = 0 := by
    intro _ _ _ _ _ _ _ _ i hi
    rw [jst_val G hG R hR, if_neg (by intro h; subst h; revert hi; decide)]; exact hw.zr i hi
  have hcnt : ∀ (ky ky' kl kl' : List Bool) (jt acc ew ℓ : ℕ),
      (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).st (G 22) = frame (binary W 0) := by
    intro _ _ _ _ _ _ _ _; rw [jst_st G hG R hR _ _ _ _ _ _ _ _ _ _ 22 (by decide)]; exact hw.cnt
  obtain ⟨hlt1, hlt2⟩ := lY_lt G hG R hR P N W V g cap σ0 hw hW hKB hcapB hnk
  obtain ⟨hA, hYh, hYl, -⟩ := Y_bounds G hG R hR P N W V g cap σ0 hw hW hKB hcapB hnk
  obtain ⟨l1, l2⟩ := lY_length P g V N
  have hks : (keyStream W (lYl P g V N)).length = (keyStream W (lYh P g V N)).length := by
    rw [keyStream_length W hW1, keyStream_length W hW1, l1, l2]
  have hks' : (keyStream W (sorted (lYh P g V N))).length = (keyStream W (lYh P g V N)).length := by
    rw [keyStream_length W hW1, keyStream_length W hW1, sorted_length]
  set K1 := keyStream W (lYh P g V N) with hK1
  set K2 := keyStream W (lYl P g V N) with hK2
  have eR := fun (k : Fin 28) (hk : 18 ≤ k.val) (hk' : k.val ≤ 21) =>
    emYR_hyp G hG R hR cap W V ℓ k hk hk' (SRm G) rfl rfl hW1
  have eLh := fun (k : Fin 28) (hk : 18 ≤ k.val) (hk' : k.val ≤ 21) =>
    emYLh_hyp G hG R hR cap W V ℓ k hk hk' (SLm G) rfl rfl hW1
  have eLl := fun (k : Fin 28) (hk : 18 ≤ k.val) (hk' : k.val ≤ 21) =>
    emYLl_hyp G hG R hR cap W V ℓ k hk hk' (SLm G) rfl rfl hW1
  have fr : ∀ a b, (fYR W a b).length ≤ 4 * W + 2 := fun a b => by simp [fYR, frame_eq_frameP]; omega
  have fh : ∀ a b, (fYLh W a b).length ≤ 4 * W + 2 := fun a b => by simp [fYLh, frame_eq_frameP]; omega
  have fl : ∀ a b, (fYLl W a b).length ≤ 4 * W + 2 := fun a b => by simp [fYLl, frame_eq_frameP]; omega
  -- KY' := the key stream of `Yh`
  have s1 := kwKS G hG R hR P N W V g cap σ0 hw ky ky' kl kl' 0 0 0 ℓ 19 ⟨by decide, by decide⟩ hW hKB hcapB
    (emYR G R 19) (emYLh G R 19) (fYR W) (fYLh W) _ _ (eR 19 (by decide) (by decide)) (eLh 19 (by decide) (by decide))
    fr fh (lYh P g V N) (streamYh P g W V N hW1 hKB) (by rw [(jst_get G hG R W σ0 _ _ _ _ _ _ _ _).2.1]; exact hky')
  rw [jst_setKY' G hG R hR] at s1
  -- KY := the key stream of `Yh`
  have s2 := kwKS G hG R hR P N W V g cap σ0 hw ky K1 kl kl' 0 0 0 ℓ 18 ⟨by decide, by decide⟩ hW hKB hcapB
    (emYR G R 18) (emYLh G R 18) (fYR W) (fYLh W) _ _ (eR 18 (by decide) (by decide)) (eLh 18 (by decide) (by decide))
    fr fh (lYh P g V N) (streamYh P g W V N hW1 hKB) (by rw [(jst_get G hG R W σ0 _ _ _ _ _ _ _ _).1]; exact hky)
  rw [jst_setKY G hG R hR] at s2
  -- ACC := Yh
  obtain ⟨junk1, hj1, s3⟩ := JW_spec G hG R hR P N W V g cap σ0 hw hW1 18 19 24 (by decide) (Or.inl rfl) (Or.inl rfl)
    (Or.inr (Or.inl rfl)) (jst G R W σ0 K1 K1 kl kl' 0 0 0 ℓ) (hsh _ _ _ _ _ _ _ _) (hzr _ _ _ _ _ _ _ _) (hcnt _ _ _ _ _ _ _ _)
    (innerY (tabR V (ptsR P g N))) ((tabL V g.threshold (ptsL P g N)).map Prod.snd) (lYh P g V N) 0 rfl hlt1
    (jst_get G hG R W σ0 _ _ _ _ _ _ _ _).1 (by rw [(jst_get G hG R W σ0 _ _ _ _ _ _ _ _).2.1])
    (jst_get G hG R W σ0 _ _ _ _ _ _ _ _).2.2.2.2.2.1 hA (by rw [Nat.zero_add]; exact hYh) (by omega)
  rw [jst_setKY G hG R hR, jst_setKY' G hG R hR, jst_setACC G hG R hR, Nat.zero_add] at s3
  -- KY := the key stream of `Yl`
  have s4 := kwKS G hG R hR P N W V g cap σ0 hw (keyStream W (sorted (lYh P g V N))) junk1 kl kl' 0 (Yh P g V N) 0 ℓ 18
    ⟨by decide, by decide⟩ hW hKB hcapB (emYR G R 18) (emYLl G R 18) (fYR W) (fYLl W) _ _ (eR 18 (by decide) (by decide))
    (eLl 18 (by decide) (by decide)) fr fl (lYl P g V N) (streamYl P g W V N hW1 hKB)
    (by rw [(jst_get G hG R W σ0 _ _ _ _ _ _ _ _).1, hks', hks])
  rw [jst_setKY G hG R hR] at s4
  -- JT := Yl
  obtain ⟨junk2, hj2, s5⟩ := JW_spec G hG R hR P N W V g cap σ0 hw hW1 18 19 23 (by decide) (Or.inl rfl) (Or.inl rfl)
    (Or.inl rfl) (jst G R W σ0 K2 junk1 kl kl' 0 (Yh P g V N) 0 ℓ) (hsh _ _ _ _ _ _ _ _) (hzr _ _ _ _ _ _ _ _)
    (hcnt _ _ _ _ _ _ _ _) (innerY (tabR V (ptsR P g N))) ((tabL V g.threshold (ptsL P g N)).map Prod.fst)
    (lYl P g V N) 0 rfl hlt2 (jst_get G hG R W σ0 _ _ _ _ _ _ _ _).1
    (by rw [(jst_get G hG R W σ0 _ _ _ _ _ _ _ _).2.1, hj1, hks]) (jst_get G hG R W σ0 _ _ _ _ _ _ _ _).2.2.2.2.1
    hA (by rw [Nat.zero_add]; exact hYl) (by rw [hks]; omega)
  rw [jst_setKY G hG R hR, jst_setKY' G hG R hR, jst_setJT G hG R hR, Nat.zero_add] at s5
  -- ACC := Yh − Yl; JT := 0
  have num := jst_num G hG R hR W σ0 (keyStream W (sorted (lYl P g V N))) junk2 kl kl' (Yl P g V N) (Yh P g V N) 0 ℓ
    hw.heads
  have s6 := satSub_spec cap W (A := G 24) (B := G 23) (F := R 6) (R := R 7) (hG.ne (by decide)) (hR.ne (by decide)) _
    (Yh P g V N) (Yl P g V N) num.2.1 num.1 (hzr _ _ _ _ _ _ _ _ 6 (by decide)) (hzr _ _ _ _ _ _ _ _ 7 (by decide))
    hYh hYl (by have := (capKW_facts P W cap hcapB).2.1; omega)
  rw [jst_setACC G hG R hR] at s6
  have num2 := jst_num G hG R hR W σ0 (keyStream W (sorted (lYl P g V N))) junk2 kl kl' (Yl P g V N)
    (Yh P g V N - Yl P g V N) 0 ℓ hw.heads
  have s7 := zeroB_spec cap W (A := G 23) (B := G 24) (F := R 6) (R := R 7) (hG.ne (by decide)) (hR.ne (by decide)) _
    (Yl P g V N) (Yh P g V N - Yl P g V N) num2.1 num2.2.1 (hzr _ _ _ _ _ _ _ _ 6 (by decide))
    (hzr _ _ _ _ _ _ _ _ 7 (by decide)) (by have := (capKW_facts P W cap hcapB).2.1; omega)
  rw [jst_setJT G hG R hR] at s7
  have hll : (lYl P g V N).length = (lYh P g V N).length := by rw [l1, l2]
  refine ⟨keyStream W (sorted (lYl P g V N)), junk2,
    by rw [keyStream_length W hW1, sorted_length, ← keyStream_length W hW1]; exact hks, by rw [hj2, hks], ?_⟩
  unfold phY phYCost
  exact WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 s7))))))
    rfl (by rw [hll])

end Phase

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
