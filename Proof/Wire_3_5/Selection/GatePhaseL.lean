import Proof.Wire_3_5.Selection.GatePhaseY
import Proof.Wire_3_5.UnionMachine.RoundDiv

/-! # C1.4: the level joins of a gate (P3:1345-1358)

Paper: "dominance counting needs only `O(U log^{O(1)} U)` comparisons" (P3:1349-1350). C1.1's R6 splits the 2-d count
by the most significant differing bit `ℓ` into two 1-d `<`-joins per level: `K3_ℓ = J<(K2_ℓ; K3_ℓ)` and
`K1_ℓ = J<(K2_ℓ; K1_ℓ)`. One level of the machine: the key stream `KL` of `K3_ℓ`, joined into `JT`; of `K1_ℓ`, joined
into `EW`; `JT := JT − EW`; `ACC := ACC − JT − JT`; the words back to `0`; `ℓ := ℓ + 1`, `PW := 2·PW`. Main
declarations: `lK1`, `lK3`, `bodyL`, **`lvlStep_spec`**. Paper quantity: the two-dimensional part of a gate's row count,
one level. -/

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

/-- The level joins' key lists. -/
def lK1 (P : StarParams) (g : NormalizedThresholdGate P.n) (V N ℓ : ℕ) : List ℕ :=
  (lvlK2 (V + 1) ℓ (tabR V (ptsR P g N))).map tagA ++ (lvlK1 (V + 1) ℓ (tabL V g.threshold (ptsL P g N))).map tagB
def lK3 (P : StarParams) (g : NormalizedThresholdGate P.n) (V N ℓ : ℕ) : List ℕ :=
  (lvlK2 (V + 1) ℓ (tabR V (ptsR P g N))).map tagA ++ (lvlK3 (V + 1) ℓ (tabL V g.threshold (ptsL P g N))).map tagB

/-- The level joins' counts. -/
def cK1 (P : StarParams) (g : NormalizedThresholdGate P.n) (V N ℓ : ℕ) : ℕ :=
  joinLt (lvlK2 (V + 1) ℓ (tabR V (ptsR P g N))) (lvlK1 (V + 1) ℓ (tabL V g.threshold (ptsL P g N)))
def cK3 (P : StarParams) (g : NormalizedThresholdGate P.n) (V N ℓ : ℕ) : ℕ :=
  joinLt (lvlK2 (V + 1) ℓ (tabR V (ptsR P g N))) (lvlK3 (V + 1) ℓ (tabL V g.threshold (ptsL P g N)))

/-- **One level.** -/
def bodyL (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) : WM ns nr :=
  .seq (kw G R (emK2 G R 20) (emK3 G R 20) 20) (.seq (JW G R 20 21 23) (.seq (kw G R (emK2 G R 20) (emK1 G R 20) 20)
    (.seq (JW G R 20 21 25) (.seq (satSub (G 23) (G 25) (R 6) (R 7)) (.seq (satSub (G 24) (G 23) (R 6) (R 7))
    (.seq (satSub (G 24) (G 23) (R 6) (R 7)) (.seq (zeroB (G 23) (G 24) (R 6) (R 7))
    (.seq (zeroB (G 25) (G 24) (R 6) (R 7)) (.seq (.inc (R 19)) (shlB (G 17) (G 24) (R 6) (R 7)))))))))))

section Sizes
variable (P : StarParams) (g : NormalizedThresholdGate P.n) (V N ℓ : ℕ)

theorem lK_length : (lK1 P g V N ℓ).length = 2 ^ (P.s * hh P) * 2 ^ rw P + 2 ^ (P.s * hh P) * 2 ^ lw P ∧
    (lK3 P g V N ℓ).length = 2 ^ (P.s * hh P) * 2 ^ rw P + 2 ^ (P.s * hh P) * 2 ^ lw P := by
  unfold lK1 lK3
  simp [lvlK1, lvlK2, lvlK3, tabR, tabL, ptsR_length, ptsL_length]

end Sizes

theorem div_pow_lt (M V ℓ : ℕ) (hM : M < 2 ^ (V + 1)) (hℓ : ℓ ≤ V) : M / 2 ^ (ℓ + 1) + 1 ≤ 2 ^ V := by
  have h1 : M / 2 ^ (ℓ + 1) < 2 ^ (V - ℓ) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
    have : V - ℓ + (ℓ + 1) = V + 1 := by omega
    rw [this]; exact hM
  have h2 : 2 ^ (V - ℓ) ≤ 2 ^ V := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **The level keys fit the word**. -/
theorem lvl_keys_lt (V ℓ W : ℕ) (hℓ : ℓ ≤ V) (hW : 2 * V + 3 ≤ W) (D I : List (ℕ × ℕ))
    (hD : ∀ d ∈ D, d.1 < 2 ^ (V + 1) ∧ d.2 < 2 ^ (V + 1)) (hI : ∀ d ∈ I, d.1 < 2 ^ (V + 1) ∧ d.2 < 2 ^ (V + 1)) :
    (∀ x ∈ (lvlK2 (V + 1) ℓ D).map tagA ++ (lvlK1 (V + 1) ℓ I).map tagB, x < 2 ^ W) ∧
    (∀ x ∈ (lvlK2 (V + 1) ℓ D).map tagA ++ (lvlK3 (V + 1) ℓ I).map tagB, x < 2 ^ W) := by
  have hq : 2 ^ (2 * (V + 1)) = 2 ^ (V + 1) * 2 ^ (V + 1) := by rw [← pow_add]; ring_nf
  have hW' : 2 * 2 ^ (2 * (V + 1)) ≤ 2 ^ W := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hVV : 2 ^ (V + 1) = 2 * 2 ^ V := by rw [pow_succ]; ring
  have bnd : ∀ M m : ℕ, M < 2 ^ (V + 1) → m < 2 ^ (V + 1) → M / 2 ^ (ℓ + 1) * 2 ^ (V + 1) + m < 2 ^ (2 * (V + 1)) := by
    intro M m hM hm
    have h1 := div_pow_lt M V ℓ hM hℓ
    have h2 : M / 2 ^ (ℓ + 1) * 2 ^ (V + 1) + 2 ^ (V + 1) ≤ 2 ^ V * 2 ^ (V + 1) := by
      rw [← add_one_mul]; exact Nat.mul_le_mul_right _ h1
    rw [hq, hVV] at *; nlinarith
  have bnd3 : ∀ M : ℕ, M < 2 ^ (V + 1) → (M / 2 ^ (ℓ + 1) + 1) * 2 ^ (V + 1) < 2 ^ (2 * (V + 1)) := by
    intro M hM
    have h1 := div_pow_lt M V ℓ hM hℓ
    have h2 : (M / 2 ^ (ℓ + 1) + 1) * 2 ^ (V + 1) ≤ 2 ^ V * 2 ^ (V + 1) := Nat.mul_le_mul_right _ h1
    rw [hq, hVV] at *; nlinarith [Nat.two_pow_pos V]
  have hX : 0 < 2 ^ (2 * (V + 1)) := Nat.two_pow_pos _
  have tA : ∀ x, x < 2 ^ (2 * (V + 1)) → tagA x < 2 ^ W := fun x hx => by
    unfold tagA; exact lt_of_lt_of_le (by omega) hW'
  have tB : ∀ x, x < 2 ^ (2 * (V + 1)) → tagB x < 2 ^ W := fun x hx => by
    unfold tagB; exact lt_of_lt_of_le (by omega) hW'
  have hA : ∀ x ∈ (lvlK2 (V + 1) ℓ D).map tagA, x < 2 ^ W := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    unfold lvlK2 at ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    have := hD d hd
    apply tA
    split_ifs
    · exact Nat.sub_lt hX Nat.one_pos
    · exact bnd d.2 d.1 this.2 this.1
  constructor
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hA x h
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      unfold lvlK1 at ha
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
      have := hI d hd
      apply tB
      split_ifs
      · exact bnd d.2 d.1 this.2 this.1
      · exact hX
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hA x h
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      unfold lvlK3 at ha
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
      have := hI d hd
      apply tB
      split_ifs
      · exact bnd3 d.2 this.2
      · exact hX

theorem accFold_le (yh yl : ℕ) (e : ℕ → ℕ) : ∀ m, accFold yh yl e m ≤ yh - yl
  | 0 => le_rfl
  | m + 1 => by rw [accFold_succ]; have := accFold_le yh yl e m; omega

theorem WReady_setv46 (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (hR : Function.Injective R) (P : StarParams)
    (N W V : ℕ) (g : NormalizedThresholdGate P.n) (σ0 : WState ns nr) (hw : WReady G R P N W V g σ0) (c : ℕ) :
    WReady G R P N W V g (σ0.setv (R 46) c) := by
  have hv : ∀ i : Fin 48, i ≠ 46 → (σ0.setv (R 46) c).val (R i) = σ0.val (R i) := by
    intro i hi; simp [Function.update_apply, hR.eq_iff, hi]
  exact ⟨hw.x0, hw.u0, hw.ci0, hw.sy0, hw.ac0, hw.ac0', hw.wv0, hw.xp, hw.up, hw.ns, hw.wtl, hw.wtr, hw.tk, hw.ofs,
    hw.ht, hw.cnt, hw.heads, by rw [hv 0 (by decide)]; exact hw.rh, by rw [hv 1 (by decide)]; exact hw.rb,
    by rw [hv 2 (by decide)]; exact hw.rs, by rw [hv 3 (by decide)]; exact hw.rfL, by rw [hv 4 (by decide)]; exact hw.rfR,
    by rw [hv 5 (by decide)]; exact hw.rv, by rw [hv 15 (by decide)]; exact hw.ro, by rw [hv 21 (by decide)]; exact hw.rq,
    by rw [hv 23 (by decide)]; exact hw.rW, by rw [hv 24 (by decide)]; exact hw.rW1,
    by rw [hv 25 (by decide)]; exact hw.rs1, by rw [hv 26 (by decide)]; exact hw.rs0,
    by rw [hv 31 (by decide)]; exact hw.pxl, by rw [hv 32 (by decide)]; exact hw.pu,
    by rw [hv 35 (by decide)]; exact hw.pxr,
    fun i hi => by rw [hv i (by intro h; subst h; revert hi; decide)]; exact hw.zr i hi⟩

/-- The level's cost. -/
def lvlCost (P : StarParams) (W m : ℕ) : ℕ :=
  kwCost P W (200 * W + 200) (400 * W + 300) + 1 + (joinCost W m + 1 + (kwCost P W (200 * W + 200) (200 * W + 200) + 1 +
    (joinCost W m + 1 + (130 * W + 30 + 1 + (130 * W + 30 + 1 + (130 * W + 30 + 1 + (41 * W + 3 + 1 +
      (41 * W + 3 + 1 + (3 + 1 + (41 * W + 8))))))))))

section Step
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (P : StarParams) (N W V : ℕ) (g : NormalizedThresholdGate P.n) (cap : ℕ) (σ0 : WState ns nr)
  (hw : WReady G R P N W V g σ0) (hW : 2 * V + 3 ≤ W) (hKB : KeyBound g V) (hcapB : capKW P W ≤ cap)
  (hnk : P.n + P.k + 4 ≤ W)
include hG hR hw hW hKB hcapB hnk

theorem lvl_counts (ℓ : ℕ) : (lvlK2 (V + 1) ℓ (tabR V (ptsR P g N))).length < 2 ^ W ∧
    cK1 P g V N ℓ < 2 ^ W ∧ cK3 P g V N ℓ < 2 ^ W ∧ cK1 P g V N ℓ ≤ cK3 P g V N ℓ := by
  have hp := pairs_pow P
  have hW' : 2 ^ (P.n + P.k) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hprod : (lvlK2 (V + 1) ℓ (tabR V (ptsR P g N))).length * (lvlK1 (V + 1) ℓ (tabL V g.threshold (ptsL P g N))).length
      = 2 ^ (P.n + P.k) := by
    simp only [lvlK2, lvlK1, tabR, tabL, List.length_map, ptsR_length, ptsL_length]; rw [← hp]
  have hprod3 : (lvlK2 (V + 1) ℓ (tabR V (ptsR P g N))).length * (lvlK3 (V + 1) ℓ (tabL V g.threshold (ptsL P g N))).length
      = 2 ^ (P.n + P.k) := by
    simp only [lvlK2, lvlK3, tabR, tabL, List.length_map, ptsR_length, ptsL_length]; rw [← hp]
  have hTL : 1 ≤ (lvlK1 (V + 1) ℓ (tabL V g.threshold (ptsL P g N))).length := by
    simp only [lvlK1, tabL, List.length_map, ptsL_length]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (lvlK2 (V + 1) ℓ (tabR V (ptsR P g N))).length
        ≤ (lvlK2 (V + 1) ℓ (tabR V (ptsR P g N))).length * (lvlK1 (V + 1) ℓ (tabL V g.threshold (ptsL P g N))).length :=
          Nat.le_mul_of_pos_right _ hTL
      _ < 2 ^ W := by rw [hprod]; exact hW'
  · have := joinLt_le (lvlK2 (V + 1) ℓ (tabR V (ptsR P g N))) (lvlK1 (V + 1) ℓ (tabL V g.threshold (ptsL P g N)))
    rw [hprod] at this; unfold cK1; omega
  · have := joinLt_le (lvlK2 (V + 1) ℓ (tabR V (ptsR P g N))) (lvlK3 (V + 1) ℓ (tabL V g.threshold (ptsL P g N)))
    rw [hprod3] at this; unfold cK3; omega
  · exact K1_le_K3 (V + 1) ℓ _ _ (fun J hJ => (tabL_lt P g V N hKB J hJ).1)

set_option maxHeartbeats 2000000 in
/-- **One level**: `ACC := ACC − e_ℓ − e_ℓ`, `e_ℓ = K3_ℓ − K1_ℓ`; `ℓ := ℓ + 1`; the level key streams stay at their
working length. -/
theorem lvlStep_spec (ky ky' kl kl' : List Bool) (acc ℓ : ℕ) (hℓ : ℓ ≤ V) (hacc : acc < 2 ^ W)
    (hkl : kl.length ≤ (keyStream W (lK1 P g V N 0)).length) (hkl' : kl'.length = (keyStream W (lK1 P g V N 0)).length)
    (hcapL : (keyStream W (lK1 P g V N 0)).length + 2 ≤ cap) (hℓcap : ℓ + 1 ≤ cap) :
    ∃ kl2 kl2' : List Bool, kl2.length = (keyStream W (lK1 P g V N 0)).length ∧
      kl2'.length = (keyStream W (lK1 P g V N 0)).length ∧
      WExec cap (bodyL G R) (jst G R W σ0 ky ky' kl kl' 0 acc 0 ℓ)
        (jst G R W σ0 ky ky' kl2 kl2' 0 (acc - (cK3 P g V N ℓ - cK1 P g V N ℓ) - (cK3 P g V N ℓ - cK1 P g V N ℓ)) 0
          (ℓ + 1)) (lvlCost P W (lK1 P g V N 0).length) := by
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
  obtain ⟨hA, h1, h3, h13⟩ := lvl_counts G hG R hR P N W V g cap σ0 hw hW hKB hcapB hnk ℓ
  obtain ⟨b1, b3⟩ := lvl_keys_lt V ℓ W hℓ hW _ _ (tabR_lt P g V N hKB) (tabL_lt P g V N hKB)
  have hL0 := lK_length P g V N 0
  have hLl := lK_length P g V N ℓ
  have ks1 : (keyStream W (lK1 P g V N ℓ)).length = (keyStream W (lK1 P g V N 0)).length := by
    rw [keyStream_length W hW1, keyStream_length W hW1, hLl.1, hL0.1]
  have ks3 : (keyStream W (lK3 P g V N ℓ)).length = (keyStream W (lK1 P g V N 0)).length := by
    rw [keyStream_length W hW1, keyStream_length W hW1, hLl.2, hL0.1]
  have kss : ∀ l : List ℕ, (keyStream W (sorted l)).length = (keyStream W l).length := fun l => by
    rw [keyStream_length W hW1, keyStream_length W hW1, sorted_length]
  have fk1 : ∀ a b, (fK1 W V ℓ a b).length ≤ 4 * W + 2 := fun a b => by simp [fK1, frame_eq_frameP]; omega
  have fk2 : ∀ a b, (fK2 W V ℓ a b).length ≤ 4 * W + 2 := fun a b => by simp [fK2, frame_eq_frameP]; omega
  have fk3 : ∀ a b, (fK3 W V ℓ a b).length ≤ 4 * W + 2 := fun a b => by simp [fK3, frame_eq_frameP]; omega
  have hc2 := (capKW_facts P W cap hcapB).2.1
  -- KL := the key stream of K3_ℓ
  have t1 := kwKS G hG R hR P N W V g cap σ0 hw ky ky' kl kl' 0 acc 0 ℓ 20 ⟨by decide, by decide⟩ hW hKB hcapB
    (emK2 G R 20) (emK3 G R 20) (fK2 W V ℓ) (fK3 W V ℓ) _ _
    (emK2_hyp G hG R hR cap W V ℓ 20 (by decide) (by decide) (SRm G) rfl rfl hW hℓ)
    (emK3_hyp G hG R hR cap W V ℓ 20 (by decide) (by decide) (SLm G) rfl rfl hW hℓ) fk2 fk3 (lK3 P g V N ℓ)
    (streamK3 P g W V N ℓ hW1 hKB) (by rw [(jst_get G hG R W σ0 _ _ _ _ _ _ _ _).2.2.1, ks3]; exact hkl)
  rw [jst_setKL G hG R hR] at t1
  -- JT := K3_ℓ
  obtain ⟨j1, hj1, t2⟩ := JW_spec G hG R hR P N W V g cap σ0 hw hW1 20 21 23 (by decide) (Or.inr rfl) (Or.inr rfl)
    (Or.inl rfl) (jst G R W σ0 ky ky' (keyStream W (lK3 P g V N ℓ)) kl' 0 acc 0 ℓ) (hsh _ _ _ _ _ _ _ _)
    (hzr _ _ _ _ _ _ _ _) (hcnt _ _ _ _ _ _ _ _) _ _ (lK3 P g V N ℓ) 0 rfl b3
    (jst_get G hG R W σ0 _ _ _ _ _ _ _ _).2.2.1 (by rw [(jst_get G hG R W σ0 _ _ _ _ _ _ _ _).2.2.2.1, hkl', ks3])
    (jst_get G hG R W σ0 _ _ _ _ _ _ _ _).2.2.2.2.1 hA (by rw [Nat.zero_add]; exact h3) (by rw [ks3]; omega)
  rw [jst_setKL G hG R hR, jst_setKL' G hG R hR, jst_setJT G hG R hR, Nat.zero_add] at t2
  -- KL := the key stream of K1_ℓ
  have t3 := kwKS G hG R hR P N W V g cap σ0 hw ky ky' (keyStream W (sorted (lK3 P g V N ℓ))) j1 (cK3 P g V N ℓ) acc 0 ℓ
    20 ⟨by decide, by decide⟩ hW hKB hcapB (emK2 G R 20) (emK1 G R 20) (fK2 W V ℓ) (fK1 W V ℓ) _ _
    (emK2_hyp G hG R hR cap W V ℓ 20 (by decide) (by decide) (SRm G) rfl rfl hW hℓ)
    (emK1_hyp G hG R hR cap W V ℓ 20 (by decide) (by decide) (SLm G) rfl rfl hW hℓ) fk2 fk1 (lK1 P g V N ℓ)
    (streamK1 P g W V N ℓ hW1 hKB) (by rw [(jst_get G hG R W σ0 _ _ _ _ _ _ _ _).2.2.1, kss, ks3, ks1])
  rw [jst_setKL G hG R hR] at t3
  -- EW := K1_ℓ
  obtain ⟨j2, hj2, t4⟩ := JW_spec G hG R hR P N W V g cap σ0 hw hW1 20 21 25 (by decide) (Or.inr rfl) (Or.inr rfl)
    (Or.inr (Or.inr rfl)) (jst G R W σ0 ky ky' (keyStream W (lK1 P g V N ℓ)) j1 (cK3 P g V N ℓ) acc 0 ℓ)
    (hsh _ _ _ _ _ _ _ _) (hzr _ _ _ _ _ _ _ _) (hcnt _ _ _ _ _ _ _ _) _ _ (lK1 P g V N ℓ) 0 rfl b1
    (jst_get G hG R W σ0 _ _ _ _ _ _ _ _).2.2.1 (by rw [(jst_get G hG R W σ0 _ _ _ _ _ _ _ _).2.2.2.1, hj1, ks3, ks1])
    (jst_get G hG R W σ0 _ _ _ _ _ _ _ _).2.2.2.2.2.2 hA (by rw [Nat.zero_add]; exact h1) (by rw [ks1]; omega)
  rw [jst_setKL G hG R hR, jst_setKL' G hG R hR, jst_setEW G hG R hR, Nat.zero_add] at t4
  -- JT := e; ACC := ACC − e − e; JT, EW := 0
  set e := cK3 P g V N ℓ - cK1 P g V N ℓ with he
  set kL := keyStream W (sorted (lK1 P g V N ℓ)) with hkL
  have n1 := jst_num G hG R hR W σ0 ky ky' kL j2 (cK3 P g V N ℓ) acc (cK1 P g V N ℓ) ℓ hw.heads
  have t5 := satSub_spec cap W (A := G 23) (B := G 25) (F := R 6) (R := R 7) (hG.ne (by decide)) (hR.ne (by decide)) _
    _ _ n1.1 n1.2.2.1 (hzr _ _ _ _ _ _ _ _ 6 (by decide)) (hzr _ _ _ _ _ _ _ _ 7 (by decide)) h3 h1 (by omega)
  rw [jst_setJT G hG R hR] at t5
  have n2 := jst_num G hG R hR W σ0 ky ky' kL j2 e acc (cK1 P g V N ℓ) ℓ hw.heads
  have t6 := satSub_spec cap W (A := G 24) (B := G 23) (F := R 6) (R := R 7) (hG.ne (by decide)) (hR.ne (by decide)) _
    _ _ n2.2.1 n2.1 (hzr _ _ _ _ _ _ _ _ 6 (by decide)) (hzr _ _ _ _ _ _ _ _ 7 (by decide)) hacc (by omega) (by omega)
  rw [jst_setACC G hG R hR] at t6
  have n3 := jst_num G hG R hR W σ0 ky ky' kL j2 e (acc - e) (cK1 P g V N ℓ) ℓ hw.heads
  have t7 := satSub_spec cap W (A := G 24) (B := G 23) (F := R 6) (R := R 7) (hG.ne (by decide)) (hR.ne (by decide)) _
    _ _ n3.2.1 n3.1 (hzr _ _ _ _ _ _ _ _ 6 (by decide)) (hzr _ _ _ _ _ _ _ _ 7 (by decide)) (by omega) (by omega)
    (by omega)
  rw [jst_setACC G hG R hR] at t7
  have n4 := jst_num G hG R hR W σ0 ky ky' kL j2 e (acc - e - e) (cK1 P g V N ℓ) ℓ hw.heads
  have t8 := zeroB_spec cap W (A := G 23) (B := G 24) (F := R 6) (R := R 7) (hG.ne (by decide)) (hR.ne (by decide)) _
    _ _ n4.1 n4.2.1 (hzr _ _ _ _ _ _ _ _ 6 (by decide)) (hzr _ _ _ _ _ _ _ _ 7 (by decide)) (by omega)
  rw [jst_setJT G hG R hR] at t8
  have n5 := jst_num G hG R hR W σ0 ky ky' kL j2 0 (acc - e - e) (cK1 P g V N ℓ) ℓ hw.heads
  have t9 := zeroB_spec cap W (A := G 25) (B := G 24) (F := R 6) (R := R 7) (hG.ne (by decide)) (hR.ne (by decide)) _
    _ _ n5.2.2.1 n5.2.1 (hzr _ _ _ _ _ _ _ _ 6 (by decide)) (hzr _ _ _ _ _ _ _ _ 7 (by decide)) (by omega)
  rw [jst_setEW G hG R hR] at t9
  -- ℓ := ℓ + 1; PW := 2·PW
  have hv19 : (jst G R W σ0 ky ky' kL j2 0 (acc - e - e) 0 ℓ).val (R 19) = ℓ := by rw [jst_val G hG R hR]; simp
  have t10 := WExec.inc (cap := cap) (R 19) (jst G R W σ0 ky ky' kL j2 0 (acc - e - e) 0 ℓ) (by rw [hv19]; omega)
  rw [hv19] at t10
  have n6 := jst_num G hG R hR W σ0 ky ky' kL j2 0 (acc - e - e) 0 ℓ hw.heads
  have t11 := shlB_spec cap W (A := G 17) (B := G 24) (F := R 6) (R := R 7) (hG.ne (by decide)) (hR.ne (by decide))
    ((jst G R W σ0 ky ky' kL j2 0 (acc - e - e) 0 ℓ).setv (R 19) (ℓ + 1)) (2 ^ (ℓ + 1)) (acc - e - e)
    n6.2.2.2 n6.2.1 (by rw [WState.setv_val, Function.update_of_ne (hR.ne (by decide))]; exact hzr _ _ _ _ _ _ _ _ 6 (by decide))
    (by rw [WState.setv_val, Function.update_of_ne (hR.ne (by decide))]; exact hzr _ _ _ _ _ _ _ _ 7 (by decide))
    (by omega)
  rw [jst_next G hG R hR] at t11
  refine ⟨kL, j2, by rw [hkL, kss, ks1], by rw [hj2, ks1], ?_⟩
  unfold bodyL lvlCost
  have hlen : (lK3 P g V N ℓ).length = (lK1 P g V N 0).length := by rw [hLl.2, hL0.1]
  have hlen1 : (lK1 P g V N ℓ).length = (lK1 P g V N 0).length := by rw [hLl.1, hL0.1]
  refine WExec.cast cap (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 (WExec.seq t4 (WExec.seq t5 (WExec.seq t6
    (WExec.seq t7 (WExec.seq t8 (WExec.seq t9 (WExec.seq t10 t11)))))))))) rfl ?_
  rw [hlen, hlen1]

end Step

theorem wsetv_zero (σ : WState ns nr) (r : Fin nr) (h : σ.val r = 0) : σ.setv r 0 = σ := by
  rw [← h]; exact wsetv_same σ r

/-- **The level phase**: `KL'` written once, the level counter `V + 1` into `R 46`, the levels, `ℓ` back to `0`. -/
def phL (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) : WM ns nr :=
  .seq (kw G R (emK2 G R 21) (emK1 G R 21) 21) (.seq (UnionMachine.FrontTWKit.cloop (R 5) (R 47) (.inc (R 46)))
    (.seq (.whr (R 46) (.seq (.dec (R 46)) (bodyL G R))) (WM.clear (R 19))))

/-- The level phase's cost. -/
def phLCost (P : StarParams) (W V m : ℕ) : ℕ :=
  kwCost P W (200 * W + 200) (200 * W + 200) + 1 + ((V + 1) * (3 + 8) + 1 + 1 + (7 * (V + 1) + 1) + 1 +
    ((V + 1) * (lvlCost P W m + 4) + 1 + 1 + (3 * (V + 1) + 1)))

section Loop
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (P : StarParams) (N W V : ℕ) (g : NormalizedThresholdGate P.n) (cap : ℕ) (σ0 : WState ns nr)
  (hw : WReady G R P N W V g σ0) (hW : 2 * V + 3 ≤ W) (hKB : KeyBound g V) (hcapB : capKW P W ≤ cap)
  (hnk : P.n + P.k + 4 ≤ W)
include hG hR hw hW hKB hcapB hnk

set_option maxHeartbeats 1000000 in
/-- **The level phase**: `ACC` goes from `acc0` through every level, `ACC := accFold acc0 …`; the level key streams end
at their working length; the level register ends at `0`. -/
theorem phL_spec (ky ky' kl kl' : List Bool) (yh yl : ℕ) (hyh : yh < 2 ^ W)
    (hkl : kl.length ≤ (keyStream W (lK1 P g V N 0)).length) (hkl' : kl'.length ≤ (keyStream W (lK1 P g V N 0)).length)
    (h46 : σ0.val (R 46) = 0) (hcapL : (keyStream W (lK1 P g V N 0)).length + 2 ≤ cap) (hVc : V + 2 ≤ cap) :
    ∃ kl2 kl2' : List Bool, kl2.length = (keyStream W (lK1 P g V N 0)).length ∧
      kl2'.length = (keyStream W (lK1 P g V N 0)).length ∧
      WExec cap (phL G R) (jst G R W σ0 ky ky' kl kl' 0 (yh - yl) 0 0)
        ((jst G R W σ0 ky ky' kl2 kl2' 0 (accFold yh yl (fun ℓ => cK3 P g V N ℓ - cK1 P g V N ℓ) (V + 1)) 0 (V + 1)).setv
          (R 19) 0) (phLCost P W V (lK1 P g V N 0).length) := by
  have hW1 : 1 ≤ W := by omega
  set LL := (keyStream W (lK1 P g V N 0)).length with hLL
  set e : ℕ → ℕ := fun ℓ => cK3 P g V N ℓ - cK1 P g V N ℓ with he
  have fk1 : ∀ a b, (fK1 W V 0 a b).length ≤ 4 * W + 2 := fun a b => by simp [fK1, frame_eq_frameP]; omega
  have fk2 : ∀ a b, (fK2 W V 0 a b).length ≤ 4 * W + 2 := fun a b => by simp [fK2, frame_eq_frameP]; omega
  -- KL' := a level key stream
  have u1 := kwKS G hG R hR P N W V g cap σ0 hw ky ky' kl kl' 0 (yh - yl) 0 0 21 ⟨by decide, by decide⟩ hW hKB hcapB
    (emK2 G R 21) (emK1 G R 21) (fK2 W V 0) (fK1 W V 0) _ _
    (emK2_hyp G hG R hR cap W V 0 21 (by decide) (by decide) (SRm G) rfl rfl hW (by omega))
    (emK1_hyp G hG R hR cap W V 0 21 (by decide) (by decide) (SLm G) rfl rfl hW (by omega)) fk2 fk1 (lK1 P g V N 0)
    (streamK1 P g W V N 0 hW1 hKB) (by rw [(jst_get G hG R W σ0 _ _ _ _ _ _ _ _).2.2.2.1]; exact hkl')
  rw [jst_setKL' G hG R hR] at u1
  set σ1 := jst G R W σ0 ky ky' kl (keyStream W (lK1 P g V N 0)) 0 (yh - yl) 0 0 with hσ1
  -- R 46 := V + 1
  have hv1 : ∀ i : Fin 48, i ≠ 19 → σ1.val (R i) = σ0.val (R i) := fun i hi => by
    rw [jst_val G hG R hR, if_neg hi]
  have u2 := cloopM cap (R 5) (R 47) (hR.ne (by decide)) (.inc (R 46)) (fun σ j => σ.setv (R 46) j)
    (fun σ j v w => by
      apply WState.eq
      · rfl
      · rfl
      · funext i; simp only [WState.setv_val, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all [hR.eq_iff]
      · rfl) σ1 (V + 1) 3
    (by rw [hv1 5 (by decide)]; exact hw.rv) (by rw [hv1 47 (by decide)]; exact hw.zr 47 (by decide)) (by omega)
    (by
      intro j hj v w
      have h := WExec.inc (cap := cap) (R 46) (((σ1.setv (R 5) v).setv (R 47) w).setv (R 46) j) (by simp; omega)
      rw [show (((σ1.setv (R 5) v).setv (R 47) w).setv (R 46) j).val (R 46) = j by simp, wsetv_setv] at h
      exact h)
  have e0 : σ1.setv (R 46) 0 = σ1 := wsetv_zero σ1 (R 46) (by rw [hv1 46 (by decide)]; exact h46)
  simp only [e0] at u2
  -- the levels
  have hloop := UnionMachine.Round.wloopE cap (R 46) (bodyL G R) (lvlCost P W (lK1 P g V N 0).length) (V + 1)
    (fun j σ => ∃ kla kla' : List Bool, kla.length ≤ LL ∧ (0 < j → kla.length = LL) ∧ kla'.length = LL ∧ ∃ c,
      σ = (jst G R W σ0 ky ky' kla kla' 0 (accFold yh yl e j) 0 j).setv (R 46) c) (by omega)
    (by
      intro j hj σ hI hK
      obtain ⟨kla, kla', hla, -, hla', c, rfl⟩ := hI
      have hacc : accFold yh yl e j < 2 ^ W := lt_of_le_of_lt (accFold_le yh yl e j) (by omega)
      rw [wsetv_setv, jst_setv46 G hG R hR]
      obtain ⟨kl2, kl2', h2, h2', hstep⟩ := lvlStep_spec G hG R hR P N W V g cap (σ0.setv (R 46) (V + 1 - j - 1))
        (WReady_setv46 G R hR P N W V g σ0 hw _) hW hKB hcapB hnk ky ky' kla kla' (accFold yh yl e j) j (by omega) hacc
        hla hla' hcapL (by omega)
      refine ⟨_, hstep, ⟨kl2, kl2', le_of_eq h2, fun _ => h2, h2', V + 1 - j - 1, ?_⟩, ?_⟩
      · rw [jst_setv46 G hG R hR, accFold_succ]
      · rw [jst_val G hG R hR, if_neg (by decide)]; simp)
    (σ1.setv (R 46) (V + 1)) ⟨kl, keyStream W (lK1 P g V N 0), hkl, fun h => absurd h (by omega), rfl, V + 1, rfl⟩
    (by simp)
  obtain ⟨τ, hτ, ⟨kl2, kl2', -, h2, h2', c, rfl⟩, hτ0⟩ := hloop
  -- ℓ := 0
  have ec : c = 0 := by simpa using hτ0
  subst ec
  have e46 : (jst G R W σ0 ky ky' kl2 kl2' 0 (accFold yh yl e (V + 1)) 0 (V + 1)).setv (R 46) 0 =
      jst G R W σ0 ky ky' kl2 kl2' 0 (accFold yh yl e (V + 1)) 0 (V + 1) :=
    wsetv_zero _ (R 46) (by rw [jst_val G hG R hR, if_neg (by decide)]; exact h46)
  rw [e46] at hτ
  have hvτ : (jst G R W σ0 ky ky' kl2 kl2' 0 (accFold yh yl e (V + 1)) 0 (V + 1)).val (R 19) = V + 1 := by
    rw [jst_val G hG R hR]; simp
  have u4 := wclear_spec cap (R 19) (V + 1) _ hvτ (by rw [hvτ]; omega)
  refine ⟨kl2, kl2', h2 (by omega), h2', ?_⟩
  · unfold phL phLCost
    exact WExec.cast cap (WExec.seq u1 (WExec.seq u2 (WExec.seq hτ u4))) rfl (by omega)

end Loop

/-! ## The machine's total is the gate's row count -/

theorem ptsR_bound (P : StarParams) (g : NormalizedThresholdGate P.n) (V N : ℕ) (hKB : KeyBound g V) :
    ∀ q ∈ ptsR P g N, q.1.natAbs < 2 ^ V ∧ q.2.natAbs < 2 ^ V := by
  intro q hq
  unfold ptsR at hq
  obtain ⟨v, -, hv⟩ := List.mem_flatMap.mp hq
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hv
  have hs := sum_lt' P g V hKB
  have b1 : ∀ z : ℤ, |z| ≤ ∑ i, |g.weight i| → z.natAbs < 2 ^ V := fun z hz => natAbs_lt_of _ _ (by linarith)
  split_ifs
  · exact ⟨b1 _ (abs_halfR P g y), b1 _ (abs_halfR' P g y v)⟩
  · simp

/-- **The machine's total is the gate's row count at the coset.** -/
theorem gateRows_total (P : StarParams) (g : NormalizedThresholdGate P.n) (V N : ℕ) (hKB : KeyBound g V) :
    gateRows P (P.translationOfCodes (codesOfIdx P.s P.r N)) g =
      accFold (Yh P g V N) (Yl P g V N) (fun ℓ => cK3 P g V N ℓ - cK1 P g V N ℓ) (V + 1) := by
  rw [gateRows_pts P g N V hKB, gateJoin_tab V g.threshold _ _ (ptsR_bound P g V N hKB)]
  rw [← levels_fold (Yh P g V N) (Yl P g V N) (cK1 P g V N) (cK3 P g V N)
    (fun ℓ => K1_le_K3 (V + 1) ℓ _ _ (fun J hJ => (tabL_lt P g V N hKB J hJ).1)) (V + 1)]
  rfl

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
