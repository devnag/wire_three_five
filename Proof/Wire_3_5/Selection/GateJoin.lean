import Proof.Wire_3_5.Selection.GateArith
import Proof.Wire_3_5.Selection.JoinW

/-! # C1.4: the joins of one gate (P3:1345-1358)

Paper: "For each of the sixteen corner patterns, count pairs satisfying its four weak inequalities [...] Sum its exact
count" (P3:1345-1358). This module runs the joins on the gate layout: each join's key stream (`kw`, identified with
`keyStream W (A.map tagA ++ B.map tagB)` by C1.4's key math: `kwYh`, `kwYl`, `kwK1`, `kwK3`), C1.3's `joinW` into a
word, and the truncated subtraction `satSub` (C6's `ltB`, `subB`, `zeroB`). Main declarations: `satSub_spec`, the
`jst` update lemmas, **`kwYh`**, **`kwYl`**, **`kwK1`**, **`kwK3`**. Paper quantity: the joins' counts. -/

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
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

variable {ns nr : ℕ}

/-! ## Truncated subtraction -/

/-- `A := a − b` (truncated at `0`). -/
def satSub (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr :=
  .seq (ltB A B F R) (.ifr F (.seq (.dec F) (zeroB A B F R)) (subB A B F R))

theorem satSub_spec (cap W : ℕ) {A B : Fin (ns + 1)} {F R : Fin nr} (hAB : A ≠ B) (hFR : F ≠ R) (σ : WState ns nr)
    (a b : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0) (hR : σ.val R = 0) (ha : a < 2 ^ W)
    (hb : b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (satSub A B F R) σ (σ.sets A (frame (binary W (a - b)))) (130 * W + 30) := by
  have h1 := ltB_spec cap W hAB hFR σ a b hA hB hF hR ha hb hcap
  by_cases hlt : a < b
  · have hd := WExec.dec (cap := cap) F (σ.setv F (decide (a < b)).toNat) (by simp [hlt]; omega)
    have e : (σ.setv F (decide (a < b)).toNat).setv F ((σ.setv F (decide (a < b)).toNat).val F - 1) = σ := by
      simp [hlt]; rw [wsetv_setv, ← hF, wsetv_same]
    rw [e] at hd
    have hz := zeroB_spec cap W hAB hFR σ a b hA hB hF hR hcap
    rw [show a - b = 0 by omega]
    exact WExec.mono (WExec.seq h1 (WExec.ifrT (by simp [hlt]) (WExec.seq hd hz))) (by omega)
  · have e : σ.setv F (decide (a < b)).toNat = σ := by simp [hlt]; rw [← hF, wsetv_same]
    rw [e] at h1
    have hs := subB_spec cap W hAB hFR σ a b hA hB hF hR (by omega) ha hcap
    exact WExec.mono (WExec.seq h1 (WExec.ifrF hF hs)) (by omega)

theorem overlay_full (out L : List Bool) (h : L.length ≤ out.length) : overlay out L = out := by
  unfold overlay; rw [List.drop_eq_nil_of_le h, List.append_nil]

/-! ## The moving parts' updates -/

section Upd
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (W : ℕ) (σ0 : WState ns nr) (ky ky' kl kl' : List Bool) (jt acc ew ℓ : ℕ)
include hG hR

theorem jst_setKY (l : List Bool) :
    (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).sets (G 18) l = jst G R W σ0 l ky' kl kl' jt acc ew ℓ := by
  apply WState.eq
  · rfl
  · funext j; simp only [jst, WState.sets_st, WState.setv_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hG.eq_iff]
  · rfl
  · rfl

theorem jst_setKY' (l : List Bool) :
    (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).sets (G 19) l = jst G R W σ0 ky l kl kl' jt acc ew ℓ := by
  apply WState.eq
  · rfl
  · funext j; simp only [jst, WState.sets_st, WState.setv_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hG.eq_iff]
  · rfl
  · rfl

theorem jst_setKL (l : List Bool) :
    (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).sets (G 20) l = jst G R W σ0 ky ky' l kl' jt acc ew ℓ := by
  apply WState.eq
  · rfl
  · funext j; simp only [jst, WState.sets_st, WState.setv_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hG.eq_iff]
  · rfl
  · rfl

theorem jst_setKL' (l : List Bool) :
    (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).sets (G 21) l = jst G R W σ0 ky ky' kl l jt acc ew ℓ := by
  apply WState.eq
  · rfl
  · funext j; simp only [jst, WState.sets_st, WState.setv_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hG.eq_iff]
  · rfl
  · rfl

theorem jst_setJT (v : ℕ) :
    (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).sets (G 23) (frame (binary W v)) = jst G R W σ0 ky ky' kl kl' v acc ew ℓ := by
  apply WState.eq
  · rfl
  · funext j; simp only [jst, WState.sets_st, WState.setv_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hG.eq_iff]
  · rfl
  · rfl

theorem jst_setACC (v : ℕ) :
    (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).sets (G 24) (frame (binary W v)) = jst G R W σ0 ky ky' kl kl' jt v ew ℓ := by
  apply WState.eq
  · rfl
  · funext j; simp only [jst, WState.sets_st, WState.setv_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hG.eq_iff]
  · rfl
  · rfl

theorem jst_setEW (v : ℕ) :
    (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).sets (G 25) (frame (binary W v)) = jst G R W σ0 ky ky' kl kl' jt acc v ℓ := by
  apply WState.eq
  · rfl
  · funext j; simp only [jst, WState.sets_st, WState.setv_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hG.eq_iff]
  · rfl
  · rfl

theorem jst_next :
    ((jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).setv (R 19) (ℓ + 1)).sets (G 17) (frame (binary W (2 * 2 ^ (ℓ + 1)))) =
      jst G R W σ0 ky ky' kl kl' jt acc ew (ℓ + 1) := by
  apply WState.eq
  · rfl
  · funext j; simp only [jst, WState.sets_st, WState.setv_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hG.eq_iff, pow_succ, Nat.mul_comm]
  · funext j; simp only [jst, WState.sets_val, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hR.eq_iff]
  · rfl

theorem jst_setv46 (c : ℕ) :
    (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).setv (R 46) c = jst G R W (σ0.setv (R 46) c) ky ky' kl kl' jt acc ew ℓ := by
  apply WState.eq
  · rfl
  · rfl
  · funext j; simp only [jst, WState.sets_val, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hR.eq_iff]
  · rfl

theorem jst_num (hs : ∀ i : Fin 28, σ0.sh (G i) = 0) :
    NumOn (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ) (G 23) W jt ∧
    NumOn (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ) (G 24) W acc ∧
    NumOn (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ) (G 25) W ew ∧
    NumOn (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ) (G 17) W (2 ^ (ℓ + 1)) := by
  refine ⟨⟨?_, hs 23⟩, ⟨?_, hs 24⟩, ⟨?_, hs 25⟩, ⟨?_, hs 17⟩⟩ <;>
    simp [jst, Function.update_apply, hG.eq_iff]

end Upd

/-! ## Each join's key stream on the gate layout -/

section Streams
variable (P : StarParams) (g : NormalizedThresholdGate P.n) (W V N ℓ : ℕ) (hW1 : 1 ≤ W) (hKB : KeyBound g V)
include hW1 hKB

/-- The right half's machine keys for an emitter value `f`. -/
abbrev RK (f : ℕ → ℕ → List Bool) : List Bool :=
  (List.range (2 ^ (P.s * hh P))).flatMap (fun u => (List.range (2 ^ rw P)).flatMap (fun x =>
    f (min (aW P (recsR P g) (2 ^ V) 0 (fR P) N x) (aW' P (recsR P g) (2 ^ V) 0 (fR P) N u x))
      (max (aW P (recsR P g) (2 ^ V) 0 (fR P) N x) (aW' P (recsR P g) (2 ^ V) 0 (fR P) N u x))))

/-- The left half's machine keys for an emitter value `f`. -/
abbrev LK (f : ℕ → ℕ → List Bool) : List Bool :=
  (List.range (2 ^ (P.s * hh P))).flatMap (fun u => (List.range (2 ^ lw P)).flatMap (fun x =>
    f (min (aW P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N x)
        (aW' P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N u x))
      (max (aW P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N x)
        (aW' P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N u x))))

theorem streamYh : RK P g V N (fYR W) ++ LK P g V N (fYLh W) ++ [false] =
    keyStream W ((innerY (tabR V (ptsR P g N))).map tagA ++
      ((tabL V g.threshold (ptsL P g N)).map Prod.snd).map tagB) := by
  rw [keyStream_eq W hW1, List.flatMap_append, innerY_stream, snd_stream, tabR_eq P g V N hKB, tabL_eq P g V N hKB]

theorem streamYl : RK P g V N (fYR W) ++ LK P g V N (fYLl W) ++ [false] =
    keyStream W ((innerY (tabR V (ptsR P g N))).map tagA ++
      ((tabL V g.threshold (ptsL P g N)).map Prod.fst).map tagB) := by
  rw [keyStream_eq W hW1, List.flatMap_append, innerY_stream, fst_stream, tabR_eq P g V N hKB, tabL_eq P g V N hKB]

theorem streamK1 : RK P g V N (fK2 W V ℓ) ++ LK P g V N (fK1 W V ℓ) ++ [false] =
    keyStream W ((lvlK2 (V + 1) ℓ (tabR V (ptsR P g N))).map tagA ++
      (lvlK1 (V + 1) ℓ (tabL V g.threshold (ptsL P g N))).map tagB) := by
  rw [keyStream_eq W hW1, List.flatMap_append, lvl2_stream, lvl1_stream, tabR_eq P g V N hKB, tabL_eq P g V N hKB]

theorem streamK3 : RK P g V N (fK2 W V ℓ) ++ LK P g V N (fK3 W V ℓ) ++ [false] =
    keyStream W ((lvlK2 (V + 1) ℓ (tabR V (ptsR P g N))).map tagA ++
      (lvlK3 (V + 1) ℓ (tabL V g.threshold (ptsL P g N))).map tagB) := by
  rw [keyStream_eq W hW1, List.flatMap_append, lvl2_stream, lvl3_stream, tabR_eq P g V N hKB, tabL_eq P g V N hKB]

end Streams

/-! ## The tables' sizes and ranges -/

theorem keyOf_mm_lt (V : ℕ) (a b : ℤ) (ha : a.natAbs < 2 ^ V) (hb : b.natAbs < 2 ^ V) :
    keyOf V (min a b) < 2 ^ (V + 1) ∧ keyOf V (max a b) < 2 ^ (V + 1) := by
  constructor
  · rcases min_choice a b with h | h <;> rw [h]
    · exact (Joins.rKey V a a ha ha).1
    · exact (Joins.rKey V b b hb hb).1
  · rcases max_choice a b with h | h <;> rw [h]
    · exact (Joins.rKey V a a ha ha).1
    · exact (Joins.rKey V b b hb hb).1

section Tabs
variable (P : StarParams) (g : NormalizedThresholdGate P.n) (V N : ℕ) (hKB : KeyBound g V)

theorem ptsR_length : (ptsR P g N).length = 2 ^ (P.s * hh P) * 2 ^ rw P := by
  unfold ptsR; rw [List.length_flatMap]; simp [List.sum_replicate]

theorem ptsL_length : (ptsL P g N).length = 2 ^ (P.s * hh P) * 2 ^ lw P := by
  unfold ptsL; rw [List.length_flatMap]; simp [List.sum_replicate]

include hKB

theorem tabR_lt : ∀ d ∈ tabR V (ptsR P g N), d.1 < 2 ^ (V + 1) ∧ d.2 < 2 ^ (V + 1) := by
  intro d hd
  unfold tabR at hd
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
  unfold ptsR at hq
  obtain ⟨v, -, hv⟩ := List.mem_flatMap.mp hq
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hv
  have hs := sum_lt' P g V hKB
  have b1 : ∀ z : ℤ, |z| ≤ ∑ i, |g.weight i| → z.natAbs < 2 ^ V := fun z hz => natAbs_lt_of _ _ (by linarith)
  have hq1 : (if okR P N y then (halfR P g y, halfR' P g y v) else (0, 0)).1.natAbs < 2 ^ V := by
    split_ifs
    · exact b1 _ (abs_halfR P g y)
    · simp
  have hq2 : (if okR P N y then (halfR P g y, halfR' P g y v) else (0, 0)).2.natAbs < 2 ^ V := by
    split_ifs
    · exact b1 _ (abs_halfR' P g y v)
    · simp
  exact keyOf_mm_lt V _ _ hq1 hq2

theorem tabL_lt : ∀ d ∈ tabL V g.threshold (ptsL P g N), d.1 < 2 ^ (V + 1) ∧ d.2 < 2 ^ (V + 1) := by
  intro d hd
  unfold tabL at hd
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
  unfold ptsL at hp
  obtain ⟨u, -, hu⟩ := List.mem_flatMap.mp hp
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hu
  have hk := keyBound_int P g V hKB
  have b1 : ∀ z : ℤ, |z| ≤ ∑ i, |g.weight i| → (g.threshold - z).natAbs < 2 ^ V := fun z hz =>
    natAbs_lt_of _ _ (by have := abs_sub g.threshold z; linarith)
  have hz0 : |(0 : ℤ)| ≤ ∑ i, |g.weight i| := by
    simp only [abs_zero]; exact Finset.sum_nonneg (fun i _ => abs_nonneg (g.weight i))
  have hp1 : (g.threshold - (if okL P N x then (halfL P g x, halfL' P g x u) else (0, 0)).1).natAbs < 2 ^ V := by
    split_ifs
    · exact b1 _ (abs_halfL P g x)
    · exact b1 _ hz0
  have hp2 : (g.threshold - (if okL P N x then (halfL P g x, halfL' P g x u) else (0, 0)).2).natAbs < 2 ^ V := by
    split_ifs
    · exact b1 _ (abs_halfL' P g x u)
    · exact b1 _ hz0
  unfold loOf hiOf
  exact keyOf_mm_lt V _ _ hp1 hp2

end Tabs

/-! ## One join on the gate layout -/

/-- The join program: key stream `G a`, its scratch `G b`, the counter `G 22`, the total `G t`. -/
def JW (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (a b t : Fin 28) : WM ns nr :=
  joinW (G a) (G b) (G 22) (G t) (R 37) (R 38) (R 39) (R 44) (R 6) (R 7) (R 45)

section Join
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (P : StarParams) (N W V : ℕ) (g : NormalizedThresholdGate P.n) (cap : ℕ) (σ0 : WState ns nr)
  (hw : WReady G R P N W V g σ0) (hW1 : 1 ≤ W)
include hG hR hw hW1

theorem JW_spec (a b t : Fin 28) (hab : a ≠ b) (ha : a.val = 18 ∨ a.val = 20) (hb : b.val = 19 ∨ b.val = 21)
    (ht : t.val = 23 ∨ t.val = 24 ∨ t.val = 25) (σ : WState ns nr) (hσsh : ∀ i : Fin 28, σ.sh (G i) = 0)
    (hσv : ∀ i : Fin 48, zeroReg i = true → σ.val (R i) = 0) (hcnt : σ.st (G 22) = frame (binary W 0))
    (A B l : List ℕ) (t0 : ℕ) (hl : l = A.map tagA ++ B.map tagB) (hlt : ∀ x ∈ l, x < 2 ^ W)
    (hS : σ.st (G a) = keyStream W l) (hS' : (σ.st (G b)).length = (keyStream W l).length)
    (hT : σ.st (G t) = frame (binary W t0)) (hA : A.length < 2 ^ W) (hj : t0 + joinLt A B < 2 ^ W)
    (hcap : (keyStream W l).length + 2 ≤ cap) :
    ∃ junk : List Bool, junk.length = (keyStream W l).length ∧
      WExec cap (JW G R a b t) σ (((σ.sets (G a) (keyStream W (sorted l))).sets (G b) junk).sets (G t)
        (frame (binary W (t0 + joinLt A B)))) (joinCost W l.length) := by
  have gne : ∀ x y : Fin 28, x.val ≠ y.val → G x ≠ G y := fun x y h => hG.ne (fun e => h (congrArg Fin.val e))
  have hJ := joinW_spec cap W (S := G a) (S' := G b) (CNT := G 22) (TOT := G t) (CA := R 37) (CB := R 38) (K := R 39)
    (C := R 44) (F := R 6) (R := R 7) (G := R 45) (hG.ne hab) (gne a 22 (by omega)) (gne a t (by omega))
    (gne b 22 (by omega)) (gne b t (by omega)) (gne 22 t (by omega)) (hR.ne (by decide)) (hR.ne (by decide))
    (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide)) (hR.ne (by decide))
    (hR.ne (by decide)) (hR.ne (by decide))
  exact hJ σ A B l t0 hW1 (by rw [hl]) hlt hS (hσsh a) hS' (hσsh b) ⟨hcnt, hσsh 22⟩ ⟨hT, hσsh t⟩ hA hj
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hσv _ (by decide)) hcap

end Join

/-! ## A key stream written as a `keyStream` -/

/-- The key-stream writer's cost. -/
def kwCost (P : StarParams) (W cR cL : ℕ) : ℕ :=
  enumCost (2 ^ (P.s * hh P)) (2 ^ rw P) (pointCost (hh P) P.b (fR P) 0 P.s W + cR + 200 * W + 30) (lw P + 1)
    (P.s * hh P + 1) + 1 + (enumCost (2 ^ (P.s * hh P)) (2 ^ lw P)
      (pointCost (hh P) P.b (fL P) (hh P) P.s W + cL + 200 * W + 30) (lw P + 1) (P.s * hh P + 1) + 1 +
        (5 * (2 ^ (P.s * hh P) * ((2 ^ lw P + 2 ^ rw P) * (4 * W + 2))) + 14))

section KS
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (P : StarParams) (N W V : ℕ) (g : NormalizedThresholdGate P.n) (cap : ℕ) (σ0 : WState ns nr)
  (hw : WReady G R P N W V g σ0) (ky ky' kl kl' : List Bool) (jt acc ew ℓ : ℕ) (k : Fin 28)
  (hk : 18 ≤ k.val ∧ k.val ≤ 21) (hW : 2 * V + 3 ≤ W) (hKB : KeyBound g V) (hcapB : capKW P W ≤ cap)
include hG hR hw hk hW hKB hcapB

theorem kwKS (EMR EML : Fin (ns + 1) → Fin (ns + 1) → Fin nr → Fin nr → WM ns nr) (fr' fl' : ℕ → ℕ → List Bool)
    (cR cL : ℕ) (hEmR : EmitHyp cap W V (SRm G) (G k) (R 27) (R 28) (R 29) EMR (EmEnv G R W V ℓ) fr' cR)
    (hEmL : EmitHyp cap W V (SLm G) (G k) (R 27) (R 28) (R 29) EML (EmEnv G R W V ℓ) fl' cL)
    (hfr : ∀ a b, (fr' a b).length ≤ 4 * W + 2) (hfl : ∀ a b, (fl' a b).length ≤ 4 * W + 2) (lst : List ℕ)
    (hst : RK P g V N fr' ++ LK P g V N fl' ++ [false] = keyStream W lst)
    (hold : ((jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).st (G k)).length ≤ (keyStream W lst).length) :
    WExec cap (kw G R EMR EML k) (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ)
      ((jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).sets (G k) (keyStream W lst)) (kwCost P W cR cL) := by
  have h := kw_spec G hG R hR P N W V g cap σ0 hw ky ky' kl kl' jt acc ew ℓ k hk hW hKB hcapB EMR EML fr' fl' cR cL
    hEmR hEmL hfr hfl
  simp only [RK, LK] at hst
  rw [hst, overlay_full _ _ hold] at h
  exact h

end KS

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
