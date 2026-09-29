import Proof.Wire_3_5.UnionMachine.RadAsm1

/-! # RADIX assembly (2): the setup fields, the seed word, the zero frames, the window word (P3:2585-2623,
P3:2150-2157)

On the setup's cell, after the numbers (`ph2`):

* `ph3` / **`ph3_spec`**: `R, Lg, cap` (from `rQ 13, 15, 14`), `M, τ₀, p, s` into `rF 0 … 6`, then
  `RadFieldsP.fieldsP` appends the setup fields `fieldsWordB` to the record stream `3` (position `rY 0`);
* `ph4` / **`ph4_spec`**: `t, ℓ₀` into `rT 0, 1`, then `RadSeed.hashSeedP` (the request's tail `frame l` onto `141`, the
  seed word `revWord l ℓ₀ (2t)` onto `144`);
* `ph5` / **`ph5_spec`**: `frame 0^{ℓ₀}` onto `145 … 148` (`RadTab.frameZ_spec`);
* `ph6` / **`ph6_spec`**: the window word `unary M ++ unary G ++ unary J ++ winRecs ++ [false]` onto `143`
  (`RadWin.winP_spec`).

Paper quantity of the main type: the RADIX record's setup fields and the fixed hash's table builder's inputs. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)

variable (cap : ℕ) (x : ℕ)

/-! ## Stage 4: the setup fields -/

def ph3 : WM (LNS x) LNR :=
  .seq (wcopyR (rQ 13) (rF 0) (rY 4)) (.seq (wcopyR (rQ 15) (rF 1) (rY 4)) (.seq (wcopyR (rQ 14) (rF 2) (rY 4))
  (.seq (wcopyR (rIn 13) (rF 3) (rY 4)) (.seq (wcopyR (rIn 12) (rF 4) (rY 4)) (.seq (wcopyR (rIn 1) (rF 5) (rY 4))
  (.seq (wcopyR (rIn 2) (rF 6) (rY 4)) (RadFieldsP.fieldsP (sk x 3) (rY 0) rF)))))))

def ph3Cost (R Lg cp M τ p s : ℕ) : ℕ :=
  (18 * R + 3) + 1 + ((18 * Lg + 3) + 1 + ((18 * cp + 3) + 1 + ((18 * M + 3) + 1 + ((18 * τ + 3) + 1 +
    ((18 * p + 3) + 1 + ((18 * s + 3) + 1 + RadFieldsP.fieldsCost cap R Lg cp M τ p))))))

theorem ph3_spec (σ : WState (LNS x) LNR) (R Lg cp M τ p s : ℕ) (hR : σ.val (rQ 13) = R) (hLg : σ.val (rQ 15) = Lg)
    (hcp : σ.val (rQ 14) = cp) (hM : σ.val (rIn 13) = M) (hτ : σ.val (rIn 12) = τ) (hp : σ.val (rIn 1) = p)
    (hs : σ.val (rIn 2) = s) (hf : ∀ i : Fin 48, σ.val (rF i) = 0) (hy0 : σ.val (rY 0) = 0) (hy4 : σ.val (rY 4) = 0)
    (h3 : σ.st (sk x 3) = []) (h3h : σ.sh (sk x 3) = 0) (cR : R ≤ cap) (cLg : Lg ≤ cap) (ccp : cp ≤ cap)
    (cM : M + 1 ≤ cap) (cτ1 : 1 ≤ τ) (cτ : 2 * τ ≤ cap) (cp2 : 2 ≤ p) (csp : s < p) (cpc : p ≤ cap)
    (cL : RadFieldsP.fieldsLen R Lg cp M τ p ≤ cap) :
    ∃ τ' : WState (LNS x) LNR, WExec cap (ph3 x) σ τ' (ph3Cost cap R Lg cp M τ p s) ∧
      Keep σ τ' (fun i => i = sk x 3) (fun r => r = rY 0 ∨ (48 ≤ r.val ∧ r.val < 96)) ∧
      τ'.st (sk x 3) = RadFieldsP.fieldsWordB R Lg M τ p s cp ∧
      τ'.sh (sk x 3) = (RadFieldsP.fieldsWordB R Lg M τ p s cp).length ∧
      τ'.val (rY 0) = (RadFieldsP.fieldsWordB R Lg M τ p s cp).length := by
  have hFQ : ∀ i j, rF i ≠ rQ j := fun i j e => QF j i e.symm
  have hQF : ∀ j i, rQ j ≠ rF i := QF
  have hFY : ∀ i j, rF i ≠ rY j := FY
  have hYF : ∀ j i, rY j ≠ rF i := fun j i e => FY i j e.symm
  have hFI : ∀ i k h, rF i ≠ rIn k h := Fin'
  have hIF : ∀ k h i, rIn k h ≠ rF i := fun k h i e => Fin' i k h e.symm
  have hQY : ∀ i j, rQ i ≠ rY j := QY
  have hYQ : ∀ j i, rY j ≠ rQ i := fun j i e => QY i j e.symm
  have hYI : ∀ i k h, rY i ≠ rIn k h := Yin
  have hIY : ∀ k h i, rIn k h ≠ rY i := fun k h i e => Yin i k h e.symm
  have s1 := wcopyR_spec cap (rQ 13) (rF 0) (rY 4) (hQF 13 0) (hQY 13 4) (hFY 0 4) σ (hf 0) hy4 (by omega)
  rw [hR] at s1
  set σ1 := σ.setv (rF 0) R with hσ1
  have s2 := wcopyR_spec cap (rQ 15) (rF 1) (rY 4) (hQF 15 1) (hQY 15 4) (hFY 1 4) σ1 (by simp [σ1, hf 1])
    (by simp [σ1, hYF, hy4]) (by simp [σ1, hQF, hLg]; omega)
  have w2 : σ1.val (rQ 15) = Lg := by simp [σ1, hQF, hLg]
  rw [w2] at s2
  set σ2 := σ1.setv (rF 1) Lg with hσ2
  have s3 := wcopyR_spec cap (rQ 14) (rF 2) (rY 4) (hQF 14 2) (hQY 14 4) (hFY 2 4) σ2 (by simp [σ2, σ1, hf 2])
    (by simp [σ2, σ1, hYF, hy4]) (by simp [σ2, σ1, hQF, hcp]; omega)
  have w3 : σ2.val (rQ 14) = cp := by simp [σ2, σ1, hQF, hcp]
  rw [w3] at s3
  set σ3 := σ2.setv (rF 2) cp with hσ3
  have s4 := wcopyR_spec cap (rIn 13) (rF 3) (rY 4) (hIF 13 _ 3) (hIY 13 _ 4) (hFY 3 4) σ3
    (by simp [σ3, σ2, σ1, hf 3]) (by simp [σ3, σ2, σ1, hYF, hy4]) (by simp [σ3, σ2, σ1, hIF, hM]; omega)
  have w4 : σ3.val (rIn 13) = M := by simp [σ3, σ2, σ1, hIF, hM]
  rw [w4] at s4
  set σ4 := σ3.setv (rF 3) M with hσ4
  have s5 := wcopyR_spec cap (rIn 12) (rF 4) (rY 4) (hIF 12 _ 4) (hIY 12 _ 4) (hFY 4 4) σ4
    (by simp [σ4, σ3, σ2, σ1, hf 4]) (by simp [σ4, σ3, σ2, σ1, hYF, hy4]) (by simp [σ4, σ3, σ2, σ1, hIF, hτ]; omega)
  have w5 : σ4.val (rIn 12) = τ := by simp [σ4, σ3, σ2, σ1, hIF, hτ]
  rw [w5] at s5
  set σ5 := σ4.setv (rF 4) τ with hσ5
  have s6 := wcopyR_spec cap (rIn 1) (rF 5) (rY 4) (hIF 1 _ 5) (hIY 1 _ 4) (hFY 5 4) σ5
    (by simp [σ5, σ4, σ3, σ2, σ1, hf 5]) (by simp [σ5, σ4, σ3, σ2, σ1, hYF, hy4])
    (by simp [σ5, σ4, σ3, σ2, σ1, hIF, hp]; omega)
  have w6 : σ5.val (rIn 1) = p := by simp [σ5, σ4, σ3, σ2, σ1, hIF, hp]
  rw [w6] at s6
  set σ6 := σ5.setv (rF 5) p with hσ6
  have s7 := wcopyR_spec cap (rIn 2) (rF 6) (rY 4) (hIF 2 _ 6) (hIY 2 _ 4) (hFY 6 4) σ6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, hf 6]) (by simp [σ6, σ5, σ4, σ3, σ2, σ1, hYF, hy4])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, hIF, hs]; omega)
  have w7 : σ6.val (rIn 2) = s := by simp [σ6, σ5, σ4, σ3, σ2, σ1, hIF, hs]
  rw [w7] at s7
  set σ7 := σ6.setv (rF 6) s with hσ7
  have hrd : RadFieldsP.Ready (sk x 3) rF σ7 R Lg cp M τ p s := by
    refine ⟨by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1], by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1],
      by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1], by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1],
      by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1], by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1],
      by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1], fun i hi => ?_, by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h3, h3h]⟩
    have n0 : i ≠ 0 := fun e => by subst e; simp at hi
    have n1 : i ≠ 1 := fun e => by subst e; simp at hi
    have n2 : i ≠ 2 := fun e => by subst e; simp at hi
    have n3 : i ≠ 3 := fun e => by subst e; simp at hi
    have n4 : i ≠ 4 := fun e => by subst e; simp at hi
    have n5 : i ≠ 5 := fun e => by subst e; simp at hi
    have n6 : i ≠ 6 := fun e => by subst e; simp at hi
    simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, n0, n1, n2, n3, n4, n5, n6, hf i]
  have s8 := RadFieldsP.fieldsP_spec cap (sk x 3) (rY 0) rF (fun i => hFY i 0) hrd cR cLg ccp cM cτ1 cτ cp2 csp cpc
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYF, hy0]; exact cL)
  refine ⟨_, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 (WExec.seq s7 s8)))))),
    ⟨fun i hi => ?_, fun r hr => ?_⟩, ?_, ?_, ?_⟩
  · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hi]
  · simp only [not_or, not_and, not_lt] at hr
    obtain ⟨hr0, hr48⟩ := hr
    have nF : ∀ i : Fin 48, r ≠ rF i := fun i e => by
      subst e; have := hr48 (by simp only [rF_val]; omega); simp only [rF_val] at this; omega
    simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, nF, hr0]
  · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h3]
  · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h3h]
  · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYF, hy0]

/-! ## Stage 5a (1): the seed word -/

def ph4 : WM (LNS x) LNR :=
  .seq (wcopyR (rIn 17) (rT 0) (rY 4)) (.seq (wcopyR (rIn 18) (rT 1) (rY 4))
    (RadSeed.hashSeedP rT (sk x 0) (sk x 141) (sk x 144)))

theorem ph4_spec (σ : WState (LNS x) LNR) (A l : List Bool) (t ℓ : ℕ) (hl : l.length = 2 * t * ℓ)
    (hs : σ.st (sk x 0) = frame (A ++ frame l)) (hsh : σ.sh (sk x 0) = 0) (h141 : σ.st (sk x 141) = [])
    (h141h : σ.sh (sk x 141) = 0) (h144 : σ.st (sk x 144) = []) (h144h : σ.sh (sk x 144) = 0)
    (ht : σ.val (rIn 17) = t) (hℓ : σ.val (rIn 18) = ℓ) (hT : ∀ i : Fin 10, σ.val (rT i) = 0)
    (hy4 : σ.val (rY 4) = 0)
    (hc : 2 * (A ++ frame l).length + 2 * t * (2 * ℓ + 2) + 4 * (t * ℓ) + ℓ + t + 2 ≤ cap) :
    ∃ τ' : WState (LNS x) LNR, WExec cap (ph4 x) σ τ'
        ((18 * t + 3) + 1 + ((18 * ℓ + 3) + 1 + RadSeed.hashSeedCost t ℓ (A ++ frame l).length)) ∧
      Keep σ τ' (fun i => i = sk x 141 ∨ i = sk x 144) (fun r => 128 ≤ r.val ∧ r.val < 138) ∧
      τ'.st (sk x 141) = frame l ∧ τ'.sh (sk x 141) = 0 ∧
      τ'.st (sk x 144) = FinalPass.HashSeed.revWord l ℓ (2 * t) ∧ τ'.sh (sk x 144) = 0 := by
  have hTY : ∀ i j, rT i ≠ rY j := fun i j e => YT j i e.symm
  have hYT : ∀ j i, rY j ≠ rT i := YT
  have hTI : ∀ i k h, rT i ≠ rIn k h := Tin
  have hIT : ∀ k h i, rIn k h ≠ rT i := fun k h i e => Tin i k h e.symm
  have hIY : ∀ k h i, rIn k h ≠ rY i := fun k h i e => Yin i k h e.symm
  have htc : t ≤ cap := by nlinarith
  have hℓc : ℓ ≤ cap := by omega
  have s1 := wcopyR_spec cap (rIn 17) (rT 0) (rY 4) (hIT 17 _ 0) (hIY 17 _ 4) (hTY 0 4) σ (hT 0) hy4 (by omega)
  rw [ht] at s1
  have s2 := wcopyR_spec cap (rIn 18) (rT 1) (rY 4) (hIT 18 _ 1) (hIY 18 _ 4) (hTY 1 4) (σ.setv (rT 0) t)
    (by simp [hT 1]) (by simp [hYT, hy4]) (by simp [hIT, hℓ]; omega)
  have w2 : (σ.setv (rT 0) t).val (rIn 18) = ℓ := by simp [hIT, hℓ]
  rw [w2] at s2
  have s3 := RadSeed.hashSeedP_spec cap rT (sk x 0) (sk x 141) (sk x 144) (fun e => by
      have := congrArg Fin.val (sk_inj x e); simp at this) (fun e => by
      have := congrArg Fin.val (sk_inj x e); simp at this) ((σ.setv (rT 0) t).setv (rT 1) ℓ) A l t ℓ hl
    (by simpa using hs) (by simpa using hsh) (by simpa using h141) (by simpa using h141h) (by simpa using h144)
    (by simpa using h144h) (by simp) (by simp) (fun i hi => by
      have n0 : i ≠ 0 := fun e => by subst e; simp at hi
      have n1 : i ≠ 1 := fun e => by subst e; simp at hi
      simp [n0, n1, hT i]) hc
  refine ⟨_, WExec.seq s1 (WExec.seq s2 s3), ⟨fun i hi => ?_, fun r hr => ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [not_or] at hi
    simp [Function.update_apply, hi.1, hi.2]
  · have nT : ∀ i : Fin 10, r ≠ rT i := fun i e => hr (by subst e; simp only [rT_val]; omega)
    simp [Function.update_apply, nT]
  · simp [Function.update_apply, show sk x 141 ≠ sk x 144 from fun e => by
      have := congrArg Fin.val (sk_inj x e); simp at this]
  · simpa using h141h
  · simp
  · simpa using h144h

/-! ## Stage 5a (2): the zero frames -/

def ph5 : WM (LNS x) LNR :=
  .seq (wcopyR (rIn 18) (rY 6) (rY 4)) (.seq (RadTab.frameZ (sk x 145) (rY 5) (rY 6) (rY 7) (rY 8))
    (.seq (RadTab.frameZ (sk x 146) (rY 5) (rY 6) (rY 7) (rY 8)) (.seq (RadTab.frameZ (sk x 147) (rY 5) (rY 6) (rY 7) (rY 8))
      (RadTab.frameZ (sk x 148) (rY 5) (rY 6) (rY 7) (rY 8)))))

theorem ph5_spec (σ : WState (LNS x) LNR) (ℓ : ℕ) (hℓ : σ.val (rIn 18) = ℓ)
    (hb : ∀ k : Fin 161, 145 ≤ k.val → k.val ≤ 148 → σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0)
    (hy : ∀ i : Fin 32, 4 ≤ i.val → i.val ≤ 8 → σ.val (rY i) = 0) (hc : 2 * ℓ + 1 ≤ cap) :
    ∃ τ' : WState (LNS x) LNR, WExec cap (ph5 x) σ τ'
        ((18 * ℓ + 3) + 1 + ((60 * ℓ + 40) + 1 + ((60 * ℓ + 40) + 1 + ((60 * ℓ + 40) + 1 + (60 * ℓ + 40))))) ∧
      Keep σ τ' (fun i => 145 ≤ i.val ∧ i.val ≤ 148) (fun r => r = rY 6) ∧
      ∀ k : Fin 161, 145 ≤ k.val → k.val ≤ 148 →
        τ'.st (sk x k) = frame (List.replicate ℓ false) ∧ τ'.sh (sk x k) = 0 := by
  have hIY : ∀ k h i, rIn k h ≠ rY i := fun k h i e => Yin i k h e.symm
  have y4 := hy 4 (by decide) (by decide)
  have y5 := hy 5 (by decide) (by decide)
  have y6 := hy 6 (by decide) (by decide)
  have y7 := hy 7 (by decide) (by decide)
  have y8 := hy 8 (by decide) (by decide)
  have s1 := wcopyR_spec cap (rIn 18) (rY 6) (rY 4) (hIY 18 _ 6) (hIY 18 _ 4) (rY.injective.ne (by decide)) σ y6 y4
    (by omega)
  rw [hℓ] at s1
  have ne56 : rY 5 ≠ rY 6 := rY.injective.ne (by decide)
  have fz : ∀ (k : Fin 161) (ω : WState (LNS x) LNR), ω.st (sk x k) = [] → ω.sh (sk x k) = 0 → ω.val (rY 5) = 0 →
      ω.val (rY 7) = 0 → ω.val (rY 8) = 0 → ω.val (rY 6) = ℓ →
      WExec cap (RadTab.frameZ (sk x k) (rY 5) (rY 6) (rY 7) (rY 8)) ω
        (ω.sets (sk x k) (frame (List.replicate ℓ false))) (60 * ℓ + 40) := fun k ω h1 h2 h3 h4 h5 h6 =>
    RadTab.frameZ_spec cap (sk x k) (rY 5) (rY 6) (rY 7) (rY 8) (rY.injective.ne (by decide)) (rY.injective.ne (by decide))
      (rY.injective.ne (by decide)) (rY.injective.ne (by decide)) (rY.injective.ne (by decide)) ω ℓ h1 h2 h3 h4 h5 h6 hc
  have b145 := hb 145 (by decide) (by decide)
  have b146 := hb 146 (by decide) (by decide)
  have b147 := hb 147 (by decide) (by decide)
  have b148 := hb 148 (by decide) (by decide)
  have skne : ∀ a b : Fin 161, a ≠ b → sk x a ≠ sk x b := fun a b h e => h (sk_inj x e)
  have f1 := fz 145 (σ.setv (rY 6) ℓ) (by simpa using b145.1) (by simpa using b145.2) (by simp [ne56, y5])
    (by simp [y7]) (by simp [y8]) (by simp)
  have f2 := fz 146 ((σ.setv (rY 6) ℓ).sets (sk x 145) (frame (List.replicate ℓ false)))
    (by simp [skne 146 145 (by decide), b146.1]) (by simpa using b146.2) (by simp [ne56, y5]) (by simp [y7])
    (by simp [y8]) (by simp)
  have f3 := fz 147 (((σ.setv (rY 6) ℓ).sets (sk x 145) (frame (List.replicate ℓ false))).sets (sk x 146)
      (frame (List.replicate ℓ false)))
    (by simp [skne 147 145 (by decide), skne 147 146 (by decide), b147.1]) (by simpa using b147.2)
    (by simp [ne56, y5]) (by simp [y7]) (by simp [y8]) (by simp)
  have f4 := fz 148 ((((σ.setv (rY 6) ℓ).sets (sk x 145) (frame (List.replicate ℓ false))).sets (sk x 146)
      (frame (List.replicate ℓ false))).sets (sk x 147) (frame (List.replicate ℓ false)))
    (by simp [skne 148 145 (by decide), skne 148 146 (by decide), skne 148 147 (by decide), b148.1])
    (by simpa using b148.2) (by simp [ne56, y5]) (by simp [y7]) (by simp [y8]) (by simp)
  refine ⟨_, WExec.seq s1 (WExec.seq f1 (WExec.seq f2 (WExec.seq f3 f4))), ⟨fun i hi => ?_, fun r hr => ?_⟩,
    fun k hk1 hk2 => ?_⟩
  · have n5 : i ≠ sk x 145 := fun e => hi (by subst e; simp [sk_val])
    have n6 : i ≠ sk x 146 := fun e => hi (by subst e; simp [sk_val])
    have n7 : i ≠ sk x 147 := fun e => hi (by subst e; simp [sk_val])
    have n8 : i ≠ sk x 148 := fun e => hi (by subst e; simp [sk_val])
    simp [Function.update_apply, n5, n6, n7, n8]
  · simp [Function.update_apply, hr]
  · have hk : k = 145 ∨ k = 146 ∨ k = 147 ∨ k = 148 := by
      rcases k with ⟨k, hk⟩
      simp only [Fin.ext_iff, Fin.val_ofNat] at *
      omega
    rcases hk with rfl | rfl | rfl | rfl
    · refine ⟨?_, by simpa using b145.2⟩
      simp [skne 145 146 (by decide), skne 145 147 (by decide), skne 145 148 (by decide)]
    · refine ⟨?_, by simpa using b146.2⟩
      simp [skne 146 147 (by decide), skne 146 148 (by decide)]
    · refine ⟨?_, by simpa using b147.2⟩
      simp [skne 147 148 (by decide)]
    · exact ⟨by simp, by simpa using b148.2⟩

/-! ## Stage 5a (3): the window word -/

def ph6 : WM (LNS x) LNR :=
  .seq (wcopyR (rIn 13) (rY 13) (rY 4)) (.seq (wcopyR (rIn 4) (rY 14) (rY 4)) (.seq (wcopyR (rIn 16) (rY 15) (rY 4))
    (.seq (wcopyR (rQ 7) (rY 16) (rY 4)) (RadWin.winP (sk x 143) (sk x 131) (rY 9) (rY 10) (rY 11) (rY 12) (rY 13)
      (rY 14) (rY 15) (rY 16)))))

theorem ph6_spec (σ : WState (LNS x) LNR) (w : List Bool) (M G J : ℕ) (hM : σ.val (rIn 13) = M)
    (hG : σ.val (rIn 4) = G) (hJ : σ.val (rIn 16) = J) (hw : σ.val (rQ 7) = w.length)
    (hS : σ.st (sk x 131) = w) (hSh : σ.sh (sk x 131) = 0) (hO : σ.st (sk x 143) = []) (hOh : σ.sh (sk x 143) = 0)
    (hy : ∀ i : Fin 32, 9 ≤ i.val → i.val ≤ 16 → σ.val (rY i) = 0) (hy4 : σ.val (rY 4) = 0)
    (hc : M + G + J + w.length + 4 ≤ cap) :
    ∃ τ' : WState (LNS x) LNR, WExec cap (ph6 x) σ τ'
        ((18 * M + 3) + 1 + ((18 * G + 3) + 1 + ((18 * J + 3) + 1 + ((18 * w.length + 3) + 1 +
          RadWin.winCost M G J w.length)))) ∧
      Keep σ τ' (fun i => i = sk x 143) (fun r => 109 ≤ r.val ∧ r.val ≤ 112) ∧
      τ'.st (sk x 143) = FinalPass.ListEval.unary M ++ FinalPass.ListEval.unary G ++ FinalPass.ListEval.unary J ++ w ++
        [false] ∧ τ'.sh (sk x 143) = 0 := by
  have hIY : ∀ k h i, rIn k h ≠ rY i := fun k h i e => Yin i k h e.symm
  have hQY : ∀ i j, rQ i ≠ rY j := QY
  have hYI : ∀ i k h, rY i ≠ rIn k h := Yin
  have hYQ : ∀ j i, rY j ≠ rQ i := fun j i e => QY i j e.symm
  have yv : ∀ i : Fin 32, 9 ≤ i.val → i.val ≤ 16 → σ.val (rY i) = 0 := hy
  have s1 := wcopyR_spec cap (rIn 13) (rY 13) (rY 4) (hIY 13 _ 13) (hIY 13 _ 4) (rY.injective.ne (by decide)) σ
    (yv 13 (by decide) (by decide)) hy4 (by omega)
  rw [hM] at s1
  have s2 := wcopyR_spec cap (rIn 4) (rY 14) (rY 4) (hIY 4 _ 14) (hIY 4 _ 4) (rY.injective.ne (by decide))
    (σ.setv (rY 13) M) (by simp [yv 14 (by decide) (by decide)]) (by simp [hy4]) (by simp [hIY, hG]; omega)
  have w2 : (σ.setv (rY 13) M).val (rIn 4) = G := by simp [hIY, hG]
  rw [w2] at s2
  have s3 := wcopyR_spec cap (rIn 16) (rY 15) (rY 4) (hIY 16 _ 15) (hIY 16 _ 4) (rY.injective.ne (by decide))
    ((σ.setv (rY 13) M).setv (rY 14) G) (by simp [yv 15 (by decide) (by decide)]) (by simp [hy4])
    (by simp [hIY, hJ]; omega)
  have w3 : ((σ.setv (rY 13) M).setv (rY 14) G).val (rIn 16) = J := by simp [hIY, hJ]
  rw [w3] at s3
  have s4 := wcopyR_spec cap (rQ 7) (rY 16) (rY 4) (hQY 7 16) (hQY 7 4) (rY.injective.ne (by decide))
    (((σ.setv (rY 13) M).setv (rY 14) G).setv (rY 15) J) (by simp [yv 16 (by decide) (by decide)]) (by simp [hy4])
    (by simp [hQY, hw]; omega)
  have w4 : (((σ.setv (rY 13) M).setv (rY 14) G).setv (rY 15) J).val (rQ 7) = w.length := by simp [hQY, hw]
  rw [w4] at s4
  have s5 := RadWin.winP_spec cap (sk x 143) (sk x 131) (fun e => by have := congrArg Fin.val (sk_inj x e); simp at this)
    (rY 9) (rY 10) (rY 11) (rY 12) (rY 13) (rY 14) (rY 15) (rY 16) (by simp [List.nodup_cons])
    ((((σ.setv (rY 13) M).setv (rY 14) G).setv (rY 15) J).setv (rY 16) w.length) w [] M G J
    (by simpa using hO) (by simpa using hOh) (by simpa using hS) (by simpa using hSh)
    (by simp [yv 9 (by decide) (by decide)]) (by simp [yv 10 (by decide) (by decide)])
    (by simp [yv 11 (by decide) (by decide)]) (by simp [yv 12 (by decide) (by decide)]) (by simp) (by simp) (by simp)
    (by simp) hc
  refine ⟨_, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5))), ⟨fun i hi => ?_, fun r hr => ?_⟩, ?_, ?_⟩
  · simp [Function.update_apply, hi]
  · have n13 : r ≠ rY 13 := fun e => hr (by subst e; simp only [rY_val]; omega)
    have n14 : r ≠ rY 14 := fun e => hr (by subst e; simp only [rY_val]; omega)
    have n15 : r ≠ rY 15 := fun e => hr (by subst e; simp only [rY_val]; omega)
    have n16 : r ≠ rY 16 := fun e => hr (by subst e; simp only [rY_val]; omega)
    simp [Function.update_apply, n13, n14, n15, n16]
  · simp
  · simpa using hOh

end NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
