import Proof.Wire_3_5.FinalPass.S5TZf
import Proof.Wire_3_5.FinalPass.S5TSeed3

/-! # S5-THR, part 18: the fixed hash's inputs for stage 4 (P3:2150-2157, 2220-2231)

On a layout with nineteen named streams `S` and forty named registers `Rg`, the first half of the THR half's tail:
the hash bits' frame from the input (`seedSrc`), the hash coefficients' seed word (`HashSeed.seedW`), stage 4's input
word from W6's ports (`winW`), and four framed zeros (`zfr`): every stream stage 4's table builder reads.

Streams: `0` input, `1` template, `2 … 9` W6's ports `3, 8, 9, 12, 13, 15, 18, 19`, `10 … 16` `SRC`, `SEED`, `WIN`,
`X`, `ACC`, `NEW`, `ST`, `17`, `18` THR slots `14`, `15`. Registers: `0 … 9` `seedSrc`'s (`1` = `t`, `2` = `ℓ₀`),
`10 … 13` `seedW`'s, `14`, `15` `winW`'s, `16 … 18` `zfr`'s, `19 … 34` the table builder's, `35 … 38` slot `15`'s,
`39` the tuple size `a`.

* `tailE`, `tailAW`, **`tailA_spec`**.

Paper quantities of the main type: the hash's seed word `seedWord ℓ₀ (coefsRev (coefVal MP s))` and stage 4's input
word `winWord M M J W` (the fixed hash's coefficients and levels). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed
open NearCubicWires.WireExponent3_5.Filters

variable {ns nr : ℕ} (cap : ℕ)

/-- `seedSrc`'s ten registers: the first ten named registers. -/
def tailE (Rg : Fin 40 ↪ Fin nr) : Fin 10 ↪ Fin nr :=
  ⟨fun j => Rg (Fin.castLE (by omega) j), fun a b h => Fin.castLE_injective _ (Rg.injective h)⟩

theorem tailE_apply (Rg : Fin 40 ↪ Fin nr) (j : Fin 10) : tailE Rg j = Rg ⟨j.val, by omega⟩ := rfl

/-- **The tail's first half**: the hash bits, the seed word, stage 4's input word, four framed zeros. -/
def tailAW (S : Fin 19 ↪ Fin (ns + 1)) (Rg : Fin 40 ↪ Fin nr) : WM ns nr :=
  .seq (seedSrc (S 0) (S 1) (S 6) (S 7) (S 10) (tailE Rg))
  (.seq (seedW (S 10) (S 11) (Rg 2) (Rg 1) (Rg 10) (Rg 11) (Rg 12) (Rg 13))
  (.seq (winW (S 4) (S 5) (S 8) (S 12) (Rg 14) (Rg 15))
  (.seq (zfr (S 13) (Rg 16) (Rg 2) (Rg 17) (Rg 18)) (.seq (zfr (S 14) (Rg 16) (Rg 2) (Rg 17) (Rg 18))
  (.seq (zfr (S 15) (Rg 16) (Rg 2) (Rg 17) (Rg 18)) (zfr (S 16) (Rg 16) (Rg 2) (Rg 17) (Rg 18)))))))

/-- The first half's cost bound. -/
def tailACost (m t ℓ w : ℕ) : ℕ :=
  1000 * (m + t + ℓ + 1) ^ 2 + 1 + (seedCost ℓ t + 1 + (30 * w + 100 + 1 + (zfrCost ℓ + 1 + (zfrCost ℓ + 1 +
    (zfrCost ℓ + 1 + zfrCost ℓ)))))

theorem tailA_spec (S : Fin 19 ↪ Fin (ns + 1)) (Rg : Fin 40 ↪ Fin nr) (σ : WState ns nr) (MP : MajorantParams)
    (s : Fin (2 * MP.t * MP.ell0) → Bool) (pre : List Bool)
    (hI : σ.st (S 0) = frame (pre ++ frame (List.ofFn s)))
    (hT : σ.st (S 1) = sent ((pre ++ frame (List.ofFn s)).length + 1))
    (h9 : σ.st (S 4) = List.replicate MP.M true) (h12 : σ.st (S 5) = List.replicate MP.J true)
    (h13 : σ.st (S 6) = List.replicate MP.t true) (h15 : σ.st (S 7) = List.replicate MP.ell0 true)
    (h18 : σ.st (S 8) = (ListEval.levels MP.J).flatMap (Hash4.winRec MP.J MP.W))
    (hbl : ∀ k : Fin 19, 10 ≤ k.val → σ.st (S k) = []) (hsh : ∀ i, σ.sh i = 0)
    (hz : ∀ k : Fin 40, k.val < 19 → σ.val (Rg k) = 0)
    (hc1 : 100 * ((pre ++ frame (List.ofFn s)).length + 1) + 10 * (MP.t + MP.ell0) ≤ cap)
    (hc2 : 2 * MP.t * (2 * MP.ell0 + 2) + 1 + MP.ell0 + MP.t ≤ cap)
    (hc3 : (Hash4.winWord MP.M MP.M MP.J MP.W).length ≤ cap) (hc4 : 2 * MP.ell0 + 2 ≤ cap) :
    ∃ τ c, WExec cap (tailAW S Rg) σ τ c ∧
      c ≤ tailACost (pre ++ frame (List.ofFn s)).length MP.t MP.ell0 (Hash4.winWord MP.M MP.M MP.J MP.W).length ∧
      τ.st (S 11) = Hash4.seedWord MP.ell0 (Hash4.coefsRev (MajorantBits.coefVal MP s)) ∧
      τ.st (S 12) = Hash4.winWord MP.M MP.M MP.J MP.W ∧
      τ.st (S 13) = frame (binary MP.ell0 0) ∧ τ.st (S 14) = frame (binary MP.ell0 0) ∧
      τ.st (S 15) = frame (binary MP.ell0 0) ∧ τ.st (S 16) = frame (binary MP.ell0 0) ∧
      (∀ i, i ≠ S 10 → i ≠ S 11 → i ≠ S 12 → i ≠ S 13 → i ≠ S 14 → i ≠ S 15 → i ≠ S 16 → τ.st i = σ.st i) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ k : Fin 40, 19 ≤ k.val → τ.val (Rg k) = σ.val (Rg k)) := by
  have hS : ∀ {i j : Fin 19}, i ≠ j → S i ≠ S j := fun h => S.injective.ne h
  have hR : ∀ {i j : Fin 40}, i ≠ j → Rg i ≠ Rg j := fun h => Rg.injective.ne h
  -- 1: the hash bits' frame
  obtain ⟨σ1, c1, e1, hc1', s1, s1o, s1h, v1, v2, v0, vo, _⟩ := seedSrc_spec cap (S 0) (S 1) (S 6) (S 7) (S 10)
    (hS (by decide)) (hS (by decide)) (hS (by decide)) (hS (by decide)) (hS (by decide)) (hS (by decide))
    (hS (by decide)) (hS (by decide)) (hS (by decide)) (hS (by decide)) (tailE Rg) pre (List.ofFn s) MP.t MP.ell0 σ
    hI (hsh _) hT (hsh _) h13 (hsh _) h15 (hsh _) (hbl 10 (by decide)) (hsh _)
    (fun j => by rw [tailE_apply]; exact hz _ (by have := j.isLt; simp; omega)) (by simp) hc1
  have v1' : σ1.val (Rg 1) = MP.t := v1
  have v2' : σ1.val (Rg 2) = MP.ell0 := v2
  have vout : ∀ k : Fin 40, 10 ≤ k.val → σ1.val (Rg k) = σ.val (Rg k) := fun k hk =>
    vo _ (fun j h => by rw [tailE_apply] at h; have := congrArg Fin.val (Rg.injective h); simp at this; omega)
  have sh1 : ∀ i, σ1.sh i = 0 := fun i => by rw [s1h, hsh]
  -- 2: the seed word
  have e2 := seed_hash cap (S 10) (S 11) (Rg 2) (Rg 1) (Rg 10) (Rg 11) (Rg 12) (Rg 13) (hS (by decide))
    (hR (by decide)) (hR (by decide)) (hR (by decide)) (hR (by decide)) (hR (by decide)) (hR (by decide))
    (hR (by decide)) (hR (by decide)) (hR (by decide)) (hR (by decide)) (hR (by decide)) (hR (by decide))
    (hR (by decide)) MP s σ1 s1 (sh1 _) (by rw [s1o _ (hS (by decide)), hbl 11 (by decide)]) (sh1 _) v2' v1'
    (by rw [vout 10 (by decide), hz 10 (by decide)]) (by rw [vout 11 (by decide), hz 11 (by decide)])
    (by rw [vout 12 (by decide), hz 12 (by decide)]) (by rw [vout 13 (by decide), hz 13 (by decide)]) hc2
  -- 3: stage 4's input word
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.sets (S 11) (Hash4.seedWord MP.ell0 (Hash4.coefsRev (MajorantBits.coefVal MP s))) :=
    ⟨_, rfl⟩
  rw [← hσ2] at e2
  have st2 : ∀ i, i ≠ S 11 → σ2.st i = σ1.st i := fun i hi => by rw [hσ2]; simp [Function.update_apply, hi]
  have e3 := winW_hash cap (S 4) (S 5) (S 8) (S 12) (hS (by decide)) (hS (by decide)) (hS (by decide)) (Rg 14) (Rg 15)
    (hR (by decide)) σ2 MP.M MP.J MP.W
    (by rw [st2 _ (hS (by decide)), s1o _ (hS (by decide)), h9]) (by rw [hσ2]; exact sh1 _)
    (by rw [st2 _ (hS (by decide)), s1o _ (hS (by decide)), h12]) (by rw [hσ2]; exact sh1 _)
    (by rw [st2 _ (hS (by decide)), s1o _ (hS (by decide)), h18]) (by rw [hσ2]; exact sh1 _)
    (by rw [st2 _ (hS (by decide)), s1o _ (hS (by decide)), hbl 12 (by decide)]) (by rw [hσ2]; exact sh1 _)
    (by rw [hσ2]; simp only [WState.sets_val]; rw [vout 14 (by decide), hz 14 (by decide)])
    (by rw [hσ2]; simp only [WState.sets_val]; rw [vout 15 (by decide), hz 15 (by decide)]) hc3
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = σ2.sets (S 12) (Hash4.winWord MP.M MP.M MP.J MP.W) := ⟨_, rfl⟩
  rw [← hσ3] at e3
  have st3 : ∀ i, i ≠ S 12 → i ≠ S 11 → σ3.st i = σ1.st i := fun i h1 h2 => by
    rw [hσ3]; simp only [WState.sets_st, Function.update_apply, h1, if_false]; exact st2 i h2
  have sh3 : ∀ i, σ3.sh i = 0 := fun i => by rw [hσ3, hσ2]; exact sh1 i
  have val3 : ∀ r, σ3.val r = σ1.val r := fun r => by rw [hσ3, hσ2]; rfl
  -- 4: the framed zeros
  have ez : ∀ (k : Fin 19) (ω : WState ns nr), 13 ≤ k.val → ω.st (S k) = [] → ω.sh (S k) = 0 →
      (∀ r, ω.val r = σ1.val r) →
      WExec cap (zfr (S k) (Rg 16) (Rg 2) (Rg 17) (Rg 18)) ω (ω.sets (S k) (frame (binary MP.ell0 0)))
        (zfrCost MP.ell0) := fun k ω _ ho hoh hv =>
    zfr_spec cap (S k) (Rg 16) (Rg 2) (Rg 17) (Rg 18) (hR (by decide)) (hR (by decide)) (hR (by decide))
      (hR (by decide)) ω MP.ell0 ho hoh (by rw [hv, v2']) (by rw [hv, vout 17 (by decide), hz 17 (by decide)])
      (by rw [hv, vout 18 (by decide), hz 18 (by decide)]) (by rw [hv, vout 16 (by decide), hz 16 (by decide)]) hc4
  have e4 := ez 13 σ3 (by decide) (by rw [st3 _ (hS (by decide)) (hS (by decide)), s1o _ (hS (by decide)),
    hbl 13 (by decide)]) (sh3 _) val3
  have e5 := ez 14 (σ3.sets (S 13) (frame (binary MP.ell0 0))) (by decide)
    (by simp only [WState.sets_st, Function.update_apply, if_neg (hS (by decide) : S 14 ≠ S 13)]
        rw [st3 _ (hS (by decide)) (hS (by decide)), s1o _ (hS (by decide)), hbl 14 (by decide)])
    (sh3 _) val3
  have e6 := ez 15 ((σ3.sets (S 13) (frame (binary MP.ell0 0))).sets (S 14) (frame (binary MP.ell0 0))) (by decide)
    (by simp only [WState.sets_st, Function.update_apply, if_neg (hS (by decide) : S 15 ≠ S 14),
          if_neg (hS (by decide) : S 15 ≠ S 13)]
        rw [st3 _ (hS (by decide)) (hS (by decide)), s1o _ (hS (by decide)), hbl 15 (by decide)])
    (sh3 _) val3
  have e7 := ez 16 (((σ3.sets (S 13) (frame (binary MP.ell0 0))).sets (S 14) (frame (binary MP.ell0 0))).sets (S 15)
      (frame (binary MP.ell0 0))) (by decide)
    (by simp only [WState.sets_st, Function.update_apply, if_neg (hS (by decide) : S 16 ≠ S 15),
          if_neg (hS (by decide) : S 16 ≠ S 14), if_neg (hS (by decide) : S 16 ≠ S 13)]
        rw [st3 _ (hS (by decide)) (hS (by decide)), s1o _ (hS (by decide)), hbl 16 (by decide)])
    (sh3 _) val3
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold tailACost; omega
  · simp only [WState.sets_st, Function.update_apply, if_neg (hS (by decide) : S 11 ≠ S 16),
      if_neg (hS (by decide) : S 11 ≠ S 15), if_neg (hS (by decide) : S 11 ≠ S 14),
      if_neg (hS (by decide) : S 11 ≠ S 13), if_neg (hS (by decide) : S 11 ≠ S 12)]
    rw [hσ3, hσ2]; simp
  · simp only [WState.sets_st, Function.update_apply, if_neg (hS (by decide) : S 12 ≠ S 16),
      if_neg (hS (by decide) : S 12 ≠ S 15), if_neg (hS (by decide) : S 12 ≠ S 14),
      if_neg (hS (by decide) : S 12 ≠ S 13)]
    rw [hσ3]; simp
  · simp only [WState.sets_st, Function.update_apply, if_neg (hS (by decide) : S 13 ≠ S 16),
      if_neg (hS (by decide) : S 13 ≠ S 15), if_neg (hS (by decide) : S 13 ≠ S 14), ↓reduceIte]
  · simp only [WState.sets_st, Function.update_apply, if_neg (hS (by decide) : S 14 ≠ S 16),
      if_neg (hS (by decide) : S 14 ≠ S 15), ↓reduceIte]
  · simp only [WState.sets_st, Function.update_apply, if_neg (hS (by decide) : S 15 ≠ S 16), ↓reduceIte]
  · simp only [WState.sets_st, Function.update_apply, ↓reduceIte]
  · intro i h10 h11 h12 h13 h14 h15 h16
    simp only [WState.sets_st, Function.update_apply, h13, h14, h15, h16, if_false]
    rw [st3 i h12 h11, s1o i h10]
  · intro i; simp only [WState.sets_sh]; exact sh3 i
  · intro k hk; simp only [WState.sets_val]; rw [val3, vout k (by omega)]

end NearCubicWires.WireExponent3_5.FinalPass.S5T
