import Proof.Wire_3_5.FinalPass.S5TTailA

/-! # S5-THR, part 19: THR slots 14 and 15 (P3:2150-2157, 2596-2599)

The tail's second half on the named layout of `tailA_spec`: stage 4's table builder renamed onto the streams `17`
(output), `12`, `11`, `9`, `13 … 16` and the registers `19 … 34` (`build_lift`), then THR slot `15`
(`slot15W`: the tuple size from register `39`, W6's ports `3`, `8`, `9`).

* `tailS`, `tailR` (the renamings), `tailBW`, **`tailB_spec`**; `tailW` = `tailAW ; tailBW`, **`tail_spec`**.

Paper quantities of the main type: THR slot `14` = stage 4's table word `levelWord M J W (rowsOf D M)` at the fixed
hash's data `D = dataBits MP s`; THR slot `15` = S2's numbers `unaryList [a, |𝒢|, τ₀, |occs|]`. -/

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

/-- The builder's streams among the named ones: `O, WIN, SEED, P, X, ACC, NEW, ST`. -/
def tailIx : Fin 8 → Fin 19 := ![17, 12, 11, 9, 13, 14, 15, 16]

theorem tailIx_inj : Function.Injective tailIx := by decide

/-- The builder's streams on the layout. -/
def tailS (S : Fin 19 ↪ Fin (ns + 1)) (i : Fin 8) : Fin (ns + 1) := S (tailIx i)

/-- The builder's registers on the layout: named registers `19 … 34`. -/
def tailR (Rg : Fin 40 ↪ Fin nr) (r : Fin 16) : Fin nr := Rg ⟨19 + r.val, by omega⟩

theorem tailS_inj (S : Fin 19 ↪ Fin (ns + 1)) : Function.Injective (tailS S) :=
  fun _ _ h => tailIx_inj (S.injective h)

theorem tailR_inj (Rg : Fin 40 ↪ Fin nr) : Function.Injective (tailR Rg) := fun a b h => by
  have := congrArg Fin.val (Rg.injective h)
  exact Fin.ext (by simp at this; omega)

/-- **The tail's second half**: the table builder renamed, then THR slot `15`. -/
def tailBW (S : Fin 19 ↪ Fin (ns + 1)) (Rg : Fin 40 ↪ Fin nr) : WM ns nr :=
  .seq (WM.liftW (tailS S) (tailR Rg) Hash4.build)
    (slot15W (S 18) (S 2) (S 3) (S 4) (Rg 39) (Rg 35) (Rg 36) (Rg 37) (Rg 38))

theorem tailB_spec (S : Fin 19 ↪ Fin (ns + 1)) (Rg : Fin 40 ↪ Fin nr) (ω : WState ns nr) (p ℓ M J : ℕ)
    (Wf : ℕ → ℕ) (all : List ℕ) (a x y : ℕ) (hℓ : 1 ≤ ℓ)
    (hO : ω.st (S 17) = []) (hW : ω.st (S 12) = Hash4.winWord M M J Wf) (hSd : ω.st (S 11) = Hash4.seedWord ℓ all)
    (hP : ω.st (S 9) = frame (binary ℓ p)) (hX : ω.st (S 13) = frame (binary ℓ 0))
    (hA : ω.st (S 14) = frame (binary ℓ 0)) (hN : ω.st (S 15) = frame (binary ℓ 0))
    (hT : ω.st (S 16) = frame (binary ℓ 0)) (hO15 : ω.st (S 18) = [])
    (h3 : ω.st (S 2) = List.replicate x true) (h8 : ω.st (S 3) = List.replicate y true)
    (h9 : ω.st (S 4) = List.replicate M true)
    (hsh : ∀ i, ω.sh i = 0) (hv : ∀ k : Fin 40, 19 ≤ k.val → k.val < 39 → ω.val (Rg k) = 0) (ha : ω.val (Rg 39) = a)
    (hcapS : (Hash4.seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap) (hcapW : (Hash4.winWord M M J Wf).length ≤ cap)
    (hcapO : (ListEval.levelWord M J Wf (Hash4.rowF p ℓ M M all)).length + 1 ≤ cap) (hM : M ≤ cap) (hJ : J ≤ cap)
    (hc5 : a + x + y + M + 4 ≤ cap) :
    ∃ τ, WExec cap (tailBW S Rg) ω τ
        (Hash4.buildCost M M J (Hash4.levelCost ℓ M M all.length J (Hash4.winWord M M J Wf).length
          (Hash4.winWord M M J Wf).length) (Hash4.winWord M M J Wf).length
          (ListEval.levelWord M J Wf (Hash4.rowF p ℓ M M all)).length + 1 + (40 * (a + x + y + M) + 120)) ∧
      τ.st (S 17) = ListEval.levelWord M J Wf (Hash4.rowF p ℓ M M all) ∧
      τ.st (S 18) = PrimAsm.Data.unaryList [a, x, y, M] ∧
      (∀ i, (∀ k : Fin 8, S (tailIx k) ≠ i) → i ≠ S 18 → τ.st i = ω.st i) := by
  have hS : ∀ {i j : Fin 19}, i ≠ j → S i ≠ S j := fun h => S.injective.ne h
  have hR : ∀ {i j : Fin 40}, i ≠ j → Rg i ≠ Rg j := fun h => Rg.injective.ne h
  have hout : ∀ (k : Fin 19), (∀ i : Fin 8, tailIx i ≠ k) → ∀ i : Fin 8, tailS S i ≠ S k :=
    fun k hk i h => hk i (S.injective h)
  obtain ⟨ω1, e1, o1, so1, vo1⟩ := build_lift cap (tailS S) (tailS_inj S) (tailR Rg) (tailR_inj Rg) ω p ℓ M J Wf all
    hℓ hO hW hSd hP hX hA hN hT (fun i => hsh _) (fun r => hv _ (by simp) (by simp; omega)) hcapS hcapW hcapO hM hJ
  have st1 : ∀ k : Fin 19, (∀ i : Fin 8, tailIx i ≠ k) → ω1.st (S k) = ω.st (S k) :=
    fun k hk => (so1 (S k) (hout k hk)).2
  have sh1 : ∀ k : Fin 19, (∀ i : Fin 8, tailIx i ≠ k) → ω1.sh (S k) = 0 :=
    fun k hk => by rw [(so1 (S k) (hout k hk)).1, hsh]
  have vl1 : ∀ k : Fin 40, (k.val < 19 ∨ 35 ≤ k.val) → ω1.val (Rg k) = ω.val (Rg k) := fun k hk =>
    vo1 _ (fun r h => by
      have := congrArg Fin.val (Rg.injective h)
      simp at this; omega)
  have e2 := slot15W_spec cap (S 18) (S 2) (S 3) (S 4) (hS (by decide)) (hS (by decide)) (hS (by decide))
    (Rg 39) (Rg 35) (Rg 36) (Rg 37) (Rg 38) (hR (by decide)) (hR (by decide)) (hR (by decide)) (hR (by decide))
    (hR (by decide)) ω1 a x y M (by rw [st1 18 (by decide), hO15]) (sh1 18 (by decide))
    (by rw [vl1 39 (by decide), ha]) (by rw [vl1 36 (by decide), hv 36 (by decide) (by decide)])
    (by rw [vl1 37 (by decide), hv 37 (by decide) (by decide)])
    (by rw [vl1 35 (by decide), hv 35 (by decide) (by decide)])
    (by rw [vl1 38 (by decide), hv 38 (by decide) (by decide)])
    (by rw [st1 2 (by decide), h3]) (sh1 2 (by decide)) (by rw [st1 3 (by decide), h8]) (sh1 3 (by decide))
    (by rw [st1 4 (by decide), h9]) (sh1 4 (by decide)) hc5
  refine ⟨_, WExec.seq e1 e2, ?_, ?_, ?_⟩
  · simp only [wSt, WState.setv_st, appW_st, Function.update_apply, if_neg (hS (by decide) : S 17 ≠ S 18)]
    exact o1
  · simp only [wSt, WState.setv_st, appW_st, Function.update_apply, ↓reduceIte]
    rw [st1 18 (by decide), hO15, List.nil_append]
  · intro i hi h18
    simp only [wSt, WState.setv_st, appW_st, Function.update_apply, if_neg h18]
    exact (so1 i (fun k h => hi k h)).2

/-- **The THR half's tail**: the hash's inputs for stage 4, then THR slots `14` and `15`. -/
def tailW (S : Fin 19 ↪ Fin (ns + 1)) (Rg : Fin 40 ↪ Fin nr) : WM ns nr := .seq (tailAW S Rg) (tailBW S Rg)

/-- The tail's cost bound. -/
def tailCost (m t ℓ w M J nall o a x y : ℕ) : ℕ :=
  tailACost m t ℓ w + 1 + (Hash4.buildCost M M J (Hash4.levelCost ℓ M M nall J w w) w o + 1 +
    (40 * (a + x + y + M) + 120))

theorem one_le_ell0 (MP : MajorantParams) : 1 ≤ MP.ell0 := by
  unfold MajorantParams.ell0; omega

/-- **The tail's run**: THR slot `14` is stage 4's table of the fixed hash at the seed `s` (`rowF_eq`), THR slot `15`
is `unaryList [a, x, y, M]`; every stream outside the tail's own (`9 … 18`) is kept. -/
theorem tail_spec (S : Fin 19 ↪ Fin (ns + 1)) (Rg : Fin 40 ↪ Fin nr) (σ : WState ns nr) (MP : MajorantParams)
    (s : Fin (2 * MP.t * MP.ell0) → Bool) (pre : List Bool) (a x y : ℕ)
    (hI : σ.st (S 0) = frame (pre ++ frame (List.ofFn s)))
    (hT : σ.st (S 1) = sent ((pre ++ frame (List.ofFn s)).length + 1))
    (h3 : σ.st (S 2) = List.replicate x true) (h8 : σ.st (S 3) = List.replicate y true)
    (h9 : σ.st (S 4) = List.replicate MP.M true) (h12 : σ.st (S 5) = List.replicate MP.J true)
    (h13 : σ.st (S 6) = List.replicate MP.t true) (h15 : σ.st (S 7) = List.replicate MP.ell0 true)
    (h18 : σ.st (S 8) = (ListEval.levels MP.J).flatMap (Hash4.winRec MP.J MP.W))
    (h19 : σ.st (S 9) = frame (binary MP.ell0 MP.refMod))
    (hbl : ∀ k : Fin 19, 10 ≤ k.val → σ.st (S k) = []) (hsh : ∀ i, σ.sh i = 0)
    (hz : ∀ k : Fin 40, k.val < 39 → σ.val (Rg k) = 0) (ha : σ.val (Rg 39) = a)
    (hc1 : 100 * ((pre ++ frame (List.ofFn s)).length + 1) + 10 * (MP.t + MP.ell0) ≤ cap)
    (hc2 : 2 * MP.t * (2 * MP.ell0 + 2) + 1 + MP.ell0 + MP.t ≤ cap)
    (hc3 : (Hash4.winWord MP.M MP.M MP.J MP.W).length ≤ cap) (hc4 : 2 * MP.ell0 + 2 ≤ cap)
    (hcapS : (Hash4.seedWord MP.ell0 (Hash4.coefsRev (MajorantBits.coefVal MP s))).length + 2 * MP.ell0 + 2 ≤ cap)
    (hcapO : (ListEval.levelWord MP.M MP.J MP.W (ListEval.rowsOf (MajorantBits.dataBits MP s) MP.M)).length + 1 ≤
      cap) (hM : MP.M ≤ cap) (hJ : MP.J ≤ cap) (hc5 : a + x + y + MP.M + 4 ≤ cap) :
    ∃ τ c, WExec cap (tailW S Rg) σ τ c ∧
      c ≤ tailCost (pre ++ frame (List.ofFn s)).length MP.t MP.ell0 (Hash4.winWord MP.M MP.M MP.J MP.W).length MP.M
        MP.J (Hash4.coefsRev (MajorantBits.coefVal MP s)).length
        (ListEval.levelWord MP.M MP.J MP.W (ListEval.rowsOf (MajorantBits.dataBits MP s) MP.M)).length a x y ∧
      τ.st (S 17) = ListEval.levelWord MP.M MP.J MP.W (ListEval.rowsOf (MajorantBits.dataBits MP s) MP.M) ∧
      τ.st (S 18) = PrimAsm.Data.unaryList [a, x, y, MP.M] ∧
      (∀ i, (∀ k : Fin 19, 9 ≤ k.val → S k ≠ i) → τ.st i = σ.st i) := by
  have hS : ∀ {i j : Fin 19}, i ≠ j → S i ≠ S j := fun h => S.injective.ne h
  obtain ⟨τA, cA, eA, hcA, sA11, sA12, sA13, sA14, sA15, sA16, sAo, shA, vA⟩ := tailA_spec cap S Rg σ MP s pre hI hT
    h9 h12 h13 h15 h18 hbl hsh (fun k hk => hz k (by omega)) hc1 hc2 hc3 hc4
  have keep : ∀ k : Fin 19, (k.val < 10 ∨ 17 ≤ k.val) → τA.st (S k) = σ.st (S k) := fun k hk =>
    sAo _ (hS (by intro e; subst e; simp at hk)) (hS (by intro e; subst e; simp at hk))
      (hS (by intro e; subst e; simp at hk)) (hS (by intro e; subst e; simp at hk))
      (hS (by intro e; subst e; simp at hk)) (hS (by intro e; subst e; simp at hk))
      (hS (by intro e; subst e; simp at hk))
  have hrow := Hash4.rowF_eq MP s MP.M
  obtain ⟨τ, eB, sB17, sB18, sBo⟩ := tailB_spec cap S Rg τA MP.refMod MP.ell0 MP.M MP.J MP.W
    (Hash4.coefsRev (MajorantBits.coefVal MP s)) a x y (one_le_ell0 MP)
    (by rw [keep 17 (by decide), hbl 17 (by decide)]) sA12 sA11 (by rw [keep 9 (by decide), h19]) sA13 sA14 sA15 sA16
    (by rw [keep 18 (by decide), hbl 18 (by decide)]) (by rw [keep 2 (by decide), h3]) (by rw [keep 3 (by decide), h8])
    (by rw [keep 4 (by decide), h9]) shA
    (fun k h1 h2 => by rw [vA k h1, hz k (by omega)]) (by rw [vA 39 (by decide), ha]) hcapS hc3
    (by rw [hrow]; exact hcapO) hM hJ hc5
  refine ⟨τ, _, WExec.seq eA eB, ?_, by rw [sB17, hrow], sB18, ?_⟩
  · unfold tailCost; rw [hrow]; omega
  · intro i hi
    rw [sBo i (fun k h => hi (tailIx k) (by fin_cases k <;> decide) h) (fun h => hi 18 (by decide) h.symm)]
    exact sAo i (fun h => hi 10 (by decide) h.symm) (fun h => hi 11 (by decide) h.symm) (fun h => hi 12 (by decide) h.symm)
      (fun h => hi 13 (by decide) h.symm) (fun h => hi 14 (by decide) h.symm) (fun h => hi 15 (by decide) h.symm)
      (fun h => hi 16 (by decide) h.symm)

end NearCubicWires.WireExponent3_5.FinalPass.S5T
