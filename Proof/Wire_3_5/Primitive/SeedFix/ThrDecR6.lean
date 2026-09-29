import Proof.Wire_3_5.Primitive.SeedFix.ThrDecR5

/-! # THR decode front, RADIX part 6a: the data tape's head after the numbers phase

`TNums` (verified) states the streams' heads except the data tape `113`'s; the RADIX setup's entry `RsIn4` wants
that head back at `0` (`h113`). **`tC2_run2`** is `tC2_run` with the data tape's head after the carriers' lengths
(`|unaryList (take (16 + |carriers|) (hashNums ++ thrCounts))|`), the position the RADIX finisher rewinds.

Paper quantity of the main type: the THR call's counts on the data tape (P3:2543-2558). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum NearCubicWires.WireExponent3_5.PrimAsm.CapNum
open NearCubicWires.WireExponent3_5.Filters

section A2
variable (cap : ℕ) (x : ℕ)

theorem tC2_run2 (σ : WState (LNS x) LNR) (hs xs : List ℕ) (tg : ℕ) (tail : List Bool) (hhs : hs.length = 16)
    (hxs : xs.length ≤ 2) (hst : σ.st (sk x 113) = Data.unaryList (hs ++ (xs ++ [tg])) ++ tail)
    (hsh : σ.sh (sk x 113) = (Data.unaryList ((hs ++ (xs ++ [tg])).take 16)).length) (h0 : σ.val (Hb 0) = xs.length)
    (h8 : σ.val (Hb 8) = hs.getD 8 0) (zK : σ.val dK = 0) (zA : σ.val XA = 0) (zB : σ.val XB = 0)
    (zM : σ.val dMS = 0) (zT : σ.val TM = 0) (hlc : ∀ k, (hs ++ (xs ++ [tg])).getD k 0 ≤ cap) (hc2 : 2 ≤ cap) :
    ∃ τ c, WExec cap (tC2W x) σ τ c ∧ c ≤ 20 * UnaryPow.sq cap ∧ τ.val XA = xs.getD 0 0 ∧
      τ.val XB = xs.getD 1 0 ∧ τ.val dMS = hs.getD 8 0 ∧ (∀ r, r ≠ XA → r ≠ XB → r ≠ dMS → τ.val r = σ.val r) ∧
      τ.st = σ.st ∧ (∀ s', s' ≠ sk x 113 → τ.sh s' = σ.sh s') ∧ τ.cell = σ.cell ∧
      τ.sh (sk x 113) = (Data.unaryList ((hs ++ (xs ++ [tg])).take (16 + xs.length))).length := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  have nKA : dK ≠ XA := by decide
  have nKB : dK ≠ XB := by decide
  have nAB : XA ≠ XB := by decide
  have nKM : dK ≠ dMS := by decide
  have nAM : XA ≠ dMS := by decide
  have nBM : XB ≠ dMS := by decide
  have nMT : dMS ≠ TM := by decide
  have nKT : dK ≠ TM := by decide
  have nAT : XA ≠ TM := by decide
  have nBT : XB ≠ TM := by decide
  have nHK : Hb 8 ≠ dK := by decide
  have nHA : Hb 8 ≠ XA := by decide
  have nHB : Hb 8 ≠ XB := by decide
  have h8c : hs.getD 8 0 ≤ cap := by
    have := hlc 8
    rwa [List.getD_append _ _ _ _ (by omega)] at this
  have e1 := SparseNum.copy1 cap (Hb 0) dK TM (by decide) (by decide) (by decide) xs.length σ h0 zK zT (by omega)
  obtain ⟨σ1, h1⟩ : ∃ y, y = σ.setv dK xs.length := ⟨_, rfl⟩
  rw [← h1] at e1
  have g16 : (hs ++ (xs ++ [tg])).getD (16 + 0) 0 = (xs ++ [tg]).getD 0 0 := getD_hs16 hs _ hhs 0
  have g17 : (hs ++ (xs ++ [tg])).getD (16 + 1) 0 = (xs ++ [tg]).getD 1 0 := getD_hs16 hs _ hhs 1
  have hlen : (hs ++ (xs ++ [tg])).length = 16 + xs.length + 1 := by simp [hhs]; omega
  have hst1 : σ1.st (sk x 113) = Data.unaryList (hs ++ (xs ++ [tg])) ++ tail := by rw [h1]; exact hst
  have hsh1 : σ1.sh (sk x 113) = (Data.unaryList ((hs ++ (xs ++ [tg])).take 16)).length := by rw [h1]; exact hsh
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, t⟩⟩⟩
  · -- no carriers
    have eM := SparseNum.copy1 cap (Hb 8) dMS TM (by decide) (by decide) (by decide) (hs.getD 8 0) σ1
      (by rw [h1]; simp [Function.update_apply, h8, nHK, nHA, nHB]) (by rw [h1]; simp [Function.update_apply, nKM.symm, zM])
      (by rw [h1]; simp [Function.update_apply, nKT.symm, zT]) h8c
    refine ⟨_, _, WExec.seq e1 (WExec.seq (WExec.ifrF (by rw [h1]; simp) (WExec.skip _)) eM), ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · omega
    · rw [h1]; simp [Function.update_apply, nAM, nKA.symm, zA]
    · rw [h1]; simp [Function.update_apply, nBM, nKB.symm, zB]
    · simp
    · intro r a b c
      rw [WState.setv_val, Function.update_of_ne c, h1, WState.setv_val]
      by_cases hk : r = dK
      · subst hk; simp [zK]
      · rw [Function.update_of_ne hk]
    · rw [WState.setv_st, h1]; rfl
    · intro s' hs'
      rw [WState.setv_sh, h1]; rfl
    · rw [WState.setv_cell, h1]; rfl
    · rw [WState.setv_sh, h1]; simpa using hsh
  · -- one carrier
    have e2 := readItem_at cap (sk x 113) XA (hs ++ ([x0] ++ [tg])) tail 16 (by rw [hlen]; simp) 0 σ1 hst1 hsh1
      (by rw [h1]; simp [Function.update_apply, nKA.symm, zA]) (by have := hlc 16; omega)
    obtain ⟨σ2, h2⟩ : ∃ y, y = (σ1.seth (sk x 113) (Data.unaryList ((hs ++ ([x0] ++ [tg])).take (16 + 1))).length).setv
        XA (0 + (hs ++ ([x0] ++ [tg])).getD 16 0) := ⟨_, rfl⟩
    rw [← h2] at e2
    have e3 := SparseNum.dec1 cap dK 1 σ2 (by rw [h2, h1]; simp [Function.update_apply, nKA]) (by omega)
    obtain ⟨σ3, h3⟩ : ∃ y, y = σ2.setv dK (1 - 1) := ⟨_, rfl⟩
    rw [← h3] at e3
    have eM := SparseNum.copy1 cap (Hb 8) dMS TM (by decide) (by decide) (by decide) (hs.getD 8 0) σ3
      (by rw [h3, h2, h1]; simp [Function.update_apply, h8, nHK, nHA, nHB])
      (by rw [h3, h2, h1]; simp [Function.update_apply, nKM.symm, nAM.symm, zM])
      (by rw [h3, h2, h1]; simp [Function.update_apply, nKT.symm, nAT.symm, zT]) h8c
    refine ⟨_, _, WExec.seq e1 (WExec.seq (WExec.ifrT (by rw [h1]; simp) (WExec.seq e2 (WExec.seq e3
      (WExec.ifrF (by rw [h3]; simp) (WExec.skip _))))) eM), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hlc 16; omega
    · rw [WState.setv_val, Function.update_of_ne nAM, h3, WState.setv_val, Function.update_of_ne nKA.symm, h2,
        WState.setv_val, Function.update_self]
      have := g16; simp at this ⊢; omega
    · rw [WState.setv_val, Function.update_of_ne nBM, h3, WState.setv_val, Function.update_of_ne nKB.symm, h2,
        WState.setv_val, Function.update_of_ne nAB.symm, WState.seth_val, h1, WState.setv_val,
        Function.update_of_ne nKB.symm, zB]; rfl
    · simp
    · intro r a b c
      rw [WState.setv_val, Function.update_of_ne c, h3, WState.setv_val]
      by_cases hk : r = dK
      · subst hk; simp [zK]
      · rw [Function.update_of_ne hk, h2, WState.setv_val, Function.update_of_ne a, WState.seth_val, h1,
          WState.setv_val, Function.update_of_ne hk]
    · rw [WState.setv_st, h3, WState.setv_st, h2, WState.setv_st, WState.seth_st, h1]; rfl
    · intro s' hs'
      rw [WState.setv_sh, h3, WState.setv_sh, h2, WState.setv_sh, WState.seth_sh, Function.update_of_ne hs', h1]; rfl
    · rw [WState.setv_cell, h3, WState.setv_cell, h2, WState.setv_cell, WState.seth_cell, h1]; rfl
    · rw [WState.setv_sh, h3, WState.setv_sh, h2, WState.setv_sh, WState.seth_sh, Function.update_self]; simp
  · -- two carriers
    have e2 := readItem_at cap (sk x 113) XA (hs ++ ([x0, x1] ++ [tg])) tail 16 (by rw [hlen]; simp) 0 σ1 hst1 hsh1
      (by rw [h1]; simp [Function.update_apply, nKA.symm, zA]) (by have := hlc 16; omega)
    obtain ⟨σ2, h2⟩ : ∃ y, y = (σ1.seth (sk x 113) (Data.unaryList ((hs ++ ([x0, x1] ++ [tg])).take (16 + 1))).length).setv
        XA (0 + (hs ++ ([x0, x1] ++ [tg])).getD 16 0) := ⟨_, rfl⟩
    rw [← h2] at e2
    have e3 := SparseNum.dec1 cap dK 2 σ2 (by rw [h2, h1]; simp [Function.update_apply, nKA]) (by omega)
    obtain ⟨σ3, h3⟩ : ∃ y, y = σ2.setv dK (2 - 1) := ⟨_, rfl⟩
    rw [← h3] at e3
    have e4 := readItem_at cap (sk x 113) XB (hs ++ ([x0, x1] ++ [tg])) tail 17 (by rw [hlen]; simp) 0 σ3
      (by rw [h3, h2]; simpa using hst1) (by rw [h3, h2]; simp)
      (by rw [h3, h2, h1]; simp [Function.update_apply, nKB.symm, nAB.symm, zB]) (by have := hlc 17; omega)
    obtain ⟨σ4, h4⟩ : ∃ y, y = (σ3.seth (sk x 113) (Data.unaryList ((hs ++ ([x0, x1] ++ [tg])).take (17 + 1))).length).setv
        XB (0 + (hs ++ ([x0, x1] ++ [tg])).getD 17 0) := ⟨_, rfl⟩
    rw [← h4] at e4
    have e5 := SparseNum.dec1 cap dK 1 σ4 (by rw [h4, h3]; simp [Function.update_apply, nKB]) (by omega)
    obtain ⟨σ5, h5⟩ : ∃ y, y = σ4.setv dK (1 - 1) := ⟨_, rfl⟩
    rw [← h5] at e5
    have eM := SparseNum.copy1 cap (Hb 8) dMS TM (by decide) (by decide) (by decide) (hs.getD 8 0) σ5
      (by rw [h5, h4, h3, h2, h1]; simp [Function.update_apply, h8, nHK, nHA, nHB])
      (by rw [h5, h4, h3, h2, h1]; simp [Function.update_apply, nKM.symm, nAM.symm, nBM.symm, zM])
      (by rw [h5, h4, h3, h2, h1]; simp [Function.update_apply, nKT.symm, nAT.symm, nBT.symm, zT]) h8c
    refine ⟨_, _, WExec.seq e1 (WExec.seq (WExec.ifrT (by rw [h1]; simp) (WExec.seq e2 (WExec.seq e3
      (WExec.ifrT (by rw [h3]; simp) (WExec.seq e4 e5))))) eM), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hlc 16; have := hlc 17; omega
    · rw [WState.setv_val, Function.update_of_ne nAM, h5, WState.setv_val, Function.update_of_ne nKA.symm, h4,
        WState.setv_val, Function.update_of_ne nAB, WState.seth_val, h3, WState.setv_val,
        Function.update_of_ne nKA.symm, h2, WState.setv_val, Function.update_self]
      have := g16; simp at this ⊢; omega
    · rw [WState.setv_val, Function.update_of_ne nBM, h5, WState.setv_val, Function.update_of_ne nKB.symm, h4,
        WState.setv_val, Function.update_self]
      have := g17; simp at this ⊢; omega
    · simp
    · intro r a b c
      rw [WState.setv_val, Function.update_of_ne c, h5, WState.setv_val]
      by_cases hk : r = dK
      · subst hk; simp [zK]
      · rw [Function.update_of_ne hk, h4, WState.setv_val, Function.update_of_ne b, WState.seth_val, h3,
          WState.setv_val, Function.update_of_ne hk, h2, WState.setv_val, Function.update_of_ne a, WState.seth_val,
          h1, WState.setv_val, Function.update_of_ne hk]
    · rw [WState.setv_st, h5, WState.setv_st, h4, WState.setv_st, WState.seth_st, h3, WState.setv_st, h2,
        WState.setv_st, WState.seth_st, h1]; rfl
    · intro s' hs'
      rw [WState.setv_sh, h5, WState.setv_sh, h4, WState.setv_sh, WState.seth_sh, Function.update_of_ne hs', h3,
        WState.setv_sh, h2, WState.setv_sh, WState.seth_sh, Function.update_of_ne hs', h1]; rfl
    · rw [WState.setv_cell, h5, WState.setv_cell, h4, WState.setv_cell, WState.seth_cell, h3, WState.setv_cell, h2,
        WState.setv_cell, WState.seth_cell, h1]; rfl
    · rw [WState.setv_sh, h5, WState.setv_sh, h4, WState.setv_sh, WState.seth_sh, Function.update_self]; simp
  · simp at hxs

/-! ## The numbers phase with the data tape's head -/

/-- Phases A, C1, C2, run from the unit's fresh cell. -/
theorem tN1_run2 (cr fe : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (w out : List Bool) (j : ℕ)
    (mb : Bool) (codes cc : List ℕ) (tl : List Bool) (Kb : ℕ) (hw : w = Data.reqW P.n mb codes cc tl)
    (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb) (hs xs : List ℕ) (tg : ℕ) (hhs : hs.length = 16) (hxs : xs.length ≤ 2)
    (h0v : hs.getD 0 0 = xs.length) (hc1 : 2 * w.length + 2 ≤ cap)
    (hcP : 2 ^ (natBitLength P.n + 1) + 2 ^ (natBitLength codes.length + 1) + 2 ^ (natBitLength cc.length + 1) +
      Kb + P.n + codes.length + 1 ≤ cap)
    (hc3 : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap) (hcl : ∀ k, (hs ++ (xs ++ [tg])).getD k 0 ≤ cap) :
    ∃ τ c, WExec cap (tN1W x cr fe) (CellLoopD.blankCellD x w out j (Data.unaryList (hs ++ (xs ++ [tg])))) τ c ∧
      c ≤ tACost P.n codes.length cc.length Kb cr fe cap + 1 + (34 * UnaryPow.sq cap + 1 + 20 * UnaryPow.sq cap) ∧
      τ.val dN = P.n ∧ τ.val dA = codes.length ∧ τ.val dNC = cc.length ∧ τ.val LEN = w.length ∧
      τ.val (SGb 8) = P.s * (P.r / 2) ∧ τ.val (SGb 10) = fe * Nat.clog 2 (P.n + 2) ∧
      (∀ k : Fin 32, k.val < 16 → τ.val (Hb k) = hs.getD k.val 0) ∧
      τ.val XA = xs.getD 0 0 ∧ τ.val XB = xs.getD 1 0 ∧ τ.val dMS = hs.getD 8 0 ∧
      (∀ r : Fin LNR, (r.val < 250 ∨ 398 ≤ r.val) → τ.val r = 0) ∧ τ.val TM = 0 ∧ τ.val dK = 0 ∧
      τ.st = (CellLoopD.blankCellD x w out j (Data.unaryList (hs ++ (xs ++ [tg])))).st ∧
      (∀ s, s ≠ sk x 113 → τ.sh s = (CellLoopD.blankCellD x w out j (Data.unaryList (hs ++ (xs ++ [tg])))).sh s) ∧
      τ.cell = false ∧ (∀ q, τ.val q ≤ cap) ∧
      τ.sh (sk x 113) = (Data.unaryList ((hs ++ (xs ++ [tg])).take (16 + xs.length))).length := by
  set σ₀ := CellLoopD.blankCellD x w out j (Data.unaryList (hs ++ (xs ++ [tg]))) with hσ₀
  have hv0 : ∀ r, σ₀.val r = 0 := fun r => rfl
  have n0B : sk x 0 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have n01 : sk x 0 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have n1B : sk x 113 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have st0 : σ₀.st (sk x 0) = frame w := by rw [hσ₀]; simp [CellLoopD.blankCellD, blankCell, n0B]
  have sh0 : σ₀.sh (sk x 0) = 0 := by rw [hσ₀]; simp [CellLoopD.blankCellD, blankCell, n01]
  have st113 : σ₀.st (sk x 113) = Data.unaryList (hs ++ (xs ++ [tg])) ++ [] := by
    rw [hσ₀, List.append_nil]; simp [CellLoopD.blankCellD]
  have sh113 : σ₀.sh (sk x 113) = 0 := by rw [hσ₀]; simp [CellLoopD.blankCellD, blankCell, n1B]
  have hc2 : 2 ≤ cap := by omega
  obtain ⟨σA, cA, eA, cAle, aN, aA, aNC, aL, a8, a10, kA, stA, shA, clA⟩ :=
    tA_run cap x cr fe P hrP σ₀ w mb codes cc tl Kb hw hKb st0 sh0 (fun r _ _ => hv0 r) hc1 hcP hc3
  have zA : ∀ r : Fin LNR, (r.val < 250 ∨ 270 ≤ r.val) → r ≠ dN → r ≠ dA → r ≠ dNC → r ≠ LEN → σA.val r = 0 :=
    fun r h a b c d => by rw [kA r a b c d h]; exact hv0 r
  have hBA : ∀ q, σA.val q ≤ cap := wexec_le cap eA (fun q => by rw [hv0]; omega)
  have eC1 := hC1_run cap x σA (hs ++ (xs ++ [tg])) [] (by simp [hhs]) (by rw [stA]; exact st113)
    (by rw [shA]; exact sh113)
    (fun i => zA _ (by rw [Hb_val]; omega) (fne (by rw [Hb_val, rv_dN']; omega))
      (fne (by rw [Hb_val, rv_dA'']; omega)) (fne (by rw [Hb_val, rv_dNC']; omega))
      (fne (by rw [Hb_val, rv_LEN']; have := i.isLt; omega))) hcl
  set σC := hC1Out x σA (hs ++ (xs ++ [tg])) with hσC
  have kC : ∀ r : Fin LNR, (r.val < 337 ∨ 353 ≤ r.val) → σC.val r = σA.val r := fun r hr =>
    hC1Out_other x σA _ r hr
  have stC : σC.st = σ₀.st := by rw [hσC]; unfold hC1Out; simp [stA]
  have shC : σC.sh (sk x 113) = (Data.unaryList ((hs ++ (xs ++ [tg])).take 16)).length := by
    rw [hσC]; unfold hC1Out; simp
  have shCo : ∀ s, s ≠ sk x 113 → σC.sh s = σA.sh s := fun s hs => by
    rw [hσC]; unfold hC1Out; simp [Function.update_apply, hs]
  have clC : σC.cell = σ₀.cell := by rw [hσC]; unfold hC1Out; simp [clA]
  have hBC : ∀ q, σC.val q ≤ cap := wexec_le cap eC1 hBA
  have cb : ∀ k : Fin 32, k.val < 16 → σC.val (Hb k) = hs.getD k.val 0 := fun k hk => by
    rw [hσC, hC1Out_hb x σA _ k hk, List.getD_append _ _ _ _ (by omega)]; simp
  obtain ⟨τ, c2, eC2, c2le, tXA, tXB, tMS, kC2, stC2, shC2, clC2, sh113⟩ := tC2_run2 cap x σC hs xs tg [] hhs hxs
    (by rw [stC]; exact st113) shC (by rw [cb 0 (by decide)]; exact h0v) (cb 8 (by decide))
    (by rw [kC _ (by rw [rv_dK']; omega)]; exact zA _ (by rw [rv_dK']; omega) (by decide) (by decide) (by decide) (by decide))
    (by rw [kC _ (by rw [rv_XA']; omega)]; exact zA _ (by rw [rv_XA']; omega) (by decide) (by decide) (by decide) (by decide))
    (by rw [kC _ (by rw [rv_XB']; omega)]; exact zA _ (by rw [rv_XB']; omega) (by decide) (by decide) (by decide) (by decide))
    (by rw [kC _ (by rw [rv_dMS']; omega)]; exact zA _ (by rw [rv_dMS']; omega) (by decide) (by decide) (by decide) (by decide))
    (by rw [kC _ (by rw [rv_TM']; omega)]; exact zA _ (by rw [rv_TM']; omega) (by decide) (by decide) (by decide) (by decide))
    hcl hc2
  have nX : ∀ r : Fin LNR, r ≠ XA → r ≠ XB → r ≠ dMS → τ.val r = σC.val r := kC2
  refine ⟨τ, _, WExec.seq eA (WExec.seq eC1 eC2), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, tXA, tXB, tMS, ?_, ?_, ?_, ?_, ?_, ?_,
    wexec_le cap eC2 hBC, sh113⟩
  · omega
  · rw [nX _ (by decide) (by decide) (by decide), kC _ (by rw [rv_dN']; omega)]; exact aN
  · rw [nX _ (by decide) (by decide) (by decide), kC _ (by rw [rv_dA'']; omega)]; exact aA
  · rw [nX _ (by decide) (by decide) (by decide), kC _ (by rw [rv_dNC']; omega)]; exact aNC
  · rw [nX _ (by decide) (by decide) (by decide), kC _ (by rw [rv_LEN']; omega)]; exact aL
  · rw [nX _ (by decide) (by decide) (by decide), kC _ (by rw [SGb_val]; omega)]; exact a8
  · rw [nX _ (by decide) (by decide) (by decide), kC _ (by rw [SGb_val]; omega)]; exact a10
  · intro k hk
    have n1 : Hb k ≠ XA := fne (by rw [Hb_val, rv_XA']; omega)
    have n2 : Hb k ≠ XB := fne (by rw [Hb_val, rv_XB']; omega)
    have n3 : Hb k ≠ dMS := fne (by rw [Hb_val, rv_dMS']; omega)
    rw [nX _ n1 n2 n3]; exact cb k hk
  · intro r hr
    have n1 : r ≠ XA := fne (by rw [rv_XA']; omega)
    have n2 : r ≠ XB := fne (by rw [rv_XB']; omega)
    have n3 : r ≠ dMS := fne (by rw [rv_dMS']; omega)
    rw [nX _ n1 n2 n3, kC _ (by omega)]
    exact zA _ (by omega) (fne (by rw [rv_dN']; omega)) (fne (by rw [rv_dA'']; omega))
      (fne (by rw [rv_dNC']; omega)) (fne (by rw [rv_LEN']; omega))
  · rw [nX _ (by decide) (by decide) (by decide), kC _ (by rw [rv_TM']; omega)]
    exact zA _ (by rw [rv_TM']; omega) (by decide) (by decide) (by decide) (by decide)
  · rw [nX _ (by decide) (by decide) (by decide), kC _ (by rw [rv_dK']; omega)]
    exact zA _ (by rw [rv_dK']; omega) (by decide) (by decide) (by decide) (by decide)
  · rw [stC2, stC]
  · intro s hs
    rw [shC2 s hs, shCo s hs, shA]
  · rw [clC2, clC]; rfl

/-- **The THR decode's numbers, run** from the unit's fresh cell to `TNums`. -/
theorem tN_run2 (cr fe : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (w out : List Bool) (j : ℕ)
    (mb : Bool) (codes cc : List ℕ) (tl : List Bool) (Kb : ℕ) (hw : w = Data.reqW P.n mb codes cc tl)
    (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb) (hs xs : List ℕ) (tg : ℕ) (hhs : hs.length = 16) (hxs : xs.length ≤ 2)
    (h0v : hs.getD 0 0 = xs.length) (FP : GapParams) (hPc : FP.cap = hs.getD 1 0)
    (hPl : FP.len = 2 * (P.n + 1) ^ 26) (hPe : FP.errExp = fe * Nat.clog 2 (P.n + 2)) (hPc1 : 1 ≤ FP.cap)
    (hN : TNeed cap w P.n codes cc Kb cr fe hs xs tg FP (P.s * (P.r / 2))) :
    ∃ τ c, WExec cap (tNW x cr fe) (CellLoopD.blankCellD x w out j (Data.unaryList (hs ++ (xs ++ [tg])))) τ c ∧
      c ≤ tNCost P.n codes.length cc.length Kb cr fe cap ∧
      TNums x cap τ w out j (Data.unaryList (hs ++ (xs ++ [tg]))) P.n codes.length cc.length (P.s * (P.r / 2)) hs xs
        FP ((xs.length + 1) * 3 + 2) (2 ^ (2 * (P.s * (P.r / 2)))) (hs.getD 6 0) (hs.getD 2 0)
        (2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2)) ∧
      τ.sh (sk x 113) = (Data.unaryList ((hs ++ (xs ++ [tg])).take (16 + xs.length))).length := by
  obtain ⟨τ1, c1, e1, c1le, aN, aA, aNC, aL, a8, a10, ab, aXA, aXB, aMS, az, aT, aK, ast, ash, acl, abd, a113⟩ :=
    tN1_run2 cap x cr fe P hrP w out j mb codes cc tl Kb hw hKb hs xs tg hhs hxs h0v hN.c1 hN.cP hN.c3 hN.cl
  have zG1 : ∀ i : Fin 64, τ1.val (G i) = 0 := fun i => az _ (Or.inr (by rw [G_val]; omega))
  obtain ⟨τ, e2, g0, g1, g2, g55, g53, g52, g41, g56, g32, k2, st2, sh2, cl2⟩ :=
    tN2_run cap x τ1 xs.length P.n (P.s * (P.r / 2)) (fe * Nat.clog 2 (P.n + 2)) (hs.getD 2 0) (hs.getD 6 0) FP
      (by rw [ab 0 (by decide)]; exact h0v) (by rw [ab 1 (by decide), hPc]; rfl) (ab 2 (by decide)) (ab 6 (by decide))
      aN a8 a10 zG1 aT hPl hPe hPc1 hN.cD hN.cG1 hN.cG2 hN.cG3 hN.cG4 hN.cG5 hN.cEU
      hN.ckh hN.cv hN.cm1 hN.cm2 hN.cm3 hN.cm4
  have nG : ∀ r : Fin LNR, r.val < 408 → ∀ i : Fin 64, r ≠ G i := fun r h i e => by rw [e, G_val] at h; omega
  have kv : ∀ r : Fin LNR, r.val < 408 → τ.val r = τ1.val r := fun r h => k2 r (nG r h)
  refine ⟨τ, _, WExec.seq e1 e2, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, g0, g1, g2, g55, g53, g52, g41,
    g56, g32, ?_, ?_, ?_, ?_, ?_, wexec_le cap e2 abd⟩, by rw [sh2]; exact a113⟩
  · unfold tNCost; omega
  · rw [st2, ast]
  · intro s hs; rw [sh2, ash s hs]
  · rw [cl2, acl]
  · rw [kv _ (by rw [rv_dN']; omega)]; exact aN
  · rw [kv _ (by rw [rv_dA'']; omega)]; exact aA
  · rw [kv _ (by rw [rv_dNC']; omega)]; exact aNC
  · rw [kv _ (by rw [rv_LEN']; omega)]; exact aL
  · rw [kv _ (by rw [SGb_val]; omega)]; exact a8
  · intro k hk; rw [kv _ (by rw [Hb_val]; omega)]; exact ab k hk
  · rw [kv _ (by rw [rv_XA']; omega)]; exact aXA
  · rw [kv _ (by rw [rv_XB']; omega)]; exact aXB
  · rw [kv _ (by rw [rv_dMS']; omega)]; exact aMS
  · intro k
    rw [k2 _ (fun i => HG i k)]
    exact az _ (Or.inr (by rw [H_val]; omega))
  · intro q hq; rw [kv _ (by omega)]; exact az _ (Or.inl hq)
  · intro q h1 h2; rw [kv _ h2]; exact az _ (Or.inr h1)
  · rw [kv _ (by rw [rv_TM']; omega)]; exact aT
  · rw [kv _ (by rw [rv_dK']; omega)]; exact aK

end A2

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
