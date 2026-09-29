import Proof.Wire_3_5.FinalPass.SymF2
import Proof.Wire_3_5.FinalPass.TabDec3
import Proof.Wire_3_5.Primitive.Writers.PopSetupIface

/-! # SWf (the SYM words writer's flat tables), part 3: a unit's decode to the POP setup's entry

Unit `j` of the flat tables writer builds the flat table of list seed `j` (the enumeration `Enum.flatSeedEquiv`) at
one population length `L`. Its request is the empty THR tuple's request word with the unit numbers as its tail,
`reqT n M B err L 0 K` (S4's tables writer's word, `TabW.reqT`), `K = |FlatSeed|`. **`decWP`**, from the loop's
blank cell (`CellLoopD.blankCellD`): the request's numbers read straight into the POP entry bank (`TabW.parseW`
at `RgP`: `M, B, errExp, L` into `ppM, ppB, ppErr, ppL`), the counter counted and rewound (`cntK`), the seed's test
`K − j` (`cmpD`), the seed `j` moved into `ppSeed` when `j < K`, the test into `ppOff` (the POP row's offset, which
the table stages keep in `Xe Pe 3` for the emission). **`dec_specP`**: the decode reaches `PopSetup.PopIn` at the
seed `if j < K then j else 0`, sign `0`, target `0`, `r4 = G = 0`, `off = K − j`, within `40·|w| + 40·j + 400`.

Paper quantity of the main type: the POP setup's entry for list seed `j` of the flat list `(M, B, errExp)` at
population length `L` (list:flatten P3:1491-1498, 1508-1520). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimAsm.PopSetup

variable (cap x : ℕ)

/-- The parse's registers: scratch `300 … 302`, then `ppM, ppB, ppErr, ppL`, scratch `303`, the seed count `310`. -/
def RgP : Fin 9 ↪ Fin LNR :=
  ⟨![⟨300, by decide⟩, ⟨301, by decide⟩, ⟨302, by decide⟩, ⟨400, by decide⟩, ⟨401, by decide⟩, ⟨402, by decide⟩,
    ⟨409, by decide⟩, ⟨303, by decide⟩, ⟨310, by decide⟩], by decide⟩

def pK : Fin LNR := ⟨310, by decide⟩
def pJa : Fin LNR := ⟨311, by decide⟩
def pJb : Fin LNR := ⟨312, by decide⟩
def pS : Fin LNR := ⟨313, by decide⟩

theorem RgP_val (k : Fin 9) : (RgP k).val = (![300, 301, 302, 400, 401, 402, 409, 303, 310] : Fin 9 → ℕ) k := by
  fin_cases k <;> rfl

theorem notRgP (q : Fin LNR) (h : q.val ≠ 300 ∧ q.val ≠ 301 ∧ q.val ≠ 302 ∧ q.val ≠ 400 ∧ q.val ≠ 401 ∧
    q.val ≠ 402 ∧ q.val ≠ 409 ∧ q.val ≠ 303 ∧ q.val ≠ 310) : ∀ k, q ≠ RgP k := fun k e => by
  have := RgP_val k
  rw [← e] at this
  fin_cases k <;> simp at this <;> omega

/-- **A unit's decode.** -/
def decWP : WM (LNS x) LNR :=
  .seq (TabW.parseW x RgP) (.seq (TabW.cntK (sk x 2) pJa pJb) (.seq (WM.rewind (sk x 2) pJb)
    (.seq (TabW.cmpD pJa pK pS) (.seq (.ifr pK (WM.move pS ppSeed) .skip) (WM.move pK ppOff)))))

/-- The decode's cost bound. -/
def decBoundP (lw j : ℕ) : ℕ := 40 * lw + 40 * j + 400

theorem dec_specP (n M B err L K j : ℕ) (w out u : List Bool) (hw : w = TabW.reqT n M B err L 0 K)
    (hc : 2 * w.length + 2 ≤ cap) (hj : j + 1 ≤ cap) :
    ∃ (σD : WState (LNS x) LNR) (m : ℕ), WExec cap (decWP x) (blankCellD x w out j u) σD m ∧
      m ≤ decBoundP w.length j ∧
      PopIn x σD w out j u M B err (if j < K then j else 0) 0 0 0 0 (K - j) L := by
  set σ0 := blankCellD x w out j u with hσ0
  have n01 := TabW.skn x 0 1 (by decide)
  have n02 := TabW.skn x 0 2 (by decide)
  have n12 := TabW.skn x 1 2 (by decide)
  have n0D := TabW.skn x 0 113 (by decide)
  have n1D := TabW.skn x 1 113 (by decide)
  have n2D := TabW.skn x 2 113 (by decide)
  have st0 : ∀ i, σ0.st i = if i = sk x 113 then u else (blankCell x w out j).st i := fun i => by
    rw [hσ0]; unfold blankCellD; simp only [WState.sets_st, Function.update_apply]
  have v0 : ∀ q, σ0.val q = 0 := fun q => by rw [hσ0]; rfl
  have sh0 : ∀ i, σ0.sh i = if i = sk x 1 then out.length else 0 := fun i => by rw [hσ0]; rfl
  have cl0 : σ0.cell = false := by rw [hσ0]; rfl
  have hlw : M + B + err + L + 0 + K ≤ w.length := by
    have := congrArg List.length (TabW.reqT_eq n M B err L 0 K)
    rw [← hw] at this
    rw [this]
    simp [Data.unaryList]
    omega
  -- the request's numbers
  obtain ⟨σA, mA, eA, cA, sA, hA, lA, aM, aB, aE, aL, -, aK, aO, -, -⟩ := TabW.parse_spec cap x RgP n M B err L 0
    K σ0 (by rw [st0, if_neg n0D, ← hw]; simp [blankCell]) (by rw [sh0, if_neg n01]) (fun k => v0 _)
    (by rw [← hw]; exact hc)
  have aZ : ∀ q : Fin LNR, (q.val ≠ 300 ∧ q.val ≠ 301 ∧ q.val ≠ 302 ∧ q.val ≠ 400 ∧ q.val ≠ 401 ∧
      q.val ≠ 402 ∧ q.val ≠ 409 ∧ q.val ≠ 303 ∧ q.val ≠ 310) → σA.val q = 0 := fun q hq => by
    rw [aO q (notRgP q hq), v0]
  have aK' : σA.val pK = K := aK
  -- the counter
  have eB1 := TabW.cntK_spec cap (sk x 2) pJa pJb (by decide) j (by omega) j 0 σA (by omega)
    (by rw [sA, st0, if_neg n2D]; simp [blankCell, n02.symm, n12.symm])
    (by rw [hA, sh0, if_neg n12.symm]) (by rw [aZ pJa (by decide)]; omega)
    (by rw [aZ pJb (by decide)]; omega)
  obtain ⟨σB1, hB1⟩ : ∃ y : WState (LNS x) LNR, y = ((σA.seth (sk x 2) j).setv pJa (σA.val pJa + j)).setv pJb
      (σA.val pJb + j) := ⟨_, rfl⟩
  rw [← hB1] at eB1
  have eB2 := wrewind_spec cap (sk x 2) pJb j σB1 (by rw [hB1]; simp [aZ pJb (by decide)])
    (by rw [hB1]; simp [aZ pJb (by decide)]; omega)
  obtain ⟨σB2, hB2⟩ : ∃ y : WState (LNS x) LNR, y = (σB1.setv pJb 0).seth (sk x 2) (σB1.sh (sk x 2) - j) :=
    ⟨_, rfl⟩
  rw [← hB2] at eB2
  have bB2v : ∀ q, q ≠ pJa → q ≠ pJb → σB2.val q = σA.val q := fun q a b => by
    rw [hB2, hB1]; simp [Function.update_of_ne a, Function.update_of_ne b]
  have bB2a : σB2.val pJa = j := by
    rw [hB2, hB1]; simp [Function.update_of_ne (by decide : pJa ≠ pJb), aZ pJa (by decide)]
  have bB2st : σB2.st = σA.st := by rw [hB2, hB1]; rfl
  have bB2sh : σB2.sh = σA.sh := by
    funext i
    rw [hB2, hB1]
    by_cases hi : i = sk x 2
    · rw [hi]; simp [hA, sh0, n12.symm]
    · simp [Function.update_of_ne hi]
  have bB2c : σB2.cell = σA.cell := by rw [hB2, hB1]; rfl
  -- the seed's test
  have eB3 := TabW.cmpD_spec cap pJa pK pS (by decide) (by decide) (by decide) j σB2 bB2a (by omega)
    (by rw [bB2v pK (by decide) (by decide), aK']; omega)
    (by rw [bB2v pS (by decide) (by decide), aZ pS (by decide)]; omega)
  obtain ⟨σB3, hB3⟩ : ∃ y : WState (LNS x) LNR, y = ((σB2.setv pJa 0).setv pK (σB2.val pK - j)).setv pS
      (σB2.val pS + j) := ⟨_, rfl⟩
  rw [← hB3] at eB3
  have b3K : σB3.val pK = K - j := by
    rw [hB3, wsetv_val_ne _ _ (by decide : pK ≠ pS), wsetv_val_self, bB2v pK (by decide) (by decide), aK']
  have b3S : σB3.val pS = j := by
    rw [hB3, wsetv_val_self, bB2v pS (by decide) (by decide), aZ pS (by decide), Nat.zero_add]
  have b3v : ∀ q, q ≠ pJa → q ≠ pJb → q ≠ pK → q ≠ pS → σB3.val q = σA.val q := fun q a b c d => by
    rw [hB3]
    simp [Function.update_of_ne a, Function.update_of_ne c, Function.update_of_ne d, bB2v q a b]
  have b3st : σB3.st = σA.st := by rw [hB3, bB2st.symm]; rfl
  have b3sh : σB3.sh = σA.sh := by rw [hB3, bB2sh.symm]; rfl
  have b3c : σB3.cell = σA.cell := by rw [hB3, bB2c.symm]; rfl
  -- the seed
  obtain ⟨σF, mF, eF, bF, fSd, fK, fv, fst, fsh, fcl⟩ : ∃ (σF : WState (LNS x) LNR) (mF : ℕ),
      WExec cap (.ifr pK (WM.move pS ppSeed) .skip) σB3 σF mF ∧ mF ≤ 7 * j + 2 ∧
      σF.val ppSeed = (if j < K then j else 0) ∧ σF.val pK = K - j ∧
      (∀ q, q ≠ pS → q ≠ ppSeed → σF.val q = σB3.val q) ∧ σF.st = σB3.st ∧ σF.sh = σB3.sh ∧
      σF.cell = σB3.cell := by
    have s0 : σB3.val ppSeed = 0 := by
      rw [b3v ppSeed (by decide) (by decide) (by decide) (by decide), aZ ppSeed (by decide)]
    by_cases hjK : j < K
    · have e := wmove_spec cap pS ppSeed (by decide) j σB3 b3S (by rw [b3S]; omega) (by rw [s0, b3S]; omega)
      refine ⟨_, _, WExec.ifrT (by rw [b3K]; omega) e, by omega, ?_, ?_, ?_, rfl, rfl, rfl⟩
      · simp [hjK, s0, b3S]
      · rw [wsetv_val_ne _ _ (by decide : pK ≠ ppSeed), wsetv_val_ne _ _ (by decide : pK ≠ pS), b3K]
      · intro q a b
        rw [wsetv_val_ne _ _ b, wsetv_val_ne _ _ a]
    · refine ⟨σB3, _, WExec.ifrF (by rw [b3K]; omega) (WExec.skip σB3), by omega, by simp [hjK, s0], b3K,
        fun _ _ _ => rfl, rfl, rfl, rfl⟩
  -- the test into the offset
  have o0 : σF.val ppOff = 0 := by
    rw [fv ppOff (by decide) (by decide), b3v ppOff (by decide) (by decide) (by decide) (by decide),
      aZ ppOff (by decide)]
  have eG := wmove_spec cap pK ppOff (by decide) (K - j) σF fK (by rw [fK]; omega) (by rw [o0, fK]; omega)
  set σD := (σF.setv pK 0).setv ppOff (σF.val ppOff + σF.val pK) with hσD
  have dv : ∀ q, q ≠ pJa → q ≠ pJb → q ≠ pK → q ≠ pS → q ≠ ppSeed → q ≠ ppOff → σD.val q = σA.val q :=
    fun q a b c d e f => by
      rw [hσD, wsetv_val_ne _ _ f, wsetv_val_ne _ _ c, fv q d e, b3v q a b c d]
  have dst : σD.st = σ0.st := by rw [hσD]; simp only [WState.setv_st]; rw [fst, b3st, sA]
  have dsh : σD.sh = σ0.sh := by rw [hσD]; simp only [WState.setv_sh]; rw [fsh, b3sh, hA]
  have dcl : σD.cell = false := by rw [hσD]; simp only [WState.setv_cell]; rw [fcl, b3c, lA, cl0]
  have nS : ∀ v : ℕ, v ≠ 311 → v ≠ 312 → v ≠ 310 → v ≠ 313 → v ≠ 403 → v ≠ 408 → ∀ q : Fin LNR, q.val = v →
      σD.val q = σA.val q := fun v a b c d e f q hq =>
    dv q (fun h => a (by rw [← hq, h]; rfl)) (fun h => b (by rw [← hq, h]; rfl)) (fun h => c (by rw [← hq, h]; rfl))
      (fun h => d (by rw [← hq, h]; rfl)) (fun h => e (by rw [← hq, h]; rfl)) (fun h => f (by rw [← hq, h]; rfl))
  refine ⟨σD, _, WExec.seq eA (WExec.seq eB1 (WExec.seq eB2 (WExec.seq eB3 (WExec.seq eF eG)))), ?_, ?_⟩
  · have hK : K ≤ w.length := by omega
    have hKj : K - j ≤ w.length := by omega
    rw [← hw] at cA
    unfold decBoundP
    omega
  · have hk0 : sk x 0 ≠ sk x 113 := n0D
    have hk2 : sk x 2 ≠ sk x 113 := n2D
    exact
      { s0 := by rw [dst]; simp [CellLoopD.blankCellD, blankCell, hk0, hσ0]
        h0 := by rw [dsh]; simp [CellLoopD.blankCellD, blankCell, n01, hσ0]
        s1 := by rw [dst]; simp [CellLoopD.blankCellD, blankCell, n1D, n01.symm, hσ0]
        h1 := by rw [dsh]; simp [CellLoopD.blankCellD, blankCell, hσ0]
        s2 := by rw [dst]; simp [CellLoopD.blankCellD, blankCell, hk2, n02.symm, n12.symm, hσ0]
        h2 := by rw [dsh]; simp [CellLoopD.blankCellD, blankCell, n12.symm, hσ0]
        s113 := by rw [dst]; simp [CellLoopD.blankCellD, hσ0]
        blank := fun k k0 k1 k2 k3 => by
          have m0' : sk x k ≠ sk x 0 := fun e => k0 (by rw [sk_inj x e]; rfl)
          have m1' : sk x k ≠ sk x 1 := fun e => k1 (by rw [sk_inj x e]; rfl)
          have m2' : sk x k ≠ sk x 2 := fun e => k2 (by rw [sk_inj x e]; rfl)
          have m3' : sk x k ≠ sk x 113 := fun e => k3 (by rw [sk_inj x e]; rfl)
          refine ⟨?_, ?_⟩
          · rw [dst]; simp [CellLoopD.blankCellD, blankCell, m0', m1', m2', m3', hσ0]
          · rw [dsh]; simp [CellLoopD.blankCellD, blankCell, m1', hσ0]
        blankT := fun k => by
          have m0' : sT x k ≠ sk x 0 := (sk_ne_sT x 0 k).symm
          have m1' : sT x k ≠ sk x 1 := (sk_ne_sT x 1 k).symm
          have m2' : sT x k ≠ sk x 2 := (sk_ne_sT x 2 k).symm
          have m3' : sT x k ≠ sk x 113 := (sk_ne_sT x 113 k).symm
          refine ⟨?_, ?_⟩
          · rw [dst]; simp [CellLoopD.blankCellD, blankCell, m0', m1', m2', m3', hσ0]
          · rw [dsh]; simp [CellLoopD.blankCellD, blankCell, m1', hσ0]
        cell := dcl
        vM := by rw [nS 400 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ppM rfl]; exact aM
        vB := by rw [nS 401 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ppB rfl]; exact aB
        vErr := by
          rw [nS 402 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ppErr rfl]; exact aE
        vSeed := by rw [hσD, wsetv_val_ne _ _ (by decide), wsetv_val_ne _ _ (by decide), fSd]
        vSgn := by
          rw [nS 404 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ppSgn rfl]
          exact aZ ppSgn (by decide)
        vS := by
          rw [nS 405 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ppS rfl]
          exact aZ ppS (by decide)
        vR4 := by
          rw [nS 406 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ppR4 rfl]
          exact aZ ppR4 (by decide)
        vG := by
          rw [nS 407 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ppG rfl]
          exact aZ ppG (by decide)
        vOff := by rw [hσD, wsetv_val_self, o0, fK, Nat.zero_add]
        vL := by rw [nS 409 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ppL rfl]; exact aL
        zLow := fun q hq => by
          rw [nS q.val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) q rfl]
          exact aZ q (by omega)
        zHigh := fun q hq => by
          have : q.val ≠ 409 ∧ q.val ≠ 402 := by omega
          rw [nS q.val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) q rfl]
          exact aZ q (by omega) }

end NearCubicWires.WireExponent3_5.FinalPass.SymF
