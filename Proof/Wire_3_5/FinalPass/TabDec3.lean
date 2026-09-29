import Proof.Wire_3_5.FinalPass.TabDec2
import Proof.Wire_3_5.Primitive.Writers.CellLoopD

/-! # S4 (f1), the tables writer, part 5: a unit's decode to the FILTER setup's entry (P3:2036-2101)

Unit `j` of the tables writer builds the table of seed `j / 2` at mask length `L_{j % 2}`. **`decW`**, from the loop's
blank cell (`CellLoopD.blankCellD`: the request `frame w`, the output, the counter `1^j`, the data `u`): the request's
numbers (`parseW` at the registers `Rg1 = 300 … 308`), the counter counted and rewound (`cntK`), halved (`div2`), the
seed's test against the seed count (`cmpD`: the seed `j / 2` when `j / 2 < nE`, else `0`), the mask length chosen by
the parity, the filter's numbers moved into C6's registers. **`dec_spec`**: the decode reaches `FsIn2` (C6's FILTER
setup entry) at the seed `if j / 2 < nE then j / 2 else 0`, the labels `0`, the mask length
`if j % 2 = 0 then L₀ else L₁`, the data `u` untouched, within `60·|w| + 40·j + 400`.

Paper quantity of the main type: the FILTER setup's entry for the seed `j / 2` at the mask length `L_{j % 2}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.TabW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup

theorem skn (x : ℕ) (a b : Fin 161) (h : a ≠ b) : sk x a ≠ sk x b := fun e => h (sk_inj x e)

/-- The decode's parse registers `300 … 308`. -/
def Rg1 : Fin 9 ↪ Fin LNR :=
  ⟨fun k => ⟨300 + k.val, by have := k.isLt; unfold LNR; omega⟩, fun a b h => Fin.ext (by
    have := congrArg Fin.val h; simp at this; omega)⟩

abbrev rLen : Fin LNR := Rg1 3
abbrev rCp : Fin LNR := Rg1 4
abbrev rEr : Fin LNR := Rg1 5
abbrev rL0 : Fin LNR := Rg1 6
abbrev rL1 : Fin LNR := Rg1 7
abbrev rNE : Fin LNR := Rg1 8

theorem notRg1 (q : Fin LNR) (hq : q.val < 300 ∨ 309 ≤ q.val) : ∀ k, q ≠ Rg1 k := fun k e => by
  have h := congrArg Fin.val e
  have := k.isLt
  simp [Rg1] at h
  omega

def rJa : Fin LNR := ⟨310, by decide⟩
def rJb : Fin LNR := ⟨311, by decide⟩
def rPar : Fin LNR := ⟨312, by decide⟩
def rSd : Fin LNR := ⟨313, by decide⟩
def rSd2 : Fin LNR := ⟨314, by decide⟩

variable (cap x : ℕ)

/-- The seed's test: the seed moved into C6's register when it is below the seed count. -/
def flagW : WM (LNS x) LNR := .ifr rNE (WM.move rSd2 fsSeed) .skip

/-- The mask length chosen by the parity. -/
def maskW : WM (LNS x) LNR := .ifr rPar (WM.move rL1 fsL) (WM.move rL0 fsL)

/-- **A unit's decode.** -/
def decW : WM (LNS x) LNR :=
  .seq (parseW x Rg1) (.seq (cntK (sk x 2) rJa rJb) (.seq (WM.rewind (sk x 2) rJb) (.seq (div2 rJa rPar rSd)
    (.seq (cmpD rSd rNE rSd2) (.seq (flagW x) (.seq (maskW x) (.seq (WM.move rLen fsLen)
    (.seq (WM.move rCp fsCap) (WM.move rEr fsErr)))))))))

theorem flag_spec (σ : WState (LNS x) LNR) (a b : ℕ) (hNE : σ.val rNE = b - a) (hS2 : σ.val rSd2 = a)
    (hS : σ.val fsSeed = 0) (ha : a ≤ cap) :
    ∃ (σ' : WState (LNS x) LNR) (c : ℕ), WExec cap (flagW x) σ σ' c ∧ c ≤ 7 * a + 2 ∧ σ'.st = σ.st ∧
      σ'.sh = σ.sh ∧ σ'.val fsSeed = (if a < b then a else 0) ∧
      (∀ q, q ≠ fsSeed → q ≠ rSd2 → σ'.val q = σ.val q) ∧ σ'.cell = σ.cell := by
  by_cases hab : a < b
  · have e := wmove_spec cap rSd2 fsSeed (by decide) a σ hS2 (by rw [hS2]; omega) (by rw [hS, hS2]; omega)
    refine ⟨_, _, WExec.ifrT (by rw [hNE]; omega) e, by omega, rfl, rfl, by simp [hab, hS, hS2], ?_, rfl⟩
    intro q h1 h2
    simp [Function.update_of_ne h1, Function.update_of_ne h2]
  · exact ⟨σ, _, WExec.ifrF (by rw [hNE]; omega) (WExec.skip σ), by omega, rfl, rfl, by simp [hab, hS],
      fun _ _ _ => rfl, rfl⟩

theorem mask_spec (σ : WState (LNS x) LNR) (j L0 L1 : ℕ) (hP : σ.val rPar = j % 2) (h0 : σ.val rL0 = L0)
    (h1 : σ.val rL1 = L1) (hL : σ.val fsL = 0) (hc0 : L0 ≤ cap) (hc1 : L1 ≤ cap) :
    ∃ (σ' : WState (LNS x) LNR) (c : ℕ), WExec cap (maskW x) σ σ' c ∧ c ≤ 7 * (L0 + L1) + 2 ∧
      σ'.st = σ.st ∧ σ'.sh = σ.sh ∧ σ'.val fsL = (if j % 2 = 0 then L0 else L1) ∧
      (∀ q, q ≠ fsL → q ≠ rL0 → q ≠ rL1 → σ'.val q = σ.val q) ∧ σ'.cell = σ.cell := by
  by_cases hj : j % 2 = 0
  · have e := wmove_spec cap rL0 fsL (by decide) L0 σ h0 (by omega) (by omega)
    refine ⟨_, _, WExec.ifrF (by rw [hP, hj]) e, by omega, rfl, rfl, by simp [hj, hL, h0], ?_, rfl⟩
    intro q a b c
    simp [Function.update_of_ne a, Function.update_of_ne b]
  · have e := wmove_spec cap rL1 fsL (by decide) L1 σ h1 (by omega) (by omega)
    refine ⟨_, _, WExec.ifrT (by rw [hP]; omega) e, by omega, rfl, rfl, by simp [hj, hL, h1], ?_, rfl⟩
    intro q a b c
    simp [Function.update_of_ne a, Function.update_of_ne c]

/-- The decode's cost bound. -/
def decBound (lw j : ℕ) : ℕ := 60 * lw + 40 * j + 400

theorem dec_spec (n len cp err L0 L1 nE j : ℕ) (w out u : List Bool) (hw : w = reqT n len cp err L0 L1 nE)
    (hc : 2 * w.length + 2 ≤ cap) (hj : j + 1 ≤ cap) (hc2 : 2 ≤ cap) :
    ∃ (σD : WState (LNS x) LNR) (m : ℕ), WExec cap (decW x) (blankCellD x w out j u) σD m ∧
      m ≤ decBound w.length j ∧
      FsIn2 x σD w out j u len cp err (if j / 2 < nE then j / 2 else 0)
        0 0 0 (if j % 2 = 0 then L0 else L1) := by
  set σ0 := blankCellD x w out j u with hσ0
  have n01 := skn x 0 1 (by decide)
  have n02 := skn x 0 2 (by decide)
  have n12 := skn x 1 2 (by decide)
  have n0D := skn x 0 113 (by decide)
  have n1D := skn x 1 113 (by decide)
  have n2D := skn x 2 113 (by decide)
  have st0 : ∀ i, σ0.st i = if i = sk x 113 then u else (blankCell x w out j).st i := fun i => by
    rw [hσ0]; unfold blankCellD; simp only [WState.sets_st, Function.update_apply]
  have v0 : ∀ q, σ0.val q = 0 := fun q => by rw [hσ0]; rfl
  have sh0 : ∀ i, σ0.sh i = if i = sk x 1 then out.length else 0 := fun i => by rw [hσ0]; rfl
  have cl0 : σ0.cell = false := by rw [hσ0]; rfl
  have hlw : len + cp + err + L0 + L1 + nE ≤ w.length := by
    have := congrArg List.length (reqT_eq n len cp err L0 L1 nE)
    rw [← hw] at this
    rw [this]
    simp [Data.unaryList]
    omega
  -- the request's numbers
  obtain ⟨σA, mA, eA, cA, sA, hA, lA, aLen, aCp, aEr, aL0, aL1, aNE, aO, -, -⟩ := parse_spec cap x Rg1 n len cp err L0 L1
    nE σ0 (by rw [st0, if_neg n0D, ← hw]; simp [blankCell]) (by rw [sh0, if_neg n01]) (fun k => v0 _)
    (by rw [← hw]; exact hc)
  have aZ : ∀ q : Fin LNR, (q.val < 300 ∨ 309 ≤ q.val) → σA.val q = 0 := fun q hq => by
    rw [aO q (notRg1 q hq), v0]
  -- the counter
  have eB1 := cntK_spec cap (sk x 2) rJa rJb (by decide) j (by omega) j 0 σA (by omega)
    (by rw [sA, st0, if_neg n2D]; simp [blankCell, n02.symm, n12.symm])
    (by rw [hA, sh0, if_neg n12.symm]) (by rw [aZ rJa (by decide)]; omega)
    (by rw [aZ rJb (by decide)]; omega)
  obtain ⟨σB1, hB1⟩ : ∃ y : WState (LNS x) LNR, y = ((σA.seth (sk x 2) j).setv rJa (σA.val rJa + j)).setv rJb
      (σA.val rJb + j) := ⟨_, rfl⟩
  rw [← hB1] at eB1
  have eB2 := wrewind_spec cap (sk x 2) rJb j σB1 (by rw [hB1]; simp [aZ rJb (by decide)])
    (by rw [hB1]; simp [aZ rJb (by decide)]; omega)
  obtain ⟨σB2, hB2⟩ : ∃ y : WState (LNS x) LNR, y = (σB1.setv rJb 0).seth (sk x 2) (σB1.sh (sk x 2) - j) :=
    ⟨_, rfl⟩
  rw [← hB2] at eB2
  have bB2v : ∀ q, q ≠ rJa → q ≠ rJb → σB2.val q = σA.val q := fun q a b => by
    rw [hB2, hB1]; simp [Function.update_of_ne a, Function.update_of_ne b]
  have bB2a : σB2.val rJa = j := by
    rw [hB2, hB1]; simp [Function.update_of_ne (by decide : rJa ≠ rJb), aZ rJa (by decide)]
  have bB2st : σB2.st = σA.st := by rw [hB2, hB1]; rfl
  have bB2sh : σB2.sh = σA.sh := by
    funext i
    rw [hB2, hB1]
    by_cases hi : i = sk x 2
    · rw [hi]; simp [hA, sh0, n12.symm]
    · simp [Function.update_of_ne hi]
  have bB2c : σB2.cell = σA.cell := by rw [hB2, hB1]; rfl
  -- halving
  have eB3 := div2_spec cap rJa rPar rSd (by decide) (by decide) (by decide) hc2 j 0 σB2 bB2a (by omega)
    (by rw [bB2v rPar (by decide) (by decide), aZ rPar (by decide)])
    (by rw [bB2v rSd (by decide) (by decide), aZ rSd (by decide)]) (by omega)
  obtain ⟨σB3, hB3⟩ : ∃ y : WState (LNS x) LNR, y = ((σB2.setv rJa 0).setv rPar ((0 + j) % 2)).setv rSd
      ((0 + j) / 2) := ⟨_, rfl⟩
  rw [← hB3] at eB3
  -- the seed's test
  have b3NE : σB3.val rNE = nE := by
    rw [hB3, wsetv_val_ne _ _ (by decide : rNE ≠ rSd), wsetv_val_ne _ _ (by decide : rNE ≠ rPar),
      wsetv_val_ne _ _ (by decide : rNE ≠ rJa), bB2v rNE (by decide) (by decide), aNE]
  have b3S2 : σB3.val rSd2 = 0 := by
    rw [hB3, wsetv_val_ne _ _ (by decide : rSd2 ≠ rSd), wsetv_val_ne _ _ (by decide : rSd2 ≠ rPar),
      wsetv_val_ne _ _ (by decide : rSd2 ≠ rJa), bB2v rSd2 (by decide) (by decide), aZ rSd2 (by decide)]
  have b3P : σB3.val rPar = j % 2 := by
    rw [hB3, wsetv_val_ne _ _ (by decide : rPar ≠ rSd), wsetv_val_self, Nat.zero_add]
  have b3S : σB3.val rSd = j / 2 := by rw [hB3, wsetv_val_self, Nat.zero_add]
  have eB4 := cmpD_spec cap rSd rNE rSd2 (by decide) (by decide) (by decide) (j / 2) σB3 b3S (by omega)
    (by rw [b3NE]; omega) (by rw [b3S2]; omega)
  obtain ⟨σB4, hB4⟩ : ∃ y : WState (LNS x) LNR, y = ((σB3.setv rSd 0).setv rNE (σB3.val rNE - j / 2)).setv rSd2
      (σB3.val rSd2 + j / 2) := ⟨_, rfl⟩
  rw [← hB4] at eB4
  have b4v : ∀ q, q ≠ rJa → q ≠ rJb → q ≠ rPar → q ≠ rSd → q ≠ rNE → q ≠ rSd2 → σB4.val q = σA.val q :=
    fun q a b c d e f => by
      rw [hB4, hB3]
      simp [Function.update_of_ne a, Function.update_of_ne c, Function.update_of_ne d, Function.update_of_ne e,
        Function.update_of_ne f, bB2v q a b]
  have b4NE : σB4.val rNE = nE - j / 2 := by
    rw [hB4, wsetv_val_ne _ _ (by decide : rNE ≠ rSd2), wsetv_val_self, b3NE]
  have b4S2 : σB4.val rSd2 = j / 2 := by
    rw [hB4, wsetv_val_self, b3S2, Nat.zero_add]
  have b4P : σB4.val rPar = j % 2 := by
    rw [hB4, wsetv_val_ne _ _ (by decide : rPar ≠ rSd2), wsetv_val_ne _ _ (by decide : rPar ≠ rNE),
      wsetv_val_ne _ _ (by decide : rPar ≠ rSd), b3P]
  have b4st : σB4.st = σA.st := by rw [hB4, hB3, bB2st.symm]; rfl
  have b4sh : σB4.sh = σA.sh := by rw [hB4, hB3, bB2sh.symm]; rfl
  have b4c : σB4.cell = σA.cell := by rw [hB4, hB3, bB2c.symm]; rfl
  -- the flag
  obtain ⟨σC1, mC1, eC1, cC1, sC1, hC1, fC1, vC1, lC1⟩ := flag_spec cap x σB4 (j / 2) nE b4NE b4S2
    (by rw [b4v fsSeed (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), aO fsSeed
      (notRg1 fsSeed (by decide)), v0]) (by omega)
  -- the mask length
  obtain ⟨σC2, mC2, eC2, cC2, sC2, hC2, fC2, vC2, lC2⟩ := mask_spec cap x σC1 j L0 L1
    (by rw [vC1 rPar (by decide) (by decide), b4P])
    (by rw [vC1 rL0 (by decide) (by decide), b4v rL0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), aL0])
    (by rw [vC1 rL1 (by decide) (by decide), b4v rL1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), aL1])
    (by rw [vC1 fsL (by decide) (by decide), b4v fsL (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), aO fsL (notRg1 fsL (by decide)), v0]) (by omega) (by omega)
  -- the filter's numbers
  have gC2 : ∀ q, q ≠ fsL → q ≠ rL0 → q ≠ rL1 → q ≠ fsSeed → q ≠ rSd2 → q ≠ rJa → q ≠ rJb → q ≠ rPar →
      q ≠ rSd → q ≠ rNE → σC2.val q = σA.val q := fun q a b c d e f g h i k => by
    rw [vC2 q a b c, vC1 q d e, b4v q f g h i k e]
  have eD1 := wmove_spec cap rLen fsLen (by decide) len σC2
    (by rw [gC2 rLen (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), aLen]) (by
      rw [gC2 rLen (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), aLen]; omega)
    (by rw [gC2 rLen (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), gC2 fsLen (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), aLen, aO fsLen (notRg1 fsLen (by decide)), v0]; omega)
  obtain ⟨σD1, hD1⟩ : ∃ y : WState (LNS x) LNR, y = (σC2.setv rLen 0).setv fsLen (σC2.val fsLen + σC2.val rLen) :=
    ⟨_, rfl⟩
  rw [← hD1] at eD1
  have gD1 : ∀ q, q ≠ rLen → q ≠ fsLen → σD1.val q = σC2.val q := fun q a b => by
    rw [hD1]; simp [Function.update_of_ne a, Function.update_of_ne b]
  have eD2 := wmove_spec cap rCp fsCap (by decide) cp σD1
    (by rw [gD1 rCp (by decide) (by decide), gC2 rCp (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), aCp])
    (by rw [gD1 rCp (by decide) (by decide), gC2 rCp (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), aCp]; omega)
    (by rw [gD1 rCp (by decide) (by decide), gC2 rCp (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), gD1 fsCap (by decide) (by decide),
      gC2 fsCap (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), aCp, aO fsCap (notRg1 fsCap (by decide)), v0]; omega)
  obtain ⟨σD2, hD2⟩ : ∃ y : WState (LNS x) LNR, y = (σD1.setv rCp 0).setv fsCap (σD1.val fsCap + σD1.val rCp) :=
    ⟨_, rfl⟩
  rw [← hD2] at eD2
  have gD2 : ∀ q, q ≠ rCp → q ≠ fsCap → σD2.val q = σD1.val q := fun q a b => by
    rw [hD2]; simp [Function.update_of_ne a, Function.update_of_ne b]
  have eD3 := wmove_spec cap rEr fsErr (by decide) err σD2
    (by rw [gD2 rEr (by decide) (by decide), gD1 rEr (by decide) (by decide), gC2 rEr (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), aEr])
    (by rw [gD2 rEr (by decide) (by decide), gD1 rEr (by decide) (by decide), gC2 rEr (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), aEr]; omega)
    (by rw [gD2 rEr (by decide) (by decide), gD1 rEr (by decide) (by decide), gC2 rEr (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      gD2 fsErr (by decide) (by decide), gD1 fsErr (by decide) (by decide), gC2 fsErr (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), aEr,
      aO fsErr (notRg1 fsErr (by decide)), v0]; omega)
  obtain ⟨σD3, hD3⟩ : ∃ y : WState (LNS x) LNR, y = (σD2.setv rEr 0).setv fsErr (σD2.val fsErr + σD2.val rEr) :=
    ⟨_, rfl⟩
  rw [← hD3] at eD3
  have gD3 : ∀ q, q ≠ rEr → q ≠ fsErr → σD3.val q = σD2.val q := fun q a b => by
    rw [hD3]; simp [Function.update_of_ne a, Function.update_of_ne b]
  have sD3 : σD3.st = σA.st := by
    rw [hD3, hD2, hD1]
    simp only [WState.setv_st]
    rw [sC2, sC1, b4st]
  have shD3 : σD3.sh = σ0.sh := by
    rw [hD3, hD2, hD1]
    simp only [WState.setv_sh]
    rw [hC2, hC1, b4sh, hA]
  have cD3 : σD3.cell = false := by
    rw [hD3, hD2, hD1]
    simp only [WState.setv_cell]
    rw [lC2, lC1, b4c, lA, cl0]
  -- the numbers' final values
  have fLen : σD3.val fsLen = len := by
    rw [gD3 fsLen (by decide) (by decide), gD2 fsLen (by decide) (by decide), hD1]
    simp only [WState.setv_val, Function.update_self]
    rw [gC2 fsLen (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), gC2 rLen (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), aLen,
      aO fsLen (notRg1 fsLen (by decide)), v0]
    omega
  have fCp : σD3.val fsCap = cp := by
    rw [gD3 fsCap (by decide) (by decide), hD2]
    simp only [WState.setv_val, Function.update_self]
    rw [gD1 fsCap (by decide) (by decide), gD1 rCp (by decide) (by decide),
      gC2 fsCap (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), gC2 rCp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), aCp, aO fsCap (notRg1 fsCap (by decide)), v0]
    omega
  have fEr : σD3.val fsErr = err := by
    rw [hD3]
    simp only [WState.setv_val, Function.update_self]
    rw [gD2 fsErr (by decide) (by decide), gD2 rEr (by decide) (by decide),
      gD1 fsErr (by decide) (by decide), gD1 rEr (by decide) (by decide),
      gC2 fsErr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), gC2 rEr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), aEr, aO fsErr (notRg1 fsErr (by decide)), v0]
    omega
  have fSeed : σD3.val fsSeed = if j / 2 < nE then j / 2 else 0 := by
    rw [gD3 fsSeed (by decide) (by decide), gD2 fsSeed (by decide) (by decide), gD1 fsSeed (by decide) (by decide),
      vC2 fsSeed (by decide) (by decide) (by decide), fC1]
  have fL : σD3.val fsL = if j % 2 = 0 then L0 else L1 := by
    rw [gD3 fsL (by decide) (by decide), gD2 fsL (by decide) (by decide), gD1 fsL (by decide) (by decide), fC2]
  have fZ : ∀ q : Fin LNR, (q.val < 300 ∨ 315 ≤ q.val) → q ≠ fsLen → q ≠ fsCap → q ≠ fsErr → q ≠ fsSeed →
      q ≠ fsL → σD3.val q = 0 := fun q hq a6 a4 a2 b1 a7 => by
    have hq' : q.val < 300 ∨ 309 ≤ q.val := by omega
    have a1 : q ≠ rEr := notRg1 q hq' 5
    have a3 : q ≠ rCp := notRg1 q hq' 4
    have a5 : q ≠ rLen := notRg1 q hq' 3
    have a8 : q ≠ rL0 := notRg1 q hq' 6
    have a9 : q ≠ rL1 := notRg1 q hq' 7
    have b2 : q ≠ rSd2 := fun e => by subst e; simp [rSd2] at hq
    have b3 : q ≠ rJa := fun e => by subst e; simp [rJa] at hq
    have b4 : q ≠ rJb := fun e => by subst e; simp [rJb] at hq
    have b5 : q ≠ rPar := fun e => by subst e; simp [rPar] at hq
    have b6 : q ≠ rSd := fun e => by subst e; simp [rSd] at hq
    have b7 : q ≠ rNE := notRg1 q hq' 8
    rw [gD3 q a1 a2, gD2 q a3 a4, gD1 q a5 a6, gC2 q a7 a8 a9 b1 b2 b3 b4 b5 b6 b7, aO q (notRg1 q hq'), v0]
  refine ⟨σD3, _, WExec.seq eA (WExec.seq eB1 (WExec.seq eB2 (WExec.seq eB3 (WExec.seq eB4 (WExec.seq eC1
    (WExec.seq eC2 (WExec.seq eD1 (WExec.seq eD2 eD3)))))))), ?_, ?_⟩
  · unfold decBound
    have hj2 : j / 2 ≤ j := Nat.div_le_self j 2
    rw [← hw] at cA
    omega
  · refine
      { s0 := ?_, s1 := ?_, h1 := ?_, s2 := ?_, h2 := ?_, s113 := ?_, blank := ?_, blankT := ?_,
        cell := cD3, vLen := fLen, vCap := fCp, vErr := fEr, vSeed := fSeed, vR4 := ?_, vG := ?_,
        vOff := ?_, vL := fL, zLow := ?_, zHigh := ?_, h0 := ?_ }
    · rw [sD3, sA, st0, if_neg n0D]; simp [blankCell]
    · rw [sD3, sA, st0, if_neg n1D]; simp [blankCell, n01.symm]
    · rw [shD3, sh0, if_pos rfl]
    · rw [sD3, sA, st0, if_neg n2D]; simp [blankCell, n02.symm, n12.symm]
    · rw [shD3, sh0, if_neg n12.symm]
    · rw [sD3, sA, st0, if_pos rfl]
    · intro k k0 k1 k2 k3
      have m0 : sk x k ≠ sk x 0 := skn x k 0 (fun e => k0 (by rw [e]; rfl))
      have m1 : sk x k ≠ sk x 1 := skn x k 1 (fun e => k1 (by rw [e]; rfl))
      have m2 : sk x k ≠ sk x 2 := skn x k 2 (fun e => k2 (by rw [e]; rfl))
      have m3 : sk x k ≠ sk x 113 := skn x k 113 (fun e => k3 (by rw [e]; rfl))
      refine ⟨?_, ?_⟩
      · rw [sD3, sA, st0, if_neg m3]; simp [blankCell, m0, m1, m2]
      · rw [shD3, sh0, if_neg m1]
    · intro k
      have m0 := sk_ne_sT x 0 k
      have m1 := sk_ne_sT x 1 k
      have m2 := sk_ne_sT x 2 k
      have m3 := sk_ne_sT x 113 k
      refine ⟨?_, ?_⟩
      · rw [sD3, sA, st0, if_neg m3.symm]
        simp [blankCell, m0.symm, m1.symm, m2.symm]
      · rw [shD3, sh0, if_neg m1.symm]
    · exact fZ fsR4 (Or.inr (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact fZ fsG (Or.inr (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact fZ fsOff (Or.inr (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    · intro q hq
      exact fZ q (Or.inl (by omega)) (fun e => by subst e; simp [fsLen] at hq) (fun e => by subst e; simp [fsCap] at hq)
        (fun e => by subst e; simp [fsErr] at hq) (fun e => by subst e; simp [fsSeed] at hq)
        (fun e => by subst e; simp [fsL] at hq)
    · intro q hq
      exact fZ q (Or.inr (by omega)) (fun e => by subst e; simp [fsLen] at hq) (fun e => by subst e; simp [fsCap] at hq)
        (fun e => by subst e; simp [fsErr] at hq) (fun e => by subst e; simp [fsSeed] at hq)
        (fun e => by subst e; simp [fsL] at hq)
    · rw [shD3, sh0, if_neg n01]

end NearCubicWires.WireExponent3_5.FinalPass.TabW
