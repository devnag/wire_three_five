import Proof.Wire_3_5.FinalPass.Core3

/-! # S5Core, part 4: the request's mode read off the input (P3:3083-3086)

The core half writes the SYM evaluator's words only at a SYM request (`SymWordsW` runs at `mode = sym`). The mode is
the request word's bit after `natWord n = 1^L 0 b_1 … b_L` (`L = natBitLength n`, `PrimAsm.Data.reqW`). A register-free
word program reads it: the input's leading ones counted on `Q = sent L` (`loopA`), `L` more framed cells skipped
against that count (`loopB`), the bit copied to `M`, the input's head returned through the count's template
`T = sent N` (S5T's `rewIn`):

* `read_frame_odd`, `mSt`, **`loopA_spec`**, **`loopB_spec`**, `modeW`, **`modeW_spec`** (from
  `frame (1^L 0 bits mb rest)`, `|bits| = L`: `Q = sent L`, `M = [mb]`, every head back at `0`).

Paper quantity: the request's mode bit (P3:3083-3086). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length read_sent rewIn rewIn_spec)
open NearCubicWires.WireExponent3_5.FinalPass.HashSeed (emit1 emit1_spec appW appW_st appW_sh appW_val)

/-- A framed word's odd cells are its bits. -/
theorem read_frame_odd : ∀ (w : List Bool) (i : ℕ), readTapeBit (frame w) (2 * i + 1) = w.getD i false
  | [], i => by simp [frame, readTapeBit, List.getD]
  | b :: bs, 0 => by simp [frame, readTapeBit]
  | b :: bs, i + 1 => by
    have h := read_frame_odd bs i
    simp only [readTapeBit] at h ⊢
    rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by ring]
    simpa [frame] using h

/-- The mode program's streams: `0` the input, `1` the template `sent N`, `2` the count `Q`, `3` the mode `M`. -/
abbrev mI : Fin 4 := 0
abbrev mT : Fin 4 := 1
abbrev mQ : Fin 4 := 2
abbrev mM : Fin 4 := 3

theorem mIQ : mI ≠ mQ := by decide
theorem mIT : mI ≠ mT := by decide
theorem mQM : mQ ≠ mM := by decide
theorem mIM : mI ≠ mM := by decide
theorem mTQ : mT ≠ mQ := by decide
theorem mTM : mT ≠ mM := by decide

/-- Count the leading ones: one `1` on `Q` per `1` of the input, the input's head two cells on. -/
def loopA : WM 3 0 := .whs mI (.seq (emit1 mQ true) (.seq (.fwd mI) (.fwd mI)))

/-- The state after `i` ones. -/
def mSt (σ : WState 3 0) (i : ℕ) : WState 3 0 := ((σ.sets mQ (sent i)).seth mI (2 * i + 1)).seth mQ (i + 1)

theorem mSt_stI (σ : WState 3 0) (i : ℕ) : (mSt σ i).st mI = σ.st mI := by
  simp only [mSt, WState.seth_st, WState.sets_st]; rw [Function.update_of_ne mIQ]

theorem mSt_stQ (σ : WState 3 0) (i : ℕ) : (mSt σ i).st mQ = sent i := by
  simp only [mSt, WState.seth_st, WState.sets_st]; rw [Function.update_self]

theorem mSt_shI (σ : WState 3 0) (i : ℕ) : (mSt σ i).sh mI = 2 * i + 1 := by
  simp only [mSt, WState.seth_sh]; rw [Function.update_of_ne mIQ, Function.update_self]

theorem mSt_shQ (σ : WState 3 0) (i : ℕ) : (mSt σ i).sh mQ = i + 1 := by
  simp only [mSt, WState.seth_sh]; rw [Function.update_self]

theorem loopA_spec (cap : ℕ) (w : List Bool) (L : ℕ) (hw : ∀ i < L, w.getD i false = true)
    (hL : w.getD L false = false) (σ : WState 3 0) (hI : σ.st mI = frame w) :
    ∀ (m i : ℕ), i + m = L → WExec cap loopA (mSt σ i) (mSt σ L) (9 * m + 1)
  | 0, i, h => by
    have hi : i = L := by omega
    subst hi
    refine WExec.whsF ?_
    unfold wbit
    rw [mSt_stI, mSt_shI, hI, read_frame_odd, hL]
  | m + 1, i, h => by
    have hb : wbit (mSt σ i) mI = true := by
      unfold wbit
      rw [mSt_stI, mSt_shI, hI, read_frame_odd, hw i (by omega)]
    have e1 := emit1_spec cap mQ true (mSt σ i) (by rw [mSt_shQ, mSt_stQ, sent_length])
    have e2 := WExec.fwd (cap := cap) mI (appW (mSt σ i) mQ [true])
    have e3 := WExec.fwd (cap := cap) mI ((appW (mSt σ i) mQ [true]).seth mI ((appW (mSt σ i) mQ [true]).sh mI + 1))
    have hnext : ((appW (mSt σ i) mQ [true]).seth mI ((appW (mSt σ i) mQ [true]).sh mI + 1)).seth mI
        (((appW (mSt σ i) mQ [true]).seth mI ((appW (mSt σ i) mQ [true]).sh mI + 1)).sh mI + 1) = mSt σ (i + 1) := by
      refine WState.eq ?_ ?_ rfl rfl
      · funext j
        simp only [WState.seth_sh, appW_sh, Function.update_self]
        by_cases hj : j = mI
        · subst hj
          rw [Function.update_self, Function.update_of_ne mIQ, mSt_shI, mSt_shI]; ring
        · rw [Function.update_of_ne hj, Function.update_of_ne hj]
          by_cases hq : j = mQ
          · subst hq; rw [Function.update_self, mSt_stQ, sent_length, mSt_shQ]; simp
          · rw [Function.update_of_ne hq]
            simp only [mSt, WState.seth_sh]
            rw [Function.update_of_ne hq, Function.update_of_ne hj, Function.update_of_ne hq, Function.update_of_ne hj]
            rfl
      · funext j
        simp only [WState.seth_st, appW_st]
        by_cases hq : j = mQ
        · subst hq; rw [Function.update_self, mSt_stQ, mSt_stQ]; simp [sent]
        · rw [Function.update_of_ne hq]
          simp only [mSt, WState.seth_st, WState.sets_st]
          rw [Function.update_of_ne hq, Function.update_of_ne hq]
    rw [hnext] at e3
    have ih := loopA_spec cap w L hw hL σ hI m (i + 1) (by omega)
    exact WExec.mono (WExec.whsT hb (WExec.seq e1 (WExec.seq e2 e3)) ih) (by omega)

/-- Skip against the count: two input cells per `1` of `Q`, `Q`'s head back to `0`. -/
def loopB : WM 3 0 := .whs mQ (.seq (.fwd mI) (.seq (.fwd mI) (.bwd mQ)))

/-- The state after the skip. -/
def bSt (σ : WState 3 0) (p j : ℕ) : WState 3 0 := (σ.seth mI p).seth mQ j

theorem bSt_shI (σ : WState 3 0) (p j : ℕ) : (bSt σ p j).sh mI = p := by
  simp only [bSt, WState.seth_sh]; rw [Function.update_of_ne mIQ, Function.update_self]

theorem bSt_shQ (σ : WState 3 0) (p j : ℕ) : (bSt σ p j).sh mQ = j := by
  simp only [bSt, WState.seth_sh]; rw [Function.update_self]

theorem bSt_st (σ : WState 3 0) (p j : ℕ) : (bSt σ p j).st = σ.st := rfl

theorem loopB_spec (cap L : ℕ) (σ : WState 3 0) (hQ : σ.st mQ = sent L) :
    ∀ (j p : ℕ), j ≤ L → WExec cap loopB (bSt σ p j) (bSt σ (p + 2 * j) 0) (7 * j + 1)
  | 0, p, _ => by
    refine WExec.whsF ?_
    unfold wbit; rw [bSt_st, bSt_shQ, hQ, read_sent]; simp
  | j + 1, p, hjL => by
    have hb : wbit (bSt σ p (j + 1)) mQ = true := by
      unfold wbit; rw [bSt_st, bSt_shQ, hQ, read_sent]; simp; omega
    have e1 := WExec.fwd (cap := cap) mI (bSt σ p (j + 1))
    have x1 : (bSt σ p (j + 1)).seth mI ((bSt σ p (j + 1)).sh mI + 1) = bSt σ (p + 1) (j + 1) := by
      rw [bSt_shI]
      refine WState.eq ?_ rfl rfl rfl
      funext k
      simp only [bSt, WState.seth_sh]
      by_cases hk : k = mI
      · subst hk; rw [Function.update_self, Function.update_of_ne mIQ, Function.update_self]
      · rw [Function.update_of_ne hk]
        by_cases hq : k = mQ
        · subst hq; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hq, Function.update_of_ne hk, Function.update_of_ne hq, Function.update_of_ne hk]
    rw [x1] at e1
    have e2 := WExec.fwd (cap := cap) mI (bSt σ (p + 1) (j + 1))
    have x2 : (bSt σ (p + 1) (j + 1)).seth mI ((bSt σ (p + 1) (j + 1)).sh mI + 1) = bSt σ (p + 2) (j + 1) := by
      rw [bSt_shI]
      refine WState.eq ?_ rfl rfl rfl
      funext k
      simp only [bSt, WState.seth_sh]
      by_cases hk : k = mI
      · subst hk; rw [Function.update_self, Function.update_of_ne mIQ, Function.update_self]
      · rw [Function.update_of_ne hk]
        by_cases hq : k = mQ
        · subst hq; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hq, Function.update_of_ne hk, Function.update_of_ne hq, Function.update_of_ne hk]
    rw [x2] at e2
    have e3 := WExec.bwd (cap := cap) mQ (bSt σ (p + 2) (j + 1))
    have x3 : (bSt σ (p + 2) (j + 1)).seth mQ ((bSt σ (p + 2) (j + 1)).sh mQ - 1) = bSt σ (p + 2) j := by
      rw [bSt_shQ, Nat.add_sub_cancel]
      refine WState.eq ?_ rfl rfl rfl
      funext k
      simp only [bSt, WState.seth_sh]
      by_cases hq : k = mQ
      · subst hq; rw [Function.update_self, Function.update_self]
      · simp only [Function.update_of_ne hq]
    rw [x3] at e3
    have ih := loopB_spec cap L σ hQ j (p + 2) (by omega)
    rw [show p + 2 + 2 * j = p + 2 * (j + 1) by ring] at ih
    exact WExec.mono (WExec.whsT hb (WExec.seq e1 (WExec.seq e2 e3)) ih) (by omega)

/-! ## The mode program -/

/-- The input word's cells: `L` ones, a zero, `L` bits, the mode bit. -/
theorem mw_ones (L : ℕ) (bits : List Bool) (mb : Bool) (rest : List Bool) (i : ℕ) (hi : i < L) :
    (List.replicate L true ++ false :: (bits ++ mb :: rest)).getD i false = true := by
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi]

theorem mw_zero (L : ℕ) (bits : List Bool) (mb : Bool) (rest : List Bool) :
    (List.replicate L true ++ false :: (bits ++ mb :: rest)).getD L false = false := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem mw_mode (L : ℕ) (bits : List Bool) (mb : Bool) (rest : List Bool) (hb : bits.length = L) :
    (List.replicate L true ++ false :: (bits ++ mb :: rest)).getD (2 * L + 1) false = mb := by
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  rw [List.length_replicate, show 2 * L + 1 - L = (L + 1) by omega, List.getD_cons_succ]
  rw [List.getD_append_right _ _ _ _ (by omega), hb, Nat.sub_self]
  rfl

/-- **The mode program**: count the leading ones, skip that many framed bits, copy the mode bit to `M`, return the
input's head through the template. -/
def modeW : WM 3 0 :=
  .seq (emit1 mQ false) (.seq (.fwd mI) (.seq loopA (.seq (.bwd mQ) (.seq loopB (.seq (.fwd mI) (.seq (.fwd mI)
    (.seq (.ifs mI (.wr mM true) (.wr mM false)) (rewIn mI mT))))))))

/-- Its cost. -/
def modeCost (L N : ℕ) : ℕ :=
  3 + 1 + (1 + 1 + (9 * L + 1 + 1 + (1 + 1 + (7 * L + 1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + 1 + (10 * N + 7))))))))

theorem seth_cases (σ : WState 3 0) (i : Fin 4) (x : ℕ) (j : Fin 4) :
    (σ.seth i x).sh j = if j = i then x else σ.sh j := by
  simp only [WState.seth_sh, Function.update_apply]

/-- **The mode program's run**: from `frame (1^L 0 bits mb rest)` (`|bits| = L`) on `mI`, the template `sent N` on
`mT` (`4L + 3 ≤ 2N`), `mQ`, `mM` blank, heads `0`: `mQ = sent L`, `mM = [mb]`, every head back at `0`. -/
theorem modeW_spec (cap L N : ℕ) (bits : List Bool) (mb : Bool) (rest : List Bool) (hb : bits.length = L)
    (hN : 4 * L + 3 ≤ 2 * N) (σ : WState 3 0) (hI : σ.st mI = frame (List.replicate L true ++ false :: (bits ++ mb :: rest)))
    (hT : σ.st mT = sent N) (hQ : σ.st mQ = []) (hM : σ.st mM = []) (hh : ∀ i, σ.sh i = 0) :
    WExec cap modeW σ ((σ.sets mQ (sent L)).sets mM [mb]) (modeCost L N) := by
  have e1 := emit1_spec cap mQ false σ (by rw [hh, hQ]; rfl)
  have e2 := WExec.fwd (cap := cap) mI (appW σ mQ [false])
  have x2 : (appW σ mQ [false]).seth mI ((appW σ mQ [false]).sh mI + 1) = mSt σ 0 := by
    refine WState.eq ?_ ?_ rfl rfl
    · funext j
      simp only [mSt, WState.seth_sh, appW_sh, WState.sets_sh, Function.update_apply]
      by_cases hj : j = mI
      · subst hj; simp [hh, mIQ]
      · by_cases hq : j = mQ
        · subst hq; simp [hQ, mIQ.symm]
        · simp [hj, hq]
    · funext j
      simp only [mSt, WState.seth_st, appW_st, WState.sets_st, Function.update_apply]
      by_cases hq : j = mQ
      · subst hq; simp [hQ, sent]
      · simp [hq]
  rw [x2] at e2
  have e3 := loopA_spec cap _ L (mw_ones L bits mb rest) (mw_zero L bits mb rest) σ hI L 0 (by omega)
  have e4 := WExec.bwd (cap := cap) mQ (mSt σ L)
  have x4 : (mSt σ L).seth mQ ((mSt σ L).sh mQ - 1) = bSt (σ.sets mQ (sent L)) (2 * L + 1) L := by
    rw [mSt_shQ, Nat.add_sub_cancel]
    simp only [mSt, bSt, wseth_seth]
  rw [x4] at e4
  have e5 := loopB_spec cap L (σ.sets mQ (sent L)) (by simp only [WState.sets_st, Function.update_self]) L
    (2 * L + 1) le_rfl
  have e6 := WExec.fwd (cap := cap) mI (bSt (σ.sets mQ (sent L)) (2 * L + 1 + 2 * L) 0)
  have e7 := WExec.fwd (cap := cap) mI ((bSt (σ.sets mQ (sent L)) (2 * L + 1 + 2 * L) 0).seth mI
    ((bSt (σ.sets mQ (sent L)) (2 * L + 1 + 2 * L) 0).sh mI + 1))
  have x7 : ((bSt (σ.sets mQ (sent L)) (2 * L + 1 + 2 * L) 0).seth mI
      ((bSt (σ.sets mQ (sent L)) (2 * L + 1 + 2 * L) 0).sh mI + 1)).seth mI
      (((bSt (σ.sets mQ (sent L)) (2 * L + 1 + 2 * L) 0).seth mI
      ((bSt (σ.sets mQ (sent L)) (2 * L + 1 + 2 * L) 0).sh mI + 1)).sh mI + 1) =
      bSt (σ.sets mQ (sent L)) (4 * L + 3) 0 := by
    refine WState.eq ?_ rfl rfl rfl
    funext j
    simp only [bSt, seth_cases]
    by_cases hj : j = mI
    · subst hj; simp only [if_true, if_neg mIQ]; omega
    · simp only [hj, if_false]
  rw [x7] at e7
  obtain ⟨X, hX⟩ : ∃ X, X = bSt (σ.sets mQ (sent L)) (4 * L + 3) 0 := ⟨_, rfl⟩
  rw [← hX] at e7
  have hXI : wbit X mI = mb := by
    unfold wbit
    rw [hX, bSt_st, bSt_shI]
    simp only [WState.sets_st]
    rw [Function.update_of_ne mIQ, hI, show 4 * L + 3 = 2 * (2 * L + 1) + 1 by ring, read_frame_odd,
      mw_mode L bits mb rest hb]
  have hXM : X.st mM = [] := by
    rw [hX, bSt_st]; simp only [WState.sets_st]; rw [Function.update_of_ne mQM.symm, hM]
  have hXMh : X.sh mM = 0 := by
    rw [hX]; simp only [bSt, seth_cases, if_neg (show mM ≠ mQ by decide), if_neg (show mM ≠ mI by decide)]
    exact hh _
  have e8 : WExec cap (.ifs mI (.wr mM true) (.wr mM false)) X (X.sets mM [mb]) (1 + 1) := by
    cases hmb : mb
    · have hw := WExec.wr (cap := cap) mM false X
      rw [hXM, hXMh] at hw
      exact WExec.ifsF (by rw [hXI, hmb]) hw
    · have hw := WExec.wr (cap := cap) mM true X
      rw [hXM, hXMh] at hw
      exact WExec.ifsT (by rw [hXI, hmb]) hw
  have e9 := rewIn_spec cap mI mT mIT N (X.sets mM [mb])
    (by rw [WState.sets_st, Function.update_of_ne mTM, hX, bSt_st]; simp only [WState.sets_st];
        rw [Function.update_of_ne mTQ, hT])
    (by rw [WState.sets_sh, hX]; simp only [bSt, seth_cases, if_neg (show mT ≠ mQ by decide),
        if_neg (show mT ≠ mI by decide)]; exact hh _)
    (by rw [WState.sets_sh, hX, bSt_shI]; exact hN)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 e9)))))))) ?_ (by unfold modeCost; omega)
  rw [hX]
  refine WState.eq ?_ rfl rfl rfl
  funext j
  simp only [WState.seth_sh, WState.sets_sh, bSt, seth_cases, Function.update_apply]
  by_cases hj : j = mI
  · subst hj; simp [hh, mIQ]
  · by_cases hq : j = mQ
    · subst hq; simp [hh, mIQ.symm]
    · simp [hj, hq, hh]

end NearCubicWires.WireExponent3_5.FinalPass.Core
