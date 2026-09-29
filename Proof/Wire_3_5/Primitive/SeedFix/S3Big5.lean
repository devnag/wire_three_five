import Proof.Wire_3_5.Primitive.SeedFix.S3Big4

/-! # S3, part 11: one circuit's factor folded into `R̂` at one list seed

`R̂_{e'}(c,u,v)` is the AND over the tuple's circuits of their factors `[termOk X W R⁺ R⁻]` (P3:3170-3178,
`rhat4`). One circuit's step at the current seed: prepare the scratch (`prepJ`), run the factor (`circJ`), fold it
into the running product (`foldJ`: `qRh := qRh·[factor]`), blank the scratch again (`cleanJ`, loop-safe scratch). **`stepJ_spec`**: the running product times the factor, the table offset and head advanced by the
table length, every other register and head as found, every word and point stream unchanged, the scratch blank.

Paper quantity of the main type: `R̂`'s running product times one circuit's factor. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Term NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimT.ReadEq

/-! ## The fold -/

/-- `qRh := qRh·[factor]`, the factor register back to `0`. -/
def foldJ : BM := .ifr qKo (.dec qKo) (WM.clear qRh)

theorem foldJ_spec (cap : ℕ) (b : Bool) (ω : BS) (hk : ω.val qKo = b.toNat) (hr : ω.val qRh ≤ 1) (hc : 1 ≤ cap) :
    ∃ τ, WExec cap foldJ ω τ 5 ∧
      τ.val = Function.update (Function.update ω.val qKo 0) qRh (ω.val qRh * b.toNat) ∧ τ.sh = ω.sh ∧
      τ.st = ω.st ∧ τ.cell = ω.cell := by
  cases b with
  | true =>
    have e := WExec.ifrT (Q := WM.clear qRh) (by rw [hk]; decide) (WExec.dec (cap := cap) qKo ω (by rw [hk]; exact hc))
    refine ⟨_, WExec.mono e (by omega), ?_, rfl, rfl, rfl⟩
    funext r
    simp only [WState.setv_val]
    by_cases h1 : r = qRh
    · subst h1
      rw [Function.update_self, Function.update_of_ne (by decide), Bool.toNat_true, Nat.mul_one]
    · rw [Function.update_of_ne h1]
      by_cases h2 : r = qKo
      · subst h2; rw [Function.update_self, Function.update_self, hk]; rfl
      · rw [Function.update_of_ne h2, Function.update_of_ne h2]
  | false =>
    have e := WExec.ifrF (P := WM.dec qKo) hk (wclear_spec cap qRh (ω.val qRh) ω rfl (by omega))
    refine ⟨_, WExec.mono e (by omega), ?_, rfl, rfl, rfl⟩
    funext r
    simp only [WState.setv_val]
    by_cases h1 : r = qRh
    · subst h1
      rw [Function.update_self, Function.update_self, Bool.toNat_false, Nat.mul_zero]
    · rw [Function.update_of_ne h1, Function.update_of_ne h1]
      by_cases h2 : r = qKo
      · subst h2; rw [Function.update_self, hk]; rfl
      · rw [Function.update_of_ne h2]

/-! ## The cleanup -/

/-- **Blank circuit `j`'s scratch again.** -/
def cleanJ (j : Fin 4) : BM :=
  .seq (blankN bPos (qN (nIdx 1 j)) qCt qTp qBk 2)
    (.seq (blankN bNeg (qN (nIdx 1 j)) qCt qTp qBk 2)
      (.seq (blankN bX (qN (nIdx 0 j)) qCt qTp qBk 8)
        (.seq (blankN bT5 (qN (nIdx 3 j)) qCt qTp qBk 1)
          (.seq (blankN bFT (qN (nIdx 2 j)) qCt qTp qBk 1) (.wr bSp false)))))

theorem cleanJ_spec (cap : ℕ) (j : Fin 4) (h g μ lam : ℕ) (ω : BS)
    (hh : ω.val (qN (nIdx 1 j)) = h) (hg : ω.val (qN (nIdx 0 j)) = g) (hμ : ω.val (qN (nIdx 3 j)) = μ)
    (hl : ω.val (qN (nIdx 2 j)) = lam) (hscs : ∀ i : Fin 28, 19 ≤ i.val → ω.sh i = 0)
    (hct : ω.val qCt = 0) (htp : ω.val qTp = 0) (hbk : ω.val qBk = 0)
    (bpos : ∀ p, 2 * h ≤ p → readTapeBit (ω.st bPos) p = false)
    (bneg : ∀ p, 2 * h ≤ p → readTapeBit (ω.st bNeg) p = false)
    (bx : ∀ p, 8 * g ≤ p → readTapeBit (ω.st bX) p = false)
    (bt5 : ∀ p, μ ≤ p → readTapeBit (ω.st bT5) p = false)
    (bft : ∀ p, lam ≤ p → readTapeBit (ω.st bFT) p = false)
    (bz : RdEq (ω.st bZ) []) (bss : RdEq (ω.st bSS) []) (bsm : RdEq (ω.st bSm) [])
    (bsp : ∀ p, 1 ≤ p → readTapeBit (ω.st bSp) p = false)
    (c1 : 2 * h ≤ cap) (c2 : 8 * g ≤ cap) (c3 : μ ≤ cap) (c4 : lam ≤ cap) :
    ∃ τ, WExec cap (cleanJ j) ω τ (96 * h + 126 * g + 35 * μ + 35 * lam + 41) ∧ τ.val = ω.val ∧ τ.sh = ω.sh ∧
      (∀ i : Fin 28, i.val < 19 → τ.st i = ω.st i) ∧ (∀ i : Fin 28, 19 ≤ i.val → RdEq (τ.st i) []) ∧
      τ.cell = ω.cell := by
  obtain ⟨ω1, e1, r1, o1, sh1, v1, cl1⟩ := blankN_spec cap bPos (qN (nIdx 1 j)) qCt qTp qBk 2 (qN_ne _ (by decide))
    (qN_ne _ (by decide)) (by decide) (by decide) ω hct htp hbk (hscs bPos (by decide)) (by rw [hh]; omega)
    (by rw [hh]; omega)
  obtain ⟨ω2, e2, r2, o2, sh2, v2, cl2⟩ := blankN_spec cap bNeg (qN (nIdx 1 j)) qCt qTp qBk 2 (qN_ne _ (by decide))
    (qN_ne _ (by decide)) (by decide) (by decide) ω1 (by rw [v1]; exact hct) (by rw [v1]; exact htp)
    (by rw [v1]; exact hbk) (by rw [sh1]; exact hscs bNeg (by decide)) (by rw [v1, hh]; omega)
    (by rw [v1, hh]; omega)
  obtain ⟨ω3, e3, r3, o3, sh3, v3, cl3⟩ := blankN_spec cap bX (qN (nIdx 0 j)) qCt qTp qBk 8 (qN_ne _ (by decide))
    (qN_ne _ (by decide)) (by decide) (by decide) ω2 (by rw [v2, v1]; exact hct) (by rw [v2, v1]; exact htp)
    (by rw [v2, v1]; exact hbk) (by rw [sh2, sh1]; exact hscs bX (by decide)) (by rw [v2, v1, hg]; omega)
    (by rw [v2, v1, hg]; omega)
  obtain ⟨ω4, e4, r4, o4, sh4, v4, cl4⟩ := blankN_spec cap bT5 (qN (nIdx 3 j)) qCt qTp qBk 1 (qN_ne _ (by decide))
    (qN_ne _ (by decide)) (by decide) (by decide) ω3 (by rw [v3, v2, v1]; exact hct)
    (by rw [v3, v2, v1]; exact htp) (by rw [v3, v2, v1]; exact hbk)
    (by rw [sh3, sh2, sh1]; exact hscs bT5 (by decide)) (by rw [v3, v2, v1, hμ]; omega)
    (by rw [v3, v2, v1, hμ]; omega)
  obtain ⟨ω5, e5, r5, o5, sh5, v5, cl5⟩ := blankN_spec cap bFT (qN (nIdx 2 j)) qCt qTp qBk 1 (qN_ne _ (by decide))
    (qN_ne _ (by decide)) (by decide) (by decide) ω4 (by rw [v4, v3, v2, v1]; exact hct)
    (by rw [v4, v3, v2, v1]; exact htp) (by rw [v4, v3, v2, v1]; exact hbk)
    (by rw [sh4, sh3, sh2, sh1]; exact hscs bFT (by decide)) (by rw [v4, v3, v2, v1, hl]; omega)
    (by rw [v4, v3, v2, v1, hl]; omega)
  have e6 := WExec.wr (cap := cap) bSp false ω5
  obtain ⟨ω6, hω6⟩ : ∃ y, y = ω5.sets bSp (writeTapeBit (ω5.st bSp) (ω5.sh bSp) false) := ⟨_, rfl⟩
  rw [← hω6] at e6
  have a1 : ω.val (qN (nIdx 1 j)) = h := hh
  have a2 : ω1.val (qN (nIdx 1 j)) = h := by rw [v1, hh]
  have a3 : ω2.val (qN (nIdx 0 j)) = g := by rw [v2, v1, hg]
  have a4 : ω3.val (qN (nIdx 3 j)) = μ := by rw [v3, v2, v1, hμ]
  have a5 : ω4.val (qN (nIdx 2 j)) = lam := by rw [v4, v3, v2, v1, hl]
  have st6 : ∀ i, i ≠ bSp → ω6.st i = ω5.st i := fun i hi => by rw [hω6, WState.sets_st, Function.update_of_ne hi]
  have lo : ∀ i : Fin 28, i.val < 19 → ω6.st i = ω.st i := fun i hi => by
    rw [st6 i (lo_ne hi (by decide)), o5 i (lo_ne hi (by decide)), o4 i (lo_ne hi (by decide)),
      o3 i (lo_ne hi (by decide)), o2 i (lo_ne hi (by decide)), o1 i (lo_ne hi (by decide))]
  refine ⟨ω6, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) (by omega),
    by rw [hω6, WState.sets_val, v5, v4, v3, v2, v1], by rw [hω6, WState.sets_sh, sh5, sh4, sh3, sh2, sh1], lo,
    fun i hi => ?_, by rw [hω6, WState.sets_cell, cl5, cl4, cl3, cl2, cl1]⟩
  rcases i with ⟨v, hv⟩
  simp only at hi
  intro p
  rw [read_nil]
  interval_cases v
  · show readTapeBit (ω6.st bPos) p = false
    rw [st6 _ (by decide), o5 _ (by decide), o4 _ (by decide), o3 _ (by decide), o2 _ (by decide), r1 p]
    split_ifs with hp
    · rfl
    · exact bpos p (by omega)
  · show readTapeBit (ω6.st bNeg) p = false
    rw [st6 _ (by decide), o5 _ (by decide), o4 _ (by decide), o3 _ (by decide), r2 p]
    split_ifs with hp
    · rfl
    · rw [o1 _ (by decide)]; exact bneg p (by omega)
  · show readTapeBit (ω6.st bX) p = false
    rw [st6 _ (by decide), o5 _ (by decide), o4 _ (by decide), r3 p]
    split_ifs with hp
    · rfl
    · rw [o2 _ (by decide), o1 _ (by decide)]; exact bx p (by omega)
  · show readTapeBit (ω6.st bZ) p = false
    rw [st6 _ (by decide), o5 _ (by decide), o4 _ (by decide), o3 _ (by decide), o2 _ (by decide), o1 _ (by decide),
      bz p, read_nil]
  · show readTapeBit (ω6.st bSp) p = false
    have hsp : ω5.sh bSp = 0 := by rw [sh5, sh4, sh3, sh2, sh1]; exact hscs bSp (by decide)
    rw [hω6, WState.sets_st, Function.update_self, hsp, readTapeBit_write]
    split_ifs with hp
    · rfl
    · rw [o5 _ (by decide), o4 _ (by decide), o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]
      exact bsp p (by omega)
  · show readTapeBit (ω6.st bSm) p = false
    rw [st6 _ (by decide), o5 _ (by decide), o4 _ (by decide), o3 _ (by decide), o2 _ (by decide), o1 _ (by decide),
      bsm p, read_nil]
  · show readTapeBit (ω6.st bT5) p = false
    rw [st6 _ (by decide), o5 _ (by decide), r4 p]
    split_ifs with hp
    · rfl
    · rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact bt5 p (by omega)
  · show readTapeBit (ω6.st bSS) p = false
    rw [st6 _ (by decide), o5 _ (by decide), o4 _ (by decide), o3 _ (by decide), o2 _ (by decide), o1 _ (by decide),
      bss p, read_nil]
  · show readTapeBit (ω6.st bFT) p = false
    rw [st6 _ (by decide), r5 p]
    split_ifs with hp
    · rfl
    · rw [o4 _ (by decide), o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact bft p (by omega)

end NearCubicWires.WireExponent3_5.PrimT.S3
