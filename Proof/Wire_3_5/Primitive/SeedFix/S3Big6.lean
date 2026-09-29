import Proof.Wire_3_5.Primitive.SeedFix.S3Big5

/-! # S3, part 12: one circuit's step at one list seed

`R̂_{e'}(c,u,v) = ⋀_j [termOk X_j W_j R⁺_j R⁻_j]` (P3:3170-3178, `rhat4`): **`stepJ_spec`** runs circuit `j`'s step
(prepare, factor, fold, clean) from a state whose scratch reads blank: the running product `qRh` times the factor, the
table offset `qOff j` and the all-seeds table head advanced by the table length `λ_j`, every other register and head
as found, every word and point stream unchanged, the scratch reading blank again.

Paper quantity of the main type: `R̂`'s running product times circuit `j`'s factor at the seed. -/

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

theorem fsJ_ne2 (j : Fin 4) (i : Fin 14) : fsJ j i ≠ bW (wIdx 2 j) := by
  fin_cases j <;> fin_cases i <;> decide

theorem qS_ne_qOff (q : Fin 32) (j : Fin 4) : qS q ≠ qOff j := fun h => by
  have := congrArg Fin.val h
  simp only [qS, qOff] at this
  omega

/-- **Circuit `j`'s step at the current seed.** -/
def stepJ (j : Fin 4) : BM := .seq (prepJ j) (.seq (circJ j) (.seq foldJ (cleanJ j)))

theorem stepJ_spec (cap : ℕ) (Pl : FlatListParams) (el : Pl.FlatSeed) {n : ℕ} (G : List (NormalizedThresholdGate n))
    (c u v : BitInput n) (W : List Bool) (j : Fin 4) (ω : BS)
    (hG : ω.st (bW (wIdx 0 j)) = gatesW (tabH G) G) (hTop : ω.st (bW (wIdx 1 j)) = frame W)
    (hT : ω.st (bW (wIdx 3 j)) = levelWord Pl.M Pl.base.J Pl.base.W (fun _ => List.replicate G.length false))
    (hC : ω.st bC = frameP (List.ofFn c) ++ [false]) (hU : ω.st bU = frameP (List.ofFn u) ++ [false])
    (hV : ω.st bV = frameP (List.ofFn v) ++ [false])
    (htab : ∀ p, p < (flatTable Pl el G.length).length →
      readTapeBit (ω.st (bW (wIdx 2 j))) (ω.sh (bW (wIdx 2 j)) + p) = readTapeBit (flatTable Pl el G.length) p)
    (hn0 : ω.val (qN (nIdx 0 j)) = G.length) (hn1 : ω.val (qN (nIdx 1 j)) = tabH G)
    (hn2 : ω.val (qN (nIdx 2 j)) = (flatTable Pl el G.length).length)
    (hn3 : ω.val (qN (nIdx 3 j)) =
      (levelWord Pl.M Pl.base.J Pl.base.W (fun _ => List.replicate G.length false)).length)
    (hsc : ∀ i : Fin 28, 19 ≤ i.val → RdEq (ω.st i) []) (hscs : ∀ i : Fin 28, 19 ≤ i.val → ω.sh i = 0)
    (hsh : ∀ i : Fin 14, ω.sh (fsJ j i) = 0) (hs3 : ω.sh (bW (wIdx 3 j)) = 0)
    (hq : ∀ q : Fin 32, ω.val (qS q) = 0)
    (hct : ω.val qCt = 0) (htp : ω.val qTp = 0) (hbk : ω.val qBk = 0) (hsk : ω.val qSk = 0)
    (hrh : ω.val qRh ≤ 1) (hcap : CircCap cap Pl el n G W.length)
    (c1 : (levelWord Pl.M Pl.base.J Pl.base.W (fun _ => List.replicate G.length false)).length ≤ cap)
    (c2 : ω.val (qOff j) + (flatTable Pl el G.length).length ≤ cap) :
    ∃ τ, WExec cap (stepJ j) ω τ (costA (tabH G) n G.length Pl el + 1 + costB G.length Pl el W.length +
        200 * ((levelWord Pl.M Pl.base.J Pl.base.W (fun _ => List.replicate G.length false)).length +
          (flatTable Pl el G.length).length + tabH G + G.length) + 100) ∧
      τ.val = Function.update (Function.update ω.val (qOff j) (ω.val (qOff j) + (flatTable Pl el G.length).length))
        qRh (ω.val qRh * (termOk (cornerWord (G.map NormalizedThresholdGate.eval) c u v) W
          (flatReportFast Pl el (popBits true (cornerWord (G.map NormalizedThresholdGate.eval) c u v)))
          (flatReportFast Pl el (popBits false (cornerWord (G.map NormalizedThresholdGate.eval) c u v)))).toNat) ∧
      τ.sh = Function.update ω.sh (bW (wIdx 2 j)) (ω.sh (bW (wIdx 2 j)) + (flatTable Pl el G.length).length) ∧
      (∀ i : Fin 28, i.val < 19 → τ.st i = ω.st i) ∧ (∀ i : Fin 28, 19 ≤ i.val → RdEq (τ.st i) []) := by
  obtain ⟨T, hTd⟩ : ∃ y, y = levelWord Pl.M Pl.base.J Pl.base.W (fun _ => List.replicate G.length false) := ⟨_, rfl⟩
  obtain ⟨FT, hFTd⟩ : ∃ y, y = flatTable Pl el G.length := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ y, y = termOk (cornerWord (G.map NormalizedThresholdGate.eval) c u v) W
      (flatReportFast Pl el (popBits true (cornerWord (G.map NormalizedThresholdGate.eval) c u v)))
      (flatReportFast Pl el (popBits false (cornerWord (G.map NormalizedThresholdGate.eval) c u v))) := ⟨_, rfl⟩
  rw [← hTd] at hT hn3 c1 ⊢
  rw [← hFTd] at htab hn2 c2 ⊢
  rw [← hb]
  -- prepare
  obtain ⟨ω1, e1, v1, sh1, st1, rp, rn, rx, rz, rsp, rsm, rt5, rss, rft, cl1⟩ := prepJ_spec cap j T FT (tabH G) ω hT
    hn3 hn2 htab hn1 hsc hscs hs3 hct htp hbk hsk c1 c2 hcap.hh
  -- the factor
  obtain ⟨ω2, e2, v2, sh2, o2, bp, bn, bx, bz, bss, bt5⟩ := circJ_spec cap Pl el G c u v W j ω1
    (by rw [st1 _ (bW_lt _)]; exact hG) (by rw [st1 _ (bW_lt _)]; exact hTop)
    (by rw [st1 _ (by decide)]; exact hC) (by rw [st1 _ (by decide)]; exact hU) (by rw [st1 _ (by decide)]; exact hV)
    rp rn rx rz rsp rsm (by rw [← hTd]; exact rt5) rss (by rw [← hFTd]; exact rft)
    (fun i => by rw [sh1, Function.update_of_ne (fsJ_ne2 j i)]; exact hsh i)
    (fun q _ => by rw [v1, Function.update_of_ne (qS_ne_qOff q j)]; exact hq q) hcap
  rw [← hb, ← qKo_eq] at v2
  rw [← hTd] at bt5
  -- the fold
  obtain ⟨ω3, e3, v3, sh3, st3, cl3⟩ := foldJ_spec cap b ω2 (by rw [v2, Function.update_self])
    (by rw [v2, Function.update_of_ne (by decide), v1, Function.update_of_ne (ne_qOff j (by decide))]; exact hrh)
    hcap.one
  have hv3 : ∀ r, r ≠ qRh → r ≠ qKo → r ≠ qOff j → ω3.val r = ω.val r := fun r h1 h2 h3 => by
    rw [v3, Function.update_of_ne h1, Function.update_of_ne h2, v2, Function.update_of_ne h2, v1,
      Function.update_of_ne h3]
  have hsh3 : ω3.sh = Function.update ω.sh (bW (wIdx 2 j)) (ω.sh (bW (wIdx 2 j)) + FT.length) := by
    rw [sh3, sh2, sh1]
  have hqN : ∀ i : Fin 18, ω3.val (qN i) = ω.val (qN i) := fun i =>
    hv3 _ (qN_ne i (by decide)) (qN_ne i (by decide)) (ne_qOff j (by have := qN_lt i; omega))
  -- clean
  obtain ⟨ω4, e4, v4, sh4, lo4, sc4, cl4⟩ := cleanJ_spec cap j (tabH G) G.length T.length FT.length ω3
    (by rw [hqN]; exact hn1) (by rw [hqN]; exact hn0) (by rw [hqN]; exact hn3) (by rw [hqN]; exact hn2)
    (fun i hi => by rw [hsh3, Function.update_of_ne (bW_ne _ hi).symm]; exact hscs i hi)
    (by rw [hv3 _ (by decide) (by decide) (ne_qOff j (by decide))]; exact hct)
    (by rw [hv3 _ (by decide) (by decide) (ne_qOff j (by decide))]; exact htp)
    (by rw [hv3 _ (by decide) (by decide) (ne_qOff j (by decide))]; exact hbk)
    (fun p hp => by rw [st3]; exact bp p hp) (fun p hp => by rw [st3]; exact bn p hp)
    (fun p hp => by rw [st3]; exact bx p hp) (fun p hp => by rw [st3]; exact bt5 p hp)
    (fun p hp => by
      rw [st3, o2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rft p]
      exact read_ge FT p hp)
    (by rw [st3]; exact bz) (by rw [st3]; exact bss)
    (by rw [st3, o2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact rsm)
    (fun p hp => by
      rw [st3, o2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rsp p]
      exact read_ge [true] p hp)
    hcap.hh hcap.oo c1 (by omega)
  refine ⟨ω4, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) (by omega), ?_, by rw [sh4, hsh3],
    fun i hi => ?_, sc4⟩
  · rw [v4, v3, v2, v1]
    funext r
    by_cases h1 : r = qRh
    · subst h1
      rw [Function.update_self, Function.update_self, Function.update_of_ne (by decide),
        Function.update_of_ne (ne_qOff j (by decide))]
    · rw [Function.update_of_ne h1, Function.update_of_ne h1]
      by_cases h2 : r = qKo
      · subst h2
        rw [Function.update_self, Function.update_of_ne (ne_qOff j (by decide))]
        exact (hq 28).symm
      · rw [Function.update_of_ne h2, Function.update_of_ne h2]
  · rw [lo4 i hi, st3, o2 i (lo_ne hi (by decide)) (lo_ne hi (by decide)) (lo_ne hi (by decide)) (lo_ne hi (by decide))
      (lo_ne hi (by decide)) (lo_ne hi (by decide)), st1 i hi]

end NearCubicWires.WireExponent3_5.PrimT.S3
