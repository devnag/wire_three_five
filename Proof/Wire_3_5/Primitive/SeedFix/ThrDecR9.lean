import Proof.Wire_3_5.Primitive.SeedFix.ThrDecR8

/-! # THR decode front, RADIX part 8: the post-dock program, to the RADIX setup's entry `RsIn4`

`pbPostW = scanW 130 ; clear G ; tCW ; clear H ; tEW ; rewind 113`: from the state after the docks at a RADIX unit
(`PostIn`: the request, output, counter, data and W6's words and the payloads on their streams, the decoded numbers and
index in their registers, the RADIX marker raised), **`pbPost_run`** reaches `RadSetupB3.RsIn4` at the values
`gi, p_t, idx − Σ_{i<t} p_i, row, 2(|X_0|+|X_1|)+M, 2(|X_0|+|X_1|), n` and W6's thirteen numbers (the prime row from
the scan's item `t`), `|carriers|`, `cap_T`, `a'`, with `rRadK ≠ 0`, `rFltK = 0`.

Paper quantity of the main type: the RADIX row's setup entry (`RsIn4`, P3:2585-2623). -/

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
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.UnionMachine.ThrDec NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB3

section R9
variable (cap : ℕ) (x : ℕ)

/-- **The post-dock program.** -/
def pbPostW : WM (LNS x) LNR :=
  .seq (scanW x (sk x 130)) (.seq (clrsW gList) (.seq (tCW x) (.seq (clrsW hList) (.seq (tEW x)
    (WM.rewind (sk x 113) dK)))))

/-- **The post-dock entry.** -/
structure PostIn (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (hs xs : List ℕ) (tg : ℕ) (L : List ℕ)
    (winW modW : List Bool) (pays : Fin 4 → List Bool) (n a gi row idx : ℕ) : Prop where
  hhs : hs.length = 16
  hxs : xs.length ≤ 2
  s0 : σ.st (sk x 0) = frame w
  h0 : σ.sh (sk x 0) = 0
  s1 : σ.st (sk x 1) = out ++ [false]
  h1 : σ.sh (sk x 1) = out.length
  s2 : σ.st (sk x 2) = List.replicate j true
  h2 : σ.sh (sk x 2) = 0
  s113 : σ.st (sk x 113) = Data.unaryList (hs ++ (xs ++ [tg]))
  h113 : σ.sh (sk x 113) = (Data.unaryList ((hs ++ (xs ++ [tg])).take (16 + xs.length))).length
  sPr : σ.st (sk x 130) = Data.unaryList L
  hPr : σ.sh (sk x 130) = 0
  sWin : σ.st (sk x 131) = winW
  hWin : σ.sh (sk x 131) = 0
  sMod : σ.st (sk x 132) = modW
  hMod : σ.sh (sk x 132) = 0
  sPay : ∀ i : Fin 4, σ.st (sk x ⟨133 + i.val, by omega⟩) = pays i
  hPay : ∀ i : Fin 4, σ.sh (sk x ⟨133 + i.val, by omega⟩) = 0
  blank : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 → (k.val < 130 ∨ 136 < k.val) →
    σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0
  cell : σ.cell = false
  vN : σ.val dN = n
  vA : σ.val dA = a
  hb : ∀ k : Fin 32, k.val < 16 → σ.val (Hb k) = hs.getD k.val 0
  vXA : σ.val XA = xs.getD 0 0
  vXB : σ.val XB = xs.getD 1 0
  vMS : σ.val dMS = hs.getD 8 0
  h0v : hs.getD 0 0 = xs.length
  vRow : σ.val (H 13) = row
  vGi : σ.val (H 17) = gi
  vIdx : σ.val (H 15) = idx
  zScan : ∀ k : Fin 40, 24 ≤ k.val → k.val ≤ 37 → k.val ≠ 29 → k.val ≠ 30 → k.val ≠ 31 → k.val ≠ 32 →
    σ.val (H k) = 0
  zl : ∀ q : Fin LNR, q.val < 250 → σ.val q = 0
  zm : ∀ q : Fin LNR, 398 < q.val → q.val < 408 → σ.val q = 0
  vR : σ.val rRadK ≠ 0
  zT : σ.val TM = 0
  zK : σ.val dK = 0
  bd : ∀ q, σ.val q ≤ cap

theorem kS (σ : WState (LNS x) LNR) (τ : WState (LNS x) LNR)
    (h : ∀ r, r ≠ H 24 → r ≠ H 25 → r ≠ H 26 → r ≠ H 27 → τ.val r = σ.val r) (r : Fin LNR) (hr : r.val < 472) :
    τ.val r = σ.val r :=
  h r (H_ne 24 r hr) (H_ne 25 r hr) (H_ne 26 r hr) (H_ne 27 r hr)

/-- The block `H` cleared, the rewind count, the data tape rewound. -/
def post2W : WM (LNS x) LNR := .seq (clrsW hList) (.seq (tEW x) (WM.rewind (sk x 113) dK))

/-- **Part 1, run.** -/
theorem post1_run (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (hs xs : List ℕ) (tg : ℕ) (L : List ℕ)
    (winW modW : List Bool) (pays : Fin 4 → List Bool) (n a gi row idx : ℕ)
    (hI : PostIn cap x σ w out j hs xs tg L winW modW pays n a gi row idx) (hidx : idx < L.sum)
    (hLc : (Data.unaryList L).length + idx + 2 ≤ cap)
    (cPool : 2 * (xs.getD 0 0 + xs.getD 1 0) + hs.getD 8 0 ≤ cap) :
    ∃ τ3 c t, (∀ τ c', WExec cap (post2W x) τ3 τ c' → WExec cap (pbPostW x) σ τ (c + 1 + c')) ∧
      c ≤ UnaryPow.sq cap + 1 + (3 + 1 + ((L.length + 1) * (10 * UnaryPow.sq cap) + 1 +
        (5 * (Data.unaryList L).length + 1))) + 1 + (64 * (3 * cap + 2) + 1 + 58 * UnaryPow.sq cap) ∧
      t < L.length ∧ (L.take t).sum ≤ idx ∧ idx < (L.take (t + 1)).sum ∧
      (∀ i : Fin 20, τ3.val (PrimThrW.RadSetup.rsReg i) =
        (![gi, L.getD t 0, idx - (L.take t).sum, row, 2 * (xs.getD 0 0 + xs.getD 1 0) + hs.getD 8 0,
          2 * (xs.getD 0 0 + xs.getD 1 0), n, hs.getD 2 0, hs.getD 3 0, hs.getD 4 0, hs.getD 5 0, hs.getD 6 0,
          hs.getD 7 0, hs.getD 8 0, hs.getD 9 0, hs.getD 10 0, hs.getD 11 0, hs.getD 12 0, hs.getD 14 0,
          hs.getD 15 0] : Fin 20 → ℕ) i) ∧
      τ3.val PrimThrW.RadSetup2.rNcK = hs.getD 0 0 ∧ τ3.val PrimThrW.RadSetup2.rCapK = hs.getD 1 0 ∧
      τ3.val RadSetupB2.rAK = a ∧
      (∀ q : Fin LNR, q.val < 408 → τ3.val q = σ.val q) ∧
      (∀ q : Fin LNR, 408 ≤ q.val → q.val < 472 → (q.val < 410 ∨ 432 < q.val) → τ3.val q = 0) ∧
      τ3.st = σ.st ∧ τ3.sh (sk x 130) = 0 ∧ (∀ s, s ≠ sk x 130 → τ3.sh s = σ.sh s) ∧ τ3.cell = σ.cell ∧
      (∀ q, τ3.val q ≤ cap) := by
  have hsq := UnaryPow.sq_ge cap
  obtain ⟨τ1, c1, t, e1, c1le, tlt, tle, tlt2, v25, v24, v26, v27, v28, sh130, k1, st1, sho1, cl1⟩ :=
    scan_run cap x (sk x 130) L [] idx σ (by rw [hI.sPr, List.append_nil]) hI.hPr hI.vIdx hI.zScan hI.zT hidx hLc
  have kk1 : ∀ r : Fin LNR, r.val < 472 → τ1.val r = σ.val r := fun r hr => kS x σ τ1 k1 r hr
  have kH : ∀ k : Fin 40, k.val ≠ 24 → k.val ≠ 25 → k.val ≠ 26 → k.val ≠ 27 → τ1.val (H k) = σ.val (H k) :=
    fun k a b c d => k1 _ (hne k 24 a) (hne k 25 b) (hne k 26 c) (hne k 27 d)
  have hB1 : ∀ q, τ1.val q ≤ cap := fun q => by
    by_cases a24 : q = H 24
    · subst a24; rw [v24]; have := hI.bd (H 15); rw [hI.vIdx] at this; omega
    by_cases a25 : q = H 25
    · subst a25; rw [v25]
      have := getD_le_sum L t; have := unaryList_length_le L; omega
    by_cases a26 : q = H 26
    · subst a26; rw [v26]; omega
    by_cases a27 : q = H 27
    · subst a27; rw [v27]; omega
    rw [k1 q a24 a25 a26 a27]; exact hI.bd q
  have e2 := clrs_spec cap gList τ1 hB1
  set τ2 := zeroOut τ1 gList with hτ2
  have v2 : ∀ q : Fin LNR, (q.val < 408 ∨ 472 ≤ q.val) → τ2.val q = τ1.val q := fun q h => by
    rw [hτ2, zeroOut_val, if_neg (not_mem_gList q h)]
  have z2 : ∀ q : Fin LNR, 408 ≤ q.val → q.val < 472 → τ2.val q = 0 := fun q a b => by
    rw [hτ2, zeroOut_val, if_pos (mem_gList q a b)]
  have hB2 : ∀ q, τ2.val q ≤ cap := wexec_le cap e2 hB1
  have lo2 : ∀ q : Fin LNR, q.val < 408 → τ2.val q = σ.val q := fun q h => by
    rw [v2 q (Or.inl h), kk1 q (by omega)]
  have b : ∀ k : Fin 32, k.val < 16 → τ2.val (Hb k) = hs.getD k.val 0 := fun k hk => by
    rw [lo2 _ (by rw [Hb_val]; omega)]; exact hI.hb k hk
  have e3 := tC_run cap x τ2 gi (L.getD t 0) (idx - (L.take t).sum) row (xs.getD 0 0) (xs.getD 1 0) (hs.getD 8 0) n a
    (hs.getD 0 0) (hs.getD 1 0) (hs.getD 2 0) (hs.getD 3 0) (hs.getD 4 0) (hs.getD 5 0) (hs.getD 6 0) (hs.getD 7 0)
    (hs.getD 8 0) (hs.getD 9 0) (hs.getD 10 0) (hs.getD 11 0) (hs.getD 12 0) (hs.getD 13 0) (hs.getD 14 0)
    (hs.getD 15 0)
    (by rw [v2 _ (by rw [H_val]; omega), kH 17 (by decide) (by decide) (by decide) (by decide)]; exact hI.vGi)
    (by rw [v2 _ (by rw [H_val]; omega)]; exact v25) (by rw [v2 _ (by rw [H_val]; omega)]; exact v24)
    (by rw [v2 _ (by rw [H_val]; omega), kH 13 (by decide) (by decide) (by decide) (by decide)]; exact hI.vRow)
    (by rw [lo2 _ (by rw [rv_XA']; omega)]; exact hI.vXA) (by rw [lo2 _ (by rw [rv_XB']; omega)]; exact hI.vXB)
    (by rw [lo2 _ (by rw [rv_dMS']; omega)]; exact hI.vMS) (by rw [lo2 _ (by rw [rv_dN']; omega)]; exact hI.vN)
    (by rw [lo2 _ (by rw [rv_dA'']; omega)]; exact hI.vA)
    (b 0 (by decide)) (b 1 (by decide)) (b 2 (by decide)) (b 3 (by decide)) (b 4 (by decide)) (b 5 (by decide))
    (b 6 (by decide)) (b 7 (by decide)) (b 8 (by decide)) (b 9 (by decide)) (b 10 (by decide)) (b 11 (by decide))
    (b 12 (by decide)) (b 13 (by decide)) (b 14 (by decide)) (b 15 (by decide)) z2
    (by rw [lo2 _ (by rw [rv_TM']; omega)]; exact hI.zT) hB2 cPool
  refine ⟨_, c1 + 1 + (gList.length * (3 * cap + 2) + 1 + 58 * UnaryPow.sq cap), t,
    fun τ c' e => WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e))) (by omega), ?_, tlt, tle, tlt2,
    fun i => tCOut_rs x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i, tCOut_nc x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _, tCOut_cap x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, tCOut_a x _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, fun q h => ?_, fun q a b c => ?_, ?_, ?_, fun s hs' => ?_, ?_, wexec_le cap e3 hB2⟩
  · rw [gList_length]; omega
  · rw [tCOut_other x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q (by omega)]; exact lo2 q h
  · rw [tCOut_other x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q c]; exact z2 q a b
  · rw [tCOut_st, hτ2, zeroOut_st, st1]
  · rw [tCOut_sh, hτ2, zeroOut_sh, sh130]
  · rw [tCOut_sh, hτ2, zeroOut_sh, sho1 s hs']
  · rw [tCOut_cell, hτ2, zeroOut_cell, cl1]

/-- **Part 2, run**: `H` cleared, the rewind count, the data tape rewound from its read position. -/
theorem post2_run (σ : WState (LNS x) LNR) (pos : ℕ) (hpos : σ.val (Hb 0) + (eRegs.map σ.val).sum + 16 = pos)
    (hsh : σ.sh (sk x 113) ≤ pos) (zK : σ.val dK = 0) (zT : σ.val TM = 0) (hc : pos ≤ cap) (hB : ∀ q, σ.val q ≤ cap) :
    ∃ τ c, WExec cap (post2W x) σ τ c ∧ c ≤ 40 * (3 * cap + 2) + 1 + (UnaryPow.sq cap + 1 +
        (18 * (UnaryPow.sq cap + 1) + 1 + UnaryPow.sq cap) + 1 + (5 * pos + 1)) ∧
      (∀ q : Fin LNR, q.val < 472 → q ≠ dK → τ.val q = σ.val q) ∧ (∀ q : Fin LNR, 472 ≤ q.val → τ.val q = 0) ∧
      τ.val dK = 0 ∧ τ.st = σ.st ∧ τ.sh (sk x 113) = 0 ∧ (∀ s, s ≠ sk x 113 → τ.sh s = σ.sh s) ∧
      τ.cell = σ.cell := by
  have e1 := clrs_spec cap hList σ hB
  set τ1 := zeroOut σ hList with hτ1
  have v1 : ∀ q : Fin LNR, q.val < 472 → τ1.val q = σ.val q := fun q h => by
    rw [hτ1, zeroOut_val, if_neg (not_mem_hList q h)]
  have z1 : ∀ q : Fin LNR, 472 ≤ q.val → τ1.val q = 0 := fun q h => by rw [hτ1, zeroOut_val, if_pos (mem_hList q h)]
  have hmap : eRegs.map τ1.val = eRegs.map σ.val := by
    apply List.map_congr_left
    intro r hr
    apply v1
    simp only [eRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      (rw [h]; simp [Hb_val, rv_XA', rv_XB'])
  have e2 := tE_run cap x τ1 (by rw [v1 _ (by rw [rv_dK']; omega)]; exact zK)
    (by rw [v1 _ (by rw [rv_TM']; omega)]; exact zT)
    (by rw [hmap, v1 _ (by rw [Hb_val]; omega), hpos]; exact hc) (wexec_le cap e1 hB)
  rw [hmap, v1 _ (by rw [Hb_val]; omega), hpos] at e2
  have e3 := wrewind_spec cap (sk x 113) dK pos (τ1.setv dK pos) (by simp)
    (by simp only [WState.setv_val, Function.update_self]; exact hc)
  have hl18 : eRegs.length = 18 := rfl
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 e3), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hList_length, hl18]; try omega
  · intro q h hq
    simp only [WState.seth_val, WState.setv_val]
    rw [Function.update_of_ne hq, Function.update_of_ne hq, v1 q h]
  · intro q h
    have hq : q ≠ dK := fun e => by rw [e, rv_dK'] at h; omega
    simp only [WState.seth_val, WState.setv_val]
    rw [Function.update_of_ne hq, Function.update_of_ne hq, z1 q h]
  · simp
  · rw [WState.seth_st, WState.setv_st, WState.setv_st, hτ1, zeroOut_st]
  · rw [WState.seth_sh, Function.update_self]
    show (zeroOut σ hList).sh (sk x 113) - pos = 0
    rw [zeroOut_sh]; omega
  · intro s hs'
    rw [WState.seth_sh, Function.update_of_ne hs', WState.setv_sh, WState.setv_sh, hτ1, zeroOut_sh]
  · rw [WState.seth_cell, WState.setv_cell, WState.setv_cell, hτ1, zeroOut_cell]

/-- **The post-dock program, run**: `RsIn4` at the prime row of the scan's item. -/
theorem pbPost_run (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (hs xs : List ℕ) (tg : ℕ) (L : List ℕ)
    (winW modW : List Bool) (pays : Fin 4 → List Bool) (n a gi row idx : ℕ)
    (hI : PostIn cap x σ w out j hs xs tg L winW modW pays n a gi row idx) (hidx : idx < L.sum)
    (hLc : (Data.unaryList L).length + idx + 2 ≤ cap)
    (cPool : 2 * (xs.getD 0 0 + xs.getD 1 0) + hs.getD 8 0 ≤ cap)
    (cPos : hs.sum + (xs.getD 0 0 + xs.getD 1 0) + 16 + xs.length ≤ cap) :
    ∃ τ c t, WExec cap (pbPostW x) σ τ c ∧
      c ≤ UnaryPow.sq cap + 1 + (3 + 1 + ((L.length + 1) * (10 * UnaryPow.sq cap) + 1 +
        (5 * (Data.unaryList L).length + 1))) + 1 + (64 * (3 * cap + 2) + 1 + 58 * UnaryPow.sq cap) + 1 +
        (40 * (3 * cap + 2) + 1 + (UnaryPow.sq cap + 1 + (18 * (UnaryPow.sq cap + 1) + 1 + UnaryPow.sq cap) + 1 +
        (5 * cap + 1))) ∧
      t < L.length ∧ (L.take t).sum ≤ idx ∧ idx < (L.take (t + 1)).sum ∧ τ.val rRadK ≠ 0 ∧ τ.val rFltK = 0 ∧
      RsIn4 x τ w out j (Data.unaryList (hs ++ (xs ++ [tg])))
        (![gi, L.getD t 0, idx - (L.take t).sum, row, 2 * (xs.getD 0 0 + xs.getD 1 0) + hs.getD 8 0,
          2 * (xs.getD 0 0 + xs.getD 1 0), n, hs.getD 2 0, hs.getD 3 0, hs.getD 4 0, hs.getD 5 0, hs.getD 6 0,
          hs.getD 7 0, hs.getD 8 0, hs.getD 9 0, hs.getD 10 0, hs.getD 11 0, hs.getD 12 0, hs.getD 14 0,
          hs.getD 15 0] : Fin 20 → ℕ) (Data.unaryList L) winW modW xs.length (hs.getD 1 0) pays a := by
  obtain ⟨τ3, c3, t, comp, c3le, tlt, tle, tlt2, vrs, vnc, vcap, va, lo3, zg3, st3, sh3a, sh3, cl3, hB3⟩ :=
    post1_run cap x σ w out j hs xs tg L winW modW pays n a gi row idx hI hidx hLc cPool
  have h130a : sk x 130 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have bb : ∀ k : Fin 32, k.val < 16 → τ3.val (Hb k) = hs.getD k.val 0 := fun k hk => by
    rw [lo3 _ (by rw [Hb_val]; omega)]; exact hI.hb k hk
  have b0 : τ3.val (Hb 0) = hs.getD 0 0 := bb 0 (by decide)
  have b1 : τ3.val (Hb 1) = hs.getD 1 0 := bb 1 (by decide)
  have b2 : τ3.val (Hb 2) = hs.getD 2 0 := bb 2 (by decide)
  have b3 : τ3.val (Hb 3) = hs.getD 3 0 := bb 3 (by decide)
  have b4 : τ3.val (Hb 4) = hs.getD 4 0 := bb 4 (by decide)
  have b5 : τ3.val (Hb 5) = hs.getD 5 0 := bb 5 (by decide)
  have b6 : τ3.val (Hb 6) = hs.getD 6 0 := bb 6 (by decide)
  have b7 : τ3.val (Hb 7) = hs.getD 7 0 := bb 7 (by decide)
  have b8 : τ3.val (Hb 8) = hs.getD 8 0 := bb 8 (by decide)
  have b9 : τ3.val (Hb 9) = hs.getD 9 0 := bb 9 (by decide)
  have b10 : τ3.val (Hb 10) = hs.getD 10 0 := bb 10 (by decide)
  have b11 : τ3.val (Hb 11) = hs.getD 11 0 := bb 11 (by decide)
  have b12 : τ3.val (Hb 12) = hs.getD 12 0 := bb 12 (by decide)
  have b13 : τ3.val (Hb 13) = hs.getD 13 0 := bb 13 (by decide)
  have b14 : τ3.val (Hb 14) = hs.getD 14 0 := bb 14 (by decide)
  have b15 : τ3.val (Hb 15) = hs.getD 15 0 := bb 15 (by decide)
  have bXA : τ3.val XA = xs.getD 0 0 := by rw [lo3 _ (by rw [rv_XA']; omega)]; exact hI.vXA
  have bXB : τ3.val XB = xs.getD 1 0 := by rw [lo3 _ (by rw [rv_XB']; omega)]; exact hI.vXB
  have hs16 := sum16 hs hI.hhs
  have h0v := hI.h0v
  have hsum : τ3.val (Hb 0) + (eRegs.map τ3.val).sum + 16 = hs.sum + (xs.getD 0 0 + xs.getD 1 0) + 16 + xs.length := by
    simp only [eRegs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, bXA, bXB]
    omega
  have hsh113 : τ3.sh (sk x 113) ≤ hs.sum + (xs.getD 0 0 + xs.getD 1 0) + 16 + xs.length := by
    rw [sh3 _ (fun e => h130a e.symm), hI.h113, sh113_eq hs xs tg hI.hhs hI.hxs]
  obtain ⟨τ, c4, e4, c4le, lo4, hi4, dK4, st4, sh4a, sh4, cl4⟩ :=
    post2_run cap x τ3 _ hsum hsh113 (by rw [lo3 _ (by rw [rv_dK']; omega)]; exact hI.zK)
      (by rw [lo3 _ (by rw [rv_TM']; omega)]; exact hI.zT) cPos hB3
  have lo : ∀ q : Fin LNR, q.val < 408 → q ≠ dK → τ.val q = σ.val q := fun q h hq => by
    rw [lo4 q (by omega) hq, lo3 q h]
  have shk : ∀ k : Fin 161, k.val ≠ 113 → k.val ≠ 130 → τ.sh (sk x k) = σ.sh (sk x k) := fun k a b => by
    rw [sh4 _ (fun e => a (by rw [sk_inj x e]; rfl)), sh3 _ (fun e => b (by rw [sk_inj x e]; rfl))]
  refine ⟨τ, _, t, comp τ c4 e4, ?_, tlt, tle, tlt2, ?_, ?_, ?_⟩
  · omega
  · rw [lo _ (by decide) (by decide)]; exact hI.vR
  · rw [lo _ (by decide) (by decide)]; exact hI.zm _ (by decide) (by decide)
  · exact
    { s0 := by rw [st4, st3]; exact hI.s0
      h0 := by rw [shk 0 (by decide) (by decide)]; exact hI.h0
      s1 := by rw [st4, st3]; exact hI.s1
      h1 := by rw [shk 1 (by decide) (by decide)]; exact hI.h1
      s2 := by rw [st4, st3]; exact hI.s2
      h2 := by rw [shk 2 (by decide) (by decide)]; exact hI.h2
      s113 := by rw [st4, st3]; exact hI.s113
      h113 := sh4a
      sPr := by show τ.st (sk x 130) = _; rw [st4, st3]; exact hI.sPr
      hPr := by show τ.sh (sk x 130) = 0; rw [sh4 _ h130a, sh3a]
      sWin := by show τ.st (sk x 131) = _; rw [st4, st3]; exact hI.sWin
      hWin := by show τ.sh (sk x 131) = 0; rw [shk 131 (by decide) (by decide)]; exact hI.hWin
      sMod := by show τ.st (sk x 132) = _; rw [st4, st3]; exact hI.sMod
      hMod := by show τ.sh (sk x 132) = 0; rw [shk 132 (by decide) (by decide)]; exact hI.hMod
      sPay := fun i => by
        show τ.st (sk x ⟨133 + i.val, by omega⟩) = _
        rw [st4, st3]; exact hI.sPay i
      hPay := fun i => by
        have hi := i.isLt
        show τ.sh (sk x ⟨133 + i.val, by omega⟩) = 0
        rw [shk ⟨133 + i.val, by omega⟩ (by simp; omega) (by simp; omega)]; exact hI.hPay i
      blank := fun k a0 a1 a2 a3 a4 a5 a6 a7 => by
        refine ⟨by rw [st4, st3]; exact (hI.blank k a0 a1 a2 a3 (by omega)).1, ?_⟩
        rw [shk k a3 a4]; exact (hI.blank k a0 a1 a2 a3 (by omega)).2
      vals := fun i => by
        have hi := i.isLt
        rw [lo4 _ (by simp [PrimThrW.RadSetup.rsReg]; omega) (fun e => by
          have := congrArg Fin.val e; simp [PrimThrW.RadSetup.rsReg, rv_dK'] at this; omega), vrs i]
      vNc := by rw [lo4 _ (by decide) (by decide), vnc, hI.h0v]
      vCap := by rw [lo4 _ (by decide) (by decide), vcap]
      vA := by rw [lo4 _ (by decide) (by decide), va]
      zero := fun r hr => by
        by_cases hK : r = dK
        · subst hK; exact dK4
        rcases hr with h | h | h
        · rw [lo r (by omega) hK]; exact hI.zl r h
        · by_cases h8 : r.val < 408
          · rw [lo r h8 hK]; exact hI.zm r (by omega) h8
          · rw [lo4 r (by omega) hK]; exact zg3 r (by omega) (by omega) (by omega)
        · by_cases h4 : 472 ≤ r.val
          · exact hi4 r h4
          · rw [lo4 r (by omega) hK]; exact zg3 r (by omega) (by omega) (by omega)
      cell := by rw [cl4, cl3]; exact hI.cell }

end R9

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
