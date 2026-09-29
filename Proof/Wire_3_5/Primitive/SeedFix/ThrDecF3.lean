import Proof.Wire_3_5.Primitive.SeedFix.ThrDecF2

/-! # THR decode front, assembly part 3: the register program's run, all three unit kinds

**`W1_run`**: from the unit's fresh cell, `W1`'s run at every unit `j`: past the call's units (`j ≥ TOT`, the capped
test's flag down) nothing is printed; below them the index and the branch (`W1b_run`). The three outcomes of
`ThrDec.ThrDecOut` (FILTER: `FsIn2`; RADIX: the pre-dock outcome `PreOK`; the rest: `IdleAt`).

* `capUp'` (a word program's run at every larger capacity), `pos_factors`, `rowOfU_le`, `FNeed` (the front's
  capacity needs), `W1Cost`, **`W1_run`**.

Paper quantity of the main type: the THR tape's unit `j` (P3:3011-3016). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.UnionMachine.ThrDec

/-- A word program's run at every larger capacity. -/
theorem capUp' {ns nr : ℕ} {cap cap' : ℕ} (hc : cap ≤ cap') {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ}
    (h : WExec cap P σ τ n) : WExec cap' P σ τ n := by
  induction h with
  | skip σ => exact WExec.skip σ
  | inc r σ hv => exact WExec.inc r σ (by omega)
  | dec r σ hv => exact WExec.dec r σ (by omega)
  | fwd i σ => exact WExec.fwd i σ
  | bwd i σ => exact WExec.bwd i σ
  | wr i b σ => exact WExec.wr i b σ
  | setc v σ => exact WExec.setc v σ
  | seq _ _ ih1 ih2 => exact WExec.seq ih1 ih2
  | ifrT h _ ih => exact WExec.ifrT h ih
  | ifrF h _ ih => exact WExec.ifrF h ih
  | ifsT h _ ih => exact WExec.ifsT h ih
  | ifsF h _ ih => exact WExec.ifsF h ih
  | whrF h => exact WExec.whrF h
  | whrT h _ _ ih1 ih2 => exact WExec.whrT h ih1 ih2
  | whsF h => exact WExec.whsF h
  | whsT h _ _ ih1 ih2 => exact WExec.whsT h ih1 ih2
  | mono _ hle ih => exact WExec.mono ih hle

theorem pos_factors (a b c d e : ℕ) (h : 0 < a * b * c * d * e) : 0 < b ∧ 0 < c ∧ 0 < d := by
  refine ⟨Nat.pos_of_ne_zero fun hb => by simp [hb] at h, Nat.pos_of_ne_zero fun hc => by simp [hc] at h,
    Nat.pos_of_ne_zero fun hd => by simp [hd] at h⟩

/-- A request unit's row is at most `|carriers|` (the RADIX row). -/
theorem rowOfU_le (TOT nc j : ℕ) (h : IsReqU TOT nc j) : rowOfU nc j ≤ nc := by
  obtain ⟨-, h1, h2, -⟩ := h
  unfold rowOfU
  rw [thrEU_eq] at h1 h2 ⊢
  have := Nat.div_lt_of_lt_mul (m := j % ((nc + 1) * (0 + 3) + 2) - 1) (n := 3) (k := nc + 1) (by simp at h2 ⊢; omega)
  omega

section F3
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp) (cap : ℕ) (x : ℕ)

/-- **The front's capacity needs** (at the virtual capacity the register programs run at). -/
structure FNeed (w : List Bool) (n : ℕ) (codes cc : List ℕ) (Kb cr fe : ℕ) (hs xs : List ℕ) (tg : ℕ) (FP : GapParams)
    (kh : ℕ) (L : List ℕ) : Prop where
  tn : TNeed cap w n codes cc Kb cr fe hs xs tg FP kh
  tot : 2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * kh) * ((xs.length + 1) * 3 + 2) + 2 ≤ cap
  idx : 2 * (2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * kh) * ((xs.length + 1) * 3 + 2)) +
    ((xs.length + 1) * 3 + 2) + 2 ^ (2 * kh) + hs.getD 6 0 + hs.getD 2 0 + xs.length + 20 ≤ cap
  fil : 4 * 2 ^ (2 * kh) + 2 * (xs.getD 0 0 + xs.getD 1 0) + hs.getD 8 0 + 1 ≤ cap
  preA : w.length + (n + 1) ^ 26 * 2 + n + hs.getD 1 0 + 42 ≤ cap
  preC : N.Cn ≤ cap
  preD : (n + hs.getD 1 0 + 1) ^ N.Dn ≤ cap
  preB : tV w.length n (hs.getD 1 0) N.Cn N.Dn + n + hs.getD 1 0 + hs.getD 0 0 + 42 ≤ cap
  post : (Data.unaryList L).length + hs.getD 6 0 + 2 ≤ cap
  pool : 2 * (xs.getD 0 0 + xs.getD 1 0) + hs.getD 8 0 ≤ cap
  pos : hs.sum + (xs.getD 0 0 + xs.getD 1 0) + 16 + xs.length ≤ cap

/-- The register program's cost bound. -/
def W1Cost (n a nc Kb cr fe cap TOT V capT ncar Dn : ℕ) : ℕ :=
  tNCost n a nc Kb cr fe cap + 1 + (UnaryPow.sq cap + 16 * TOT + 16) + 1 +
    (1 + 1 + (30 * UnaryPow.sq cap + 1 + 26 * UnaryPow.sq cap + 1 + (finCost cap V ncar capT Dn + 12)) + 1)

/-- **The register program before the docks, run.** -/
theorem W1_run (hx : dX T N ≤ x) (cr fe : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n)
    (w out : List Bool) (j : ℕ) (codes cc : List ℕ) (tl : List Bool) (Kb : ℕ) (hw : w = Data.reqW P.n true codes cc tl)
    (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb) (hs xs : List ℕ) (tg : ℕ) (hhs : hs.length = 16) (hxs : xs.length ≤ 2)
    (h0v : hs.getD 0 0 = xs.length) (hcc : cc.length = xs.length) (FP : GapParams) (hPc : FP.cap = hs.getD 1 0)
    (hPl : FP.len = 2 * (P.n + 1) ^ 26) (hPe : FP.errExp = fe * Nat.clog 2 (P.n + 2)) (hPc1 : 1 ≤ FP.cap)
    (L : List ℕ) (hF : FNeed N cap w P.n codes cc Kb cr fe hs xs tg FP (P.s * (P.r / 2)) L)
    (rq : ℕ → ℕ → ℕ → List Bool) :
    ∃ τ c, WExec cap (W1 T N x hx cr fe) (CellLoopD.blankCellD x w out j (Data.unaryList (hs ++ (xs ++ [tg])))) τ c ∧
      c ≤ W1Cost P.n codes.length cc.length Kb cr fe cap
        (2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2))
        (tV w.length P.n (hs.getD 1 0) N.Cn N.Dn) (hs.getD 1 0) (hs.getD 0 0) N.Dn ∧
      τ.st (sk x 0) = frame w ∧ τ.sh (sk x 0) = 0 ∧ τ.st (sk x 2) = List.replicate j true ∧ τ.sh (sk x 2) = 0 ∧
      (IsReqU (2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2))
          xs.length j → rowOfU xs.length j < xs.length → τ.val rRadK = 0 ∧ τ.val rFltK ≠ 0 ∧
        FsIn2 x τ w out j (Data.unaryList (hs ++ (xs ++ [tg]))) FP.len FP.cap FP.errExp
          (j / thrEU xs.length / 2 ^ (2 * (P.s * (P.r / 2))) / hs.getD 6 0 / hs.getD 2 0)
          (2 * (2 * (j / thrEU xs.length % 2 ^ (2 * (P.s * (P.r / 2))))))
          (2 * (xs.getD 0 0 + xs.getD 1 0) + hs.getD 8 0)
          (fbOff (rowOfU xs.length j) (xs.getD 0 0)) (fbL (rowOfU xs.length j) (xs.getD 0 0) (xs.getD 1 0))) ∧
      (IsReqU (2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2))
          xs.length j → rowOfU xs.length j = xs.length →
        PreOK T N cap x hx τ w out j hs xs tg P.n codes.length (j / thrEU xs.length % 2 ^ (2 * (P.s * (P.r / 2))))
          (j / thrEU xs.length / 2 ^ (2 * (P.s * (P.r / 2))) / hs.getD 6 0 % hs.getD 2 0)
          (j / thrEU xs.length / 2 ^ (2 * (P.s * (P.r / 2))) % hs.getD 6 0)
          (tV w.length P.n (hs.getD 1 0) N.Cn N.Dn) (hs.getD 1 0)) ∧
      (¬ IsReqU (2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2))
          xs.length j →
        IdleAt x τ w out (unitE (2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) *
          ((xs.length + 1) * 3 + 2)) (xs.length + 1) 0 rq j) j) := by
  set TOT := 2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2)
    with hTOT
  obtain ⟨σN, c1, e1, c1le, hT, h113⟩ := W1a_run cap x cr fe P hrP w out j codes cc tl Kb hw hKb hs xs tg hhs hxs h0v
    FP hPc hPl hPe hPc1 hF.tn hF.tot
  have n2B : sk x 2 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have n21 : sk x 2 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have n20 : sk x 2 ≠ sk x 0 := fun e => absurd (sk_inj x e) (by decide)
  have n0B : sk x 0 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have n01 : sk x 0 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have n1B : sk x 1 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have z22 : σN.val (H 22) = 0 := hT.zH 22
  by_cases hj : j < TOT
  · rw [if_pos hj] at e1
    have e2 := WExec.dec (cap := cap) (H 22) (σN.setv (H 22) 1) (by simp; have := hF.tot; omega)
    have eqN : (σN.setv (H 22) 1).setv (H 22) ((σN.setv (H 22) 1).val (H 22) - 1) = σN := by
      simp only [WState.setv_val, Function.update_self, Nat.sub_self]
      rw [wsetv_setv, ← z22, wsetv_same]
    rw [eqN] at e2
    obtain ⟨p0, p1, p2⟩ := pos_factors _ _ _ _ _ (show 0 < TOT by omega)
    have hcc' : cc.length = xs.length := hcc
    obtain ⟨τ, c3, e3, c3le, hFo, hPo, hIo⟩ := W1b_run T N cap x hx σN w out j hs xs tg P.n codes.length cc.length
      (P.s * (P.r / 2)) FP (2 ^ (2 * (P.s * (P.r / 2)))) (hs.getD 6 0) (hs.getD 2 0) TOT rq hT h113 hcc hxs h0v hj p2
      p1 p0 (by rw [hcc]; have := hF.idx; omega)
      (by
        have hr : j / thrEU cc.length % 2 ^ (2 * (P.s * (P.r / 2))) < 2 ^ (2 * (P.s * (P.r / 2))) :=
          Nat.mod_lt _ (by positivity)
        have := hF.fil; omega)
      hF.preA hF.preC hF.preD hF.preB
    rw [hcc] at hFo hPo hIo
    have e := WExec.seq e1 (WExec.ifrT (Q := .skip) (show (σN.setv (H 22) 1).val (H 22) ≠ 0 by simp)
      (WExec.seq e2 e3))
    have streams : τ.st (sk x 0) = frame w ∧ τ.sh (sk x 0) = 0 ∧ τ.st (sk x 2) = List.replicate j true ∧
        τ.sh (sk x 2) = 0 := by
      by_cases hq : IsReqU TOT xs.length j
      · have hrl := rowOfU_le TOT xs.length j hq
        by_cases hr : rowOfU xs.length j < xs.length
        · obtain ⟨-, -, hFs⟩ := hFo hq hr
          exact ⟨hFs.s0, hFs.h0, hFs.s2, hFs.h2⟩
        · have hPr := hPo hq (by omega)
          exact ⟨hPr.dock.s0, hPr.dock.h0, hPr.s2, hPr.h2⟩
      · obtain ⟨-, -, -, -, -, -, -, -, i0, i0h, i2, i2h⟩ := hIo hq
        exact ⟨i0, i0h, i2, i2h⟩
    exact ⟨τ, _, e, by unfold W1Cost; omega, streams.1, streams.2.1, streams.2.2.1, streams.2.2.2,
      hFo, hPo, hIo⟩
  · rw [if_neg hj] at e1
    have eqN : σN.setv (H 22) 0 = σN := by rw [← z22, wsetv_same]
    rw [eqN] at e1
    have e := WExec.seq e1 (WExec.ifrF (cap := cap) (P := .seq (.dec (H 22)) (.seq (idxW x)
      (tBrW x (fbTW x) (pbPreW T N x hx)))) z22 (WExec.skip σN))
    have hnq : ¬ IsReqU TOT xs.length j := fun h => hj h.1
    have s0 : σN.st (sk x 0) = frame w := by rw [hT.st]; simp [CellLoopD.blankCellD, blankCell, n0B]
    have h0 : σN.sh (sk x 0) = 0 := by rw [hT.sh _ n0B]; simp [CellLoopD.blankCellD, blankCell, n01]
    have s2 : σN.st (sk x 2) = List.replicate j true := by
      rw [hT.st]; simp [CellLoopD.blankCellD, blankCell, n2B, n20, n21]
    have h2 : σN.sh (sk x 2) = 0 := by rw [hT.sh _ n2B]; simp [CellLoopD.blankCellD, blankCell, n21]
    refine ⟨σN, _, e, ?_, s0, h0, s2, h2, fun h => absurd h hnq, fun h => absurd h hnq, fun _ => ?_⟩
    · unfold W1Cost; omega
    · have n150 : sk x 150 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
      have n151 : sk x 151 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
      have m150 : ∀ k : Fin 161, k.val ≠ 150 → sk x 150 ≠ sk x k := fun k hk e => hk (by rw [← sk_inj x e]; rfl)
      have m151 : ∀ k : Fin 161, k.val ≠ 151 → sk x 151 ≠ sk x k := fun k hk e => hk (by rw [← sk_inj x e]; rfl)
      unfold unitE; rw [if_neg hj]
      refine ⟨hT.zm _ (by decide) (by decide), hT.zm _ (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, s0, h0, s2, h2⟩
      · rw [hT.st]; simp [CellLoopD.blankCellD, blankCell, m150 0 (by decide), m150 1 (by decide),
          m150 2 (by decide), n150]
      · rw [hT.sh _ n150]; simp [CellLoopD.blankCellD, blankCell, m150 1 (by decide)]
      · rw [hT.st]; simp [CellLoopD.blankCellD, blankCell, m151 0 (by decide), m151 1 (by decide),
          m151 2 (by decide), n151]
      · rw [hT.sh _ n151]; simp [CellLoopD.blankCellD, blankCell, m151 1 (by decide)]
      · rw [hT.st]; simp [CellLoopD.blankCellD, blankCell, n1B, n01.symm]
      · rw [hT.sh _ n1B]; simp [CellLoopD.blankCellD, blankCell]

end F3

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
