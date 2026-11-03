import Proof.Wire_3_5.Primitive.SeedFix.ThrDecD
import Proof.Wire_3_5.UnionMachine.ThrDecIfaceBase

/-! # THR decode front, part E: the unit's branch and the FILTER finisher

The THR tape's units are SymDec's at `R = |carriers| + 1` rows of `M = 0` targets (`SymFlat.symEmit (nc+1) 0`: per
entry `[true]`, per row `[true]`, the row's request, `[false]`, then `[false]`). On the decoded index (`HVals` at
`EU = thrEU nc`) the branch prints the markers and hands the request units to the finishers: a FILTER row
(`r < nc`) to `fb`, the RADIX row (`r = nc`) to `pb` (`ThrDec.IsReqU`, `ThrDec.rowOfU`).

* `tBrW` (SymDec's `brW` shape on any layout `LNS x`), **`tBr_spec`** (the three clauses of `ThrDec.ThrDecOut`:
  `filt` / `rad` from the finishers' runs, `idle`: the markers printed, both marker registers `0`, `150`, `151` blank);
* `fbTW` (SymDec's FILTER bank registers `fbAW`, the slice `fbB`, the blocks `G`, `H` cleared, then `rFltK := 1`),
  **`fbT_spec`**: `FiltSetup.FsIn2` at the row's parameters, `rRadK = 0`, `rFltK ≠ 0`.

Paper quantities of the main types: the THR tape's unit `j` (P3:3011-3016) and the FILTER row's setup entry
(P3:2019-2054, 3072-3080). -/

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
open NearCubicWires.WireExponent3_5.PrimAsm.SparseNum NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup
open NearCubicWires.WireExponent3_5.UnionMachine.ThrDec

theorem thrEU_eq (nc : ℕ) : thrEU nc = (nc + 1) * (0 + 3) + 2 := rfl

section E
variable (cap : ℕ) (x : ℕ)

/-- **The THR unit's branch**: past the units, the entry markers, the row markers, the FILTER finisher `fb`, the RADIX
finisher `pb` (SymDec's `brW` on `LNS x`). -/
def tBrW (fb pb : WM (LNS x) LNR) : WM (LNS x) LNR :=
  .ifr (H 2) (.ifr (H 3) (.ifr (H 6) (.ifr (H 7) (.ifr (H 11) (.ifr (H 19) (.ifr (H 12) .skip fb) pb)
    (emitF x)) (emitT x)) (emitF x)) (emitT x)) .skip

/-- The idle clause of `ThrDecOut` at an emission `e`. -/
def IdleAt (τ : WState (LNS x) LNR) (w out e : List Bool) (j : ℕ) : Prop :=
  τ.val rRadK = 0 ∧ τ.val rFltK = 0 ∧ τ.st (sk x 150) = [] ∧ τ.sh (sk x 150) = 0 ∧ τ.st (sk x 151) = [] ∧
    τ.sh (sk x 151) = 0 ∧ τ.st (sk x 1) = out ++ e ++ [false] ∧ τ.sh (sk x 1) = (out ++ e).length ∧
    τ.st (sk x 0) = frame w ∧ τ.sh (sk x 0) = 0 ∧ τ.st (sk x 2) = List.replicate j true ∧ τ.sh (sk x 2) = 0

/-- **The unit's branch, run**: at a FILTER row's request unit the finisher `fb`'s outcome, at the RADIX row's the
finisher `pb`'s, at every other unit the loop's emission `unitE j` printed (`IdleAt`). -/
theorem tBr_spec (fb pb : WM (LNS x) LNR) (σ : WState (LNS x) LNR) (out w : List Bool) (j TOT nc N2 pS nG Bf : ℕ)
    (rq : ℕ → ℕ → ℕ → List Bool) (PF PR : WState (LNS x) LNR → Prop)
    (hV : HVals x σ j TOT (thrEU nc) 0 N2 pS nG nc)
    (ho : σ.st (sk x 1) = out ++ [false]) (hoh : σ.sh (sk x 1) = out.length)
    (f0 : σ.st (sk x 150) = []) (f0h : σ.sh (sk x 150) = 0) (f1 : σ.st (sk x 151) = [])
    (f1h : σ.sh (sk x 151) = 0) (hw0 : σ.st (sk x 0) = frame w) (hw0h : σ.sh (sk x 0) = 0)
    (hj2 : σ.st (sk x 2) = List.replicate j true) (hj2h : σ.sh (sk x 2) = 0)
    (zR : σ.val rRadK = 0) (zF : σ.val rFltK = 0)
    (hF : IsReqU TOT nc j → rowOfU nc j < nc → ∃ τ c, WExec cap fb σ τ c ∧ PF τ ∧ c ≤ Bf)
    (hP : IsReqU TOT nc j → rowOfU nc j = nc → ∃ τ c, WExec cap pb σ τ c ∧ PR τ ∧ c ≤ Bf) :
    ∃ τ c, WExec cap (tBrW x fb pb) σ τ c ∧ c ≤ Bf + 12 ∧
      (IsReqU TOT nc j → rowOfU nc j < nc → PF τ) ∧ (IsReqU TOT nc j → rowOfU nc j = nc → PR τ) ∧
      (¬ IsReqU TOT nc j → IdleAt x τ w out (unitE TOT (nc + 1) 0 rq j) j) := by
  have n01 : (0 : Fin 161) ≠ 1 := by decide
  have n21 : (2 : Fin 161) ≠ 1 := by decide
  have n150 : (150 : Fin 161) ≠ 1 := by decide
  have n151 : (151 : Fin 161) ≠ 1 := by decide
  have mk : ∀ bits : List Bool, IdleAt x (markOut x σ out bits) w out bits j := fun bits =>
    ⟨by simp [markOut, zR], by simp [markOut, zF], by rw [markOut_st _ _ _ _ _ n150, f0],
      by rw [markOut_sh _ _ _ _ _ n150, f0h], by rw [markOut_st _ _ _ _ _ n151, f1],
      by rw [markOut_sh _ _ _ _ _ n151, f1h], by simp [markOut], by simp [markOut],
      by rw [markOut_st _ _ _ _ _ n01, hw0], by rw [markOut_sh _ _ _ _ _ n01, hw0h],
      by rw [markOut_st _ _ _ _ _ n21, hj2], by rw [markOut_sh _ _ _ _ _ n21, hj2h]⟩
  have hEU : thrEU nc - 1 = (nc + 1) * (0 + 3) + 1 := by rw [thrEU_eq]; omega
  have hM : 0 + 3 - 1 = 0 + 2 := by omega
  have v2 := hV.h2; have v3 := hV.h3; have v6 := hV.h6; have v7 := hV.h7; have v11 := hV.h11
  have v12 := hV.h12; have v19 := hV.h19
  rw [hEU] at v6; rw [hM] at v11
  rw [thrEU_eq] at v3 v6 v7 v11 v12 v19
  have hq : ∀ q : ℕ, q % (0 + 3) = q % 3 := fun q => rfl
  unfold IsReqU rowOfU
  rw [thrEU_eq]
  by_cases hT : j < TOT
  · have c2 : σ.val (H 2) ≠ 0 := by rw [v2, if_pos hT]; omega
    by_cases hw : j % ((nc + 1) * (0 + 3) + 2) = 0
    · have c3 : σ.val (H 3) = 0 := by rw [v3, hw]
      refine ⟨_, _, WExec.ifrT c2 (WExec.ifrF c3 (emitT_spec cap x σ out ho hoh)), by omega, fun h => absurd hw h.2.1,
        fun h => absurd hw h.2.1, fun _ => ?_⟩
      unfold unitE; rw [if_pos hT, symEmit_w0 (nc + 1) 0 rq j hw]; exact mk [true]
    · have c3 : σ.val (H 3) ≠ 0 := by rw [v3]; exact hw
      by_cases hL : j % ((nc + 1) * (0 + 3) + 2) < (nc + 1) * (0 + 3) + 1
      · have c6 : σ.val (H 6) ≠ 0 := by rw [v6, if_pos hL]; omega
        by_cases hv : (j % ((nc + 1) * (0 + 3) + 2) - 1) % (0 + 3) = 0
        · have c7 : σ.val (H 7) = 0 := by rw [v7, hv]
          refine ⟨_, _, WExec.ifrT c2 (WExec.ifrT c3 (WExec.ifrT c6 (WExec.ifrF c7
            (emitT_spec cap x σ out ho hoh)))), by omega, fun h => absurd h.2.2.2 (by rw [← hq, hv]; omega),
            fun h => absurd h.2.2.2 (by rw [← hq, hv]; omega), fun _ => ?_⟩
          unfold unitE; rw [if_pos hT, symEmit_v0 (nc + 1) 0 rq j hw hL hv]; exact mk [true]
        · have c7 : σ.val (H 7) ≠ 0 := by rw [v7]; exact hv
          by_cases hvL : (j % ((nc + 1) * (0 + 3) + 2) - 1) % (0 + 3) < 0 + 2
          · have c11 : σ.val (H 11) ≠ 0 := by rw [v11, if_pos hvL]; omega
            have h1 : (j % ((nc + 1) * (0 + 3) + 2) - 1) % 3 = 1 := by
              have := hq (j % ((nc + 1) * (0 + 3) + 2) - 1); omega
            have hreq : j < TOT ∧ j % ((nc + 1) * (0 + 3) + 2) ≠ 0 ∧
                j % ((nc + 1) * (0 + 3) + 2) < (nc + 1) * (0 + 3) + 2 - 1 ∧
                (j % ((nc + 1) * (0 + 3) + 2) - 1) % 3 = 1 := ⟨hT, hw, by omega, h1⟩
            have hrl : (j % ((nc + 1) * (0 + 3) + 2) - 1) / 3 ≤ nc := by
              have := Nat.div_lt_of_lt_mul (m := j % ((nc + 1) * (0 + 3) + 2) - 1) (n := 3) (k := nc + 1)
                (by simp at hL ⊢; omega)
              omega
            have hdq : (j % ((nc + 1) * (0 + 3) + 2) - 1) / (0 + 3) = (j % ((nc + 1) * (0 + 3) + 2) - 1) / 3 := rfl
            by_cases hr : (j % ((nc + 1) * (0 + 3) + 2) - 1) / 3 < nc
            · have c19 : σ.val (H 19) ≠ 0 := by rw [v19, hdq, if_pos hr]; omega
              have c12 : σ.val (H 12) = 0 := by rw [v12, hq]; omega
              obtain ⟨τ, c, e, d, hc⟩ := hF hreq hr
              refine ⟨τ, _, WExec.ifrT c2 (WExec.ifrT c3 (WExec.ifrT c6 (WExec.ifrT c7 (WExec.ifrT c11
                (WExec.ifrT c19 (WExec.ifrF c12 e)))))), by omega, fun _ _ => d, fun _ h => absurd h (by omega),
                fun h => absurd hreq h⟩
            · have c19 : σ.val (H 19) = 0 := by rw [v19, hdq, if_neg hr]
              obtain ⟨τ, c, e, d, hc⟩ := hP hreq (show rowOfU nc j = nc by unfold rowOfU; rw [thrEU_eq]; omega)
              refine ⟨τ, _, WExec.ifrT c2 (WExec.ifrT c3 (WExec.ifrT c6 (WExec.ifrT c7 (WExec.ifrT c11
                (WExec.ifrF c19 e))))), by omega, fun _ h => absurd h hr, fun _ _ => d, fun h => absurd hreq h⟩
          · have c11 : σ.val (H 11) = 0 := by rw [v11, if_neg hvL]
            refine ⟨_, _, WExec.ifrT c2 (WExec.ifrT c3 (WExec.ifrT c6 (WExec.ifrT c7 (WExec.ifrF c11
              (emitF_spec cap x σ out ho hoh))))), by omega, fun h => absurd h.2.2.2 (by rw [← hq]; omega),
              fun h => absurd h.2.2.2 (by rw [← hq]; omega), fun _ => ?_⟩
            unfold unitE; rw [if_pos hT, symEmit_vL (nc + 1) 0 rq j hw hL hv hvL]; exact mk [false]
      · have c6 : σ.val (H 6) = 0 := by rw [v6, if_neg hL]
        refine ⟨_, _, WExec.ifrT c2 (WExec.ifrT c3 (WExec.ifrF c6 (emitF_spec cap x σ out ho hoh))), by omega,
          fun h => absurd h.2.2.1 (by omega), fun h => absurd h.2.2.1 (by omega), fun _ => ?_⟩
        unfold unitE; rw [if_pos hT, symEmit_wL (nc + 1) 0 rq j hw hL]; exact mk [false]
  · have c2 : σ.val (H 2) = 0 := by rw [v2, if_neg hT]
    refine ⟨σ, _, WExec.ifrF c2 (WExec.skip σ), by omega, fun h => absurd h.1 hT, fun h => absurd h.1 hT,
      fun _ => ?_⟩
    unfold unitE; rw [if_neg hT]
    exact ⟨zR, zF, f0, f0h, f1, f1h, by simp [ho], by simp [hoh], hw0, hw0h, hj2, hj2h⟩

/-- **The FILTER finisher**: SymDec's FILTER bank registers (the parameters, the seed index, `r4 = 4·row`, the pool
size, the slice), the blocks `G`, `H` cleared, the FILTER marker `rFltK := 1`. -/
def fbTW : WM (LNS x) LNR :=
  .seq (fbAW x) (.seq (.ifr (H 9) (fbB1W x) (fbB0W x)) (.seq (clrsW ghList) (.inc rFltK)))

theorem rv_rFltK : rFltK.val = 399 := rfl

/-- **The FILTER finisher, run**: from the decoded state (the unit's streams as at the entry but the data tape's head,
the registers below `250` and `398 … 407` zero, the parameters in `G 0 … G 2`, the seed's index in `H 18`, the cell
row in `H 13`, the carrier `r ≤ 1` in `H 9`, the counts in `XA`, `XB`, `dMS`), the FILTER setup's entry `FsIn2` at the
row's slice, `rRadK = 0`, `rFltK ≠ 0`. -/
theorem fbT_spec (σ : WState (LNS x) LNR) (w out u : List Bool) (j : ℕ) (P : GapParams)
    (g row xa xb M r : ℕ) (hr : r ≤ 1)
    (hst : σ.st = (CellLoopD.blankCellD x w out j u).st)
    (hsh : ∀ s, s ≠ sk x 113 → σ.sh s = (CellLoopD.blankCellD x w out j u).sh s) (hcl : σ.cell = false)
    (hzl : ∀ q : Fin LNR, q.val < 250 → σ.val q = 0) (zfs : ∀ q : Fin LNR, 398 ≤ q.val → q.val < 408 → σ.val q = 0)
    (zTM : σ.val TM = 0) (hB : ∀ q, σ.val q ≤ cap)
    (g0 : σ.val (G 0) = P.cap) (g1 : σ.val (G 1) = P.len) (g2 : σ.val (G 2) = P.errExp)
    (h18 : σ.val (H 18) = g) (h13 : σ.val (H 13) = row) (h9 : σ.val (H 9) = r)
    (vA : σ.val XA = xa) (vB : σ.val XB = xb) (vM : σ.val dMS = M)
    (c4 : 4 * row ≤ cap) (cG : 2 * (xa + xb) + M ≤ cap) (cA : 2 * xa ≤ cap) (cB : 2 * xb ≤ cap) (c1 : 1 ≤ cap) :
    ∃ τ m, WExec cap (fbTW x) σ τ m ∧ m ≤ fbCost cap + 4 ∧ τ.val rRadK = 0 ∧ τ.val rFltK ≠ 0 ∧
      FsIn2 x τ w out j u P.len P.cap P.errExp g (2 * (2 * row)) (2 * (xa + xb) + M) (fbOff r xa) (fbL r xa xb) := by
  have zfs' : ∀ q : Fin LNR, 400 ≤ q.val → q.val < 408 → σ.val q = 0 := fun q a b => zfs q (by omega) b
  have eA := fbA_run cap x σ P.len P.cap P.errExp g row xa xb M g0 g1 g2 h18 h13 vA vB vM zTM zfs' hB c4 cG
  set σA := fbAOut x σ P.len P.cap P.errExp g row xa xb M with hσA
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := fbAOut_val x σ P.len P.cap P.errExp g row xa xb M
  have kA : ∀ q : Fin LNR, (q.val < 400 ∨ 406 ≤ q.val) → σA.val q = σ.val q :=
    fun q h => fbAOut_other x σ P.len P.cap P.errExp g row xa xb M q h
  have hBA : ∀ q, σA.val q ≤ cap := wexec_le cap eA hB
  obtain ⟨σB, eB, bOff, bL, kB, sB, shB, clB⟩ := fbB_run cap x σA r xa xb hr
    (by rw [kA _ (by rw [H_val]; right; decide)]; exact h9) (by rw [kA _ (by decide)]; exact vA)
    (by rw [kA _ (by decide)]; exact vB) (by rw [kA _ (by decide)]; exact zTM)
    (by rw [kA _ (by decide)]; exact zfs' _ (by decide) (by decide))
    (by rw [kA _ (by decide)]; exact zfs' _ (by decide) (by decide)) hBA cA cB
  have hBB := wexec_le cap eB hBA
  have eC := clrs_spec cap ghList σB hBB
  set σC := zeroOut σB ghList with hσC
  have vC : ∀ q : Fin LNR, q.val < 408 → σC.val q = σB.val q := fun q h => by
    rw [hσC, zeroOut_val, if_neg (not_mem_gh q h)]
  have f399 : σC.val rFltK = 0 := by
    rw [vC _ (by decide), kB _ (by decide), kA _ (by decide)]; exact zfs _ (by decide) (by decide)
  have r398 : σC.val rRadK = 0 := by
    rw [vC _ (by decide), kB _ (by decide), kA _ (by decide)]; exact zfs _ (by decide) (by decide)
  have eD := WExec.inc (cap := cap) rFltK σC (by rw [f399]; omega)
  set τ := σC.setv rFltK (σC.val rFltK + 1) with hτ
  have kD : ∀ q, q ≠ rFltK → τ.val q = σC.val q := fun q h => by rw [hτ]; simp [Function.update_of_ne h]
  have stC : τ.st = (CellLoopD.blankCellD x w out j u).st := by
    rw [hτ, WState.setv_st, hσC, zeroOut_st, sB, hσA, fbAOut_st, hst]
  have shC : ∀ s, s ≠ sk x 113 → τ.sh s = (CellLoopD.blankCellD x w out j u).sh s := fun s hs => by
    rw [hτ, WState.setv_sh, hσC, zeroOut_sh, shB, hσA, fbAOut_sh, hsh s hs]
  have n0B : sk x 0 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have n1B : sk x 1 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have n2B : sk x 2 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have n01 : sk x 0 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have n21 : sk x 2 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have n20 : sk x 2 ≠ sk x 0 := fun e => absurd (sk_inj x e) (by decide)
  have ne400 : ∀ q : Fin LNR, 400 ≤ q.val → q ≠ rFltK := fun q h e => by rw [e, rv_rFltK] at h; omega
  refine ⟨τ, _, WExec.seq eA (WExec.seq eB (WExec.seq eC eD)), ?_, ?_, ?_, ?_⟩
  · unfold fbCost; rw [gh_length]; omega
  · rw [kD _ (by decide)]; exact r398
  · rw [hτ]; simp
  · exact
    { s0 := by rw [stC]; simp [CellLoopD.blankCellD, blankCell, n0B]
      s1 := by rw [stC]; simp [CellLoopD.blankCellD, blankCell, n1B, n01.symm]
      h1 := by rw [shC _ n1B]; simp [CellLoopD.blankCellD, blankCell]
      s2 := by rw [stC]; simp [CellLoopD.blankCellD, blankCell, n2B, n20, n21]
      h2 := by rw [shC _ n2B]; simp [CellLoopD.blankCellD, blankCell, n21]
      s113 := by rw [stC]; simp [CellLoopD.blankCellD]
      blank := fun k k0 k1 k2 k3 => by
        have m0 : sk x k ≠ sk x 0 := fun e => k0 (by rw [sk_inj x e]; rfl)
        have m1 : sk x k ≠ sk x 1 := fun e => k1 (by rw [sk_inj x e]; rfl)
        have m2 : sk x k ≠ sk x 2 := fun e => k2 (by rw [sk_inj x e]; rfl)
        have m3 : sk x k ≠ sk x 113 := fun e => k3 (by rw [sk_inj x e]; rfl)
        refine ⟨?_, ?_⟩
        · rw [stC]; simp [CellLoopD.blankCellD, blankCell, m0, m1, m2, m3]
        · rw [shC _ m3]; simp [CellLoopD.blankCellD, blankCell, m1]
      blankT := fun k => by
        have m0 : sT x k ≠ sk x 0 := (sk_ne_sT x 0 k).symm
        have m1 : sT x k ≠ sk x 1 := (sk_ne_sT x 1 k).symm
        have m2 : sT x k ≠ sk x 2 := (sk_ne_sT x 2 k).symm
        have m3 : sT x k ≠ sk x 113 := (sk_ne_sT x 113 k).symm
        refine ⟨?_, ?_⟩
        · rw [stC]; simp [CellLoopD.blankCellD, blankCell, m0, m1, m2, m3]
        · rw [shC _ m3]; simp [CellLoopD.blankCellD, blankCell, m1]
      cell := by rw [hτ, WState.setv_cell, hσC, zeroOut_cell, clB, hσA, fbAOut_cell, hcl]
      vLen := by rw [kD _ (ne400 _ (by decide)), vC _ (by decide), kB _ (by decide)]; exact a0
      vCap := by rw [kD _ (ne400 _ (by decide)), vC _ (by decide), kB _ (by decide)]; exact a1
      vErr := by rw [kD _ (ne400 _ (by decide)), vC _ (by decide), kB _ (by decide)]; exact a2
      vSeed := by rw [kD _ (ne400 _ (by decide)), vC _ (by decide), kB _ (by decide)]; exact a3
      vR4 := by rw [kD _ (ne400 _ (by decide)), vC _ (by decide), kB _ (by decide)]; exact a4
      vG := by rw [kD _ (ne400 _ (by decide)), vC _ (by decide), kB _ (by decide)]; exact a5
      vOff := by rw [kD _ (ne400 _ (by decide)), vC _ (by decide)]; exact bOff
      vL := by rw [kD _ (ne400 _ (by decide)), vC _ (by decide)]; exact bL
      zLow := fun q hq => by
        rw [kD _ (fun e => by rw [e, rv_rFltK] at hq; omega), vC _ (by omega), kB _ (by omega), kA _ (by omega)]
        exact hzl q hq
      zHigh := fun q hq => by
        rw [kD _ (ne400 _ (by omega)), hσC, zeroOut_val, if_pos (mem_gh q hq)]
      h0 := by rw [shC _ n0B]; simp [CellLoopD.blankCellD, blankCell, n01] }

end E

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
