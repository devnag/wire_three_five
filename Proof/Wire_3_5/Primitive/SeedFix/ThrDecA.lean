import Proof.Wire_3_5.Primitive.Writers.HashNum
import Proof.Wire_3_5.Primitive.Writers.SymDecReq2

/-! # THR decode front, part A: the call's request and counts, register-only

P3:2543-2558 (the THR call's numbers once per call), P3:3011-3016 (the unit's decode before the loop's branch). The THR
unit's decode reads, from the unit's fresh cell `CellLoopD.blankCellD x w out j u`, the THR request `w` (framed on
stream `0`) and the call's counts `u = unaryList (hashNums ++ thrCounts)` (stream `113`) into registers ONLY: on a
FILTER unit the setup's entry `FsIn2` demands every stream but `0, 1, 2, 113` blank (`blank`, `blankT`), so no stream
is written before the unit's branch.

* `tAW` / **`tA_run`**: `n`, `a' = |codes|`, `|carriers|` from the request (`SymDec.reqParse_spec2`, mode-generic),
  `|w|`, the star numbers with the THR filter's error exponent `fe·L` (`StarNums.starNums_spec` at `fe`);
* `tC2W` / **`tC2_run`**: the carriers' lengths `|X_0|`, `|X_1|` (`XA`, `XB`) after the sixteen numbers, and the
  occurrence count `M = hashNums[8]` in `dMS` (the FILTER bank's pool size `2(|X_0|+|X_1|) + M`).

Paper quantities of the main types: the THR call's `n`, `a'`, the carriers' sizes and the occurrence count. -/

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
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum

theorem rv_LEN' : LEN.val = 369 := rfl
theorem rv_TM' : TM.val = 374 := rfl
theorem rv_dN' : dN.val = 320 := rfl
theorem rv_dA'' : dA.val = 321 := rfl
theorem rv_dNC' : dNC.val = 322 := rfl
theorem rv_dK' : dK.val = 327 := rfl
theorem rv_dMS' : dMS.val = 334 := rfl
theorem rv_XA' : XA.val = 370 := rfl
theorem rv_XB' : XB.val = 371 := rfl

theorem fne {n : ℕ} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

section A
variable (cap : ℕ) (x : ℕ)

/-- **Phase A**: `|w|`, the request's `n`, `a'`, `|carriers|` (the request rewound), the star numbers at the THR
filter's error degree `fe`. -/
def tAW (cr fe : ℕ) : WM (LNS x) LNR :=
  .seq (preAW x) (.seq (reqParseW x) (.seq (preBW x) (.seq (FinalPass.Hash4.wcopyR dN (SGb 0) xT)
    (StarNums.starNumsM cr fe SGb))))

/-- Phase A's cost. -/
def tACost (n a nc Kb cr fe cap : ℕ) : ℕ :=
  4 * UnaryPow.sq cap + 1 + (reqParseCost n a nc Kb + 1 + (5 * UnaryPow.sq cap + 1 +
    (UnaryPow.sq cap + 1 + StarNums.starCost n cr fe)))

theorem SGb_ne_lo (i : Fin 20) (r : Fin LNR) (h : r.val < 250 ∨ 270 ≤ r.val) : r ≠ SGb i := fun e => by
  have := congrArg Fin.val e; rw [SGb_val] at this; have := i.isLt; omega

/-- **Phase A, run**: from a state with the framed request on `0` (head `0`) and the decode's scratch `250 … 399`
zero, `dN = n`, `dA = |codes|`, `dNC = |cc|`, `LEN = |w|`, `SGb 8 = kh`, `SGb 10 = fe·L`; the other registers
outside `SGb` kept; the streams, heads and cell kept. -/
theorem tA_run (cr fe : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (σ : WState (LNS x) LNR)
    (w : List Bool) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) (Kb : ℕ) (hw : w = Data.reqW P.n mb codes cc tl)
    (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb) (hst : σ.st (sk x 0) = frame w) (hsh : σ.sh (sk x 0) = 0)
    (z : ∀ r : Fin LNR, 250 ≤ r.val → r.val < 400 → σ.val r = 0)
    (hc1 : 2 * w.length + 2 ≤ cap)
    (hcP : 2 ^ (natBitLength P.n + 1) + 2 ^ (natBitLength codes.length + 1) + 2 ^ (natBitLength cc.length + 1) +
      Kb + P.n + codes.length + 1 ≤ cap)
    (hc3 : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap) :
    ∃ τ c, WExec cap (tAW x cr fe) σ τ c ∧ c ≤ tACost P.n codes.length cc.length Kb cr fe cap ∧
      τ.val dN = P.n ∧ τ.val dA = codes.length ∧ τ.val dNC = cc.length ∧ τ.val LEN = w.length ∧
      τ.val (SGb 8) = P.s * (P.r / 2) ∧ τ.val (SGb 10) = fe * Nat.clog 2 (P.n + 2) ∧
      (∀ r : Fin LNR, r ≠ dN → r ≠ dA → r ≠ dNC → r ≠ LEN → (r.val < 250 ∨ 270 ≤ r.val) → τ.val r = σ.val r) ∧
      τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  have zL : σ.val LEN = 0 := z _ (by decide) (by decide)
  have zC : σ.val CR = 0 := z _ (by decide) (by decide)
  have zT : σ.val TM = 0 := z _ (by decide) (by decide)
  have e1 := preA_spec cap x w σ hst hsh zL zC zT hc1
  set σ1 := σ.setv LEN w.length with hσ1
  have k1 : ∀ r, r ≠ LEN → σ1.val r = σ.val r := fun r hr => by rw [hσ1]; simp [Function.update_of_ne hr]
  obtain ⟨τ2, c2, e2, v2N, v2A, v2NC, v2F, v2C, v2P, v2T, v2K, k2, s2, o2, cl2, c2le, p2⟩ :=
    reqParse_spec2 cap x P.n mb codes cc tl Kb hKb σ1 (by rw [hσ1]; simp [hst, hw]) (by rw [hσ1]; simp [hsh])
      (by rw [k1 _ (by decide)]; exact z _ (by decide) (by decide))
      (by rw [k1 _ (by decide)]; exact z _ (by decide) (by decide))
      (by rw [k1 _ (by decide)]; exact z _ (by decide) (by decide))
      (by rw [k1 _ (by decide)]; exact z _ (by decide) (by decide))
      (by rw [k1 _ (by decide)]; exact z _ (by decide) (by decide))
      (by rw [k1 _ (by decide)]; exact z _ (by decide) (by decide))
      (by rw [k1 _ (by decide)]; exact z _ (by decide) (by decide))
      (by rw [k1 _ (by decide)]; exact z _ (by decide) (by decide)) hcP
  have k2' : ∀ r, r ≠ dN → r ≠ dA → r ≠ dNC → r ≠ dK → τ2.val r = σ1.val r := k2
  have e3 := preB_spec cap x w.length τ2 (by rw [k2' _ (by decide) (by decide) (by decide) (by decide)]; simp [hσ1])
    (by rw [k2' _ (by decide) (by decide) (by decide) (by decide), k1 _ (by decide)]; exact zC)
    (by rw [k2' _ (by decide) (by decide) (by decide) (by decide), k1 _ (by decide)]; exact zT)
    (by rw [SymDec.frame_length, ← hw] at p2; exact p2) hc1
  set τ3 := τ2.seth (sk x 0) 0 with hτ3
  have q1 := Nat.one_le_two_pow (n := natBitLength P.n)
  have q2 := Nat.one_le_two_pow (n := natBitLength codes.length)
  have q3 := Nat.one_le_two_pow (n := natBitLength cc.length)
  have hn : P.n ≤ cap := by omega
  have e4 := SparseNum.copy1 cap dN (SGb 0) xT (by decide) (by decide) (by decide) P.n τ3 (by rw [hτ3]; simp [v2N])
    (by rw [hτ3]; simp only [WState.seth_val]
        rw [k2' _ (by decide) (by decide) (by decide) (by decide), k1 _ (by decide)]
        exact z _ (by simp [SGb_val]) (by simp [SGb_val]))
    (by rw [hτ3]; simp only [WState.seth_val]
        rw [k2' _ (by decide) (by decide) (by decide) (by decide), k1 _ (by decide)]
        exact z _ (by decide) (by decide)) hn
  set τ4 := τ3.setv (SGb 0) P.n with hτ4
  have e5 := StarNums.starNums_spec cap cr fe SGb P hrP τ4 (by rw [hτ4]; simp)
    (fun i hi => by
      have n1 : SGb i ≠ SGb 0 := fun e => hi (SGb.injective e)
      rw [hτ4]; simp only [WState.setv_val, Function.update_of_ne n1, hτ3, WState.seth_val]
      have hi' := i.isLt
      rw [k2' _ (fne (by rw [SGb_val, rv_dN']; omega)) (fne (by rw [SGb_val, rv_dA'']; omega))
        (fne (by rw [SGb_val, rv_dNC']; omega)) (fne (by rw [SGb_val, rv_dK']; omega)),
        k1 _ (fne (by rw [SGb_val, rv_LEN']; omega))]
      exact z _ (by rw [SGb_val]; omega) (by rw [SGb_val]; omega)) hc3
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold tACost; omega
  · have n1 : ∀ i : Fin 20, dN ≠ SGb i := fun i => fne (by rw [SGb_val, rv_dN']; have := i.isLt; omega)
    simp [StarNums.starOut, Function.update_apply, n1, hτ4, hτ3, v2N]
  · have n1 : ∀ i : Fin 20, dA ≠ SGb i := fun i => fne (by rw [SGb_val, rv_dA'']; have := i.isLt; omega)
    simp [StarNums.starOut, Function.update_apply, n1, hτ4, hτ3, v2A]
  · have n1 : ∀ i : Fin 20, dNC ≠ SGb i := fun i => fne (by rw [SGb_val, rv_dNC']; have := i.isLt; omega)
    simp [StarNums.starOut, Function.update_apply, n1, hτ4, hτ3, v2NC]
  · have n1 : ∀ i : Fin 20, LEN ≠ SGb i := fun i => fne (by rw [SGb_val, rv_LEN']; have := i.isLt; omega)
    simp [StarNums.starOut, Function.update_apply, n1, hτ4, hτ3]
    rw [k2' _ (by decide) (by decide) (by decide) (by decide)]; simp [hσ1]
  · simp [StarNums.starOut, Function.update_apply]
  · simp [StarNums.starOut, Function.update_apply]
  · intro r a b c d e
    have hS : ∀ i : Fin 20, r ≠ SGb i := fun i => SGb_ne_lo i r e
    simp [StarNums.starOut, Function.update_apply, hS, hτ4, hτ3]
    by_cases hK : r = dK
    · subst hK
      rw [v2K]; exact (z _ (by decide) (by decide)).symm
    · rw [k2' _ a b c hK, k1 _ d]
  · simp [StarNums.starOut, hτ4, hτ3, s2, hσ1]
  · funext i
    simp only [StarNums.starOut, hτ4, hτ3, WState.setv_sh, WState.seth_sh]
    by_cases h : i = sk x 0
    · subst h; simp [hsh]
    · rw [Function.update_of_ne h, o2 i h, hσ1]; rfl
  · simp [StarNums.starOut, hτ4, hτ3, cl2, hσ1]

/-- **Phase C2**: the carriers' lengths `|X_0|`, `|X_1|` into `XA`, `XB` (after the sixteen numbers; `|carriers| ≤ 2`),
the occurrence count `M = hashNums[8]` into `dMS`; `dK` back at `0`. -/
def tC2W : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR (Hb 0) dK TM) (.seq (.ifr dK (.seq (readItemW (sk x 113) XA) (.seq (.dec dK)
    (.ifr dK (.seq (readItemW (sk x 113) XB) (.dec dK)) .skip))) .skip) (FinalPass.Hash4.wcopyR (Hb 8) dMS TM))

end A

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
