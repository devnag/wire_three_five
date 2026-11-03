import Proof.Wire_3_5.Primitive.Writers.HashNum
import Proof.Wire_3_5.Primitive.Writers.SymDecP1
import Proof.Wire_3_5.Primitive.Writers.SymDecReq2

/-! # c4 THR block, numbers part 1: the THR call's request and data items

From the THR cell's entry (`frame (reqW n true codes cc tl)`, the data word `unaryList (hs ++ (xs ++ [tg]))` with
`hs = hashNums`, `tl` free so that it absorbs the hash suffix of `thrIn`): `n`, `a' = |codes|`, `|carriers|`, the sixteen
numbers `hs` into `Hb 0 … 15`, `Σ|X_j|` into `XA`, `|tupleG|` into `XB`.

Paper quantity: the THR call's numbers (P3:2987-3000 at THR, samp:q). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrNums
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec

variable (cap : ℕ)

/-- **The THR decode's first stage**: the request (`n`, `a'`, `|carriers|`), the data items. -/
def p1TW : WM (LNS 0) LNR := .seq (preAW 0) (.seq (reqParseW 0) (.seq (preBW 0) (.seq (hC1W 0) (hC2W 0))))

/-- The first stage's step bound. -/
def p1TCost (n a nc Kb : ℕ) : ℕ :=
  4 * UnaryPow.sq cap + 1 + (reqParseCost n a nc Kb + 1 + (5 * UnaryPow.sq cap + 1 + (34 * UnaryPow.sq cap + 1 +
    8 * UnaryPow.sq cap)))

theorem hC1_Hb (σ : WState (LNS 0) LNR) (l : List ℕ) (i : ℕ) (hi : i < 16) :
    (hC1Out 0 σ l).val (Hb ⟨i, by omega⟩) = l.getD i 0 := by
  unfold hC1Out
  interval_cases i <;> simp [Function.update_apply, Fin.ext_iff, Hb_val, -List.getD_eq_getElem?_getD]

theorem hC1_other (σ : WState (LNS 0) LNR) (l : List ℕ) (r : Fin LNR) (hr : r.val < 337 ∨ 353 ≤ r.val) :
    (hC1Out 0 σ l).val r = σ.val r := by
  have e0 : r.val ≠ 337 := by omega
  have e1 : r.val ≠ 338 := by omega
  have e2 : r.val ≠ 339 := by omega
  have e3 : r.val ≠ 340 := by omega
  have e4 : r.val ≠ 341 := by omega
  have e5 : r.val ≠ 342 := by omega
  have e6 : r.val ≠ 343 := by omega
  have e7 : r.val ≠ 344 := by omega
  have e8 : r.val ≠ 345 := by omega
  have e9 : r.val ≠ 346 := by omega
  have e10 : r.val ≠ 347 := by omega
  have e11 : r.val ≠ 348 := by omega
  have e12 : r.val ≠ 349 := by omega
  have e13 : r.val ≠ 350 := by omega
  have e14 : r.val ≠ 351 := by omega
  have e15 : r.val ≠ 352 := by omega
  unfold hC1Out
  simp [Function.update_apply, Fin.ext_iff, Hb_val, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]

/-- **The THR decode's first stage, run.** -/
theorem p1T_spec (w : List Bool) (n : ℕ) (codes cc : List ℕ) (tl : List Bool) (hs xs : List ℕ) (tg Kb : ℕ)
    (hw : w = Data.reqW n true codes cc tl) (hhs : hs.length = 16) (hxs : xs.length ≤ 2)
    (h0v : hs.getD 0 0 = xs.length) (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb)
    (cW : 2 * w.length + 2 ≤ cap)
    (cP : 2 ^ (natBitLength n + 1) + 2 ^ (natBitLength codes.length + 1) + 2 ^ (natBitLength cc.length + 1) +
      Kb + n + codes.length + 1 ≤ cap)
    (hcl : ∀ k, (hs ++ (xs ++ [tg])).getD k 0 ≤ cap) (hcs : xs.sum + tg + 4 ≤ cap) :
    ∃ τ c, WExec cap p1TW (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (hs ++ (xs ++ [tg])))) τ c ∧
      c ≤ p1TCost cap n codes.length cc.length Kb ∧
      τ.val dN = n ∧ τ.val dA = codes.length ∧ τ.val dNC = cc.length ∧ τ.val LEN = w.length ∧
      (∀ i : Fin 32, i.val < 16 → τ.val (Hb i) = hs.getD i.val 0) ∧ τ.val XA = xs.sum ∧ τ.val XB = tg ∧
      (∀ r : Fin LNR, r.val ≠ 320 → r.val ≠ 321 → r.val ≠ 322 → r.val ≠ 327 → r.val ≠ 369 → r.val ≠ 370 →
        r.val ≠ 371 → (r.val < 337 ∨ 353 ≤ r.val) → τ.val r = 0) ∧
      τ.st = (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (hs ++ (xs ++ [tg])))).st ∧
      (∀ s, s ≠ sk 0 113 → τ.sh s = (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (hs ++ (xs ++ [tg])))).sh s) ∧
      τ.cell = false := by
  set σ0 := CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (hs ++ (xs ++ [tg]))) with hσ0
  have n01 : sk 0 0 ≠ sk 0 1 := fun e => absurd (sk_inj 0 e) (by decide)
  have n0B : sk 0 0 ≠ sk 0 113 := fun e => absurd (sk_inj 0 e) (by decide)
  have nB1 : sk 0 113 ≠ sk 0 1 := fun e => absurd (sk_inj 0 e) (by decide)
  have z0 : ∀ r, σ0.val r = 0 := fun r => by simp [hσ0, CellLoopD.blankCellD, blankCell]
  have s0 : σ0.st (sk 0 0) = frame w := by simp [hσ0, CellLoopD.blankCellD, blankCell, n0B]
  have sh0 : σ0.sh (sk 0 0) = 0 := by simp [hσ0, CellLoopD.blankCellD, blankCell, n01]
  have s113 : σ0.st (sk 0 113) = Data.unaryList (hs ++ (xs ++ [tg])) ++ [] := by
    rw [List.append_nil]; simp [hσ0, CellLoopD.blankCellD]
  have sh113 : σ0.sh (sk 0 113) = 0 := by simp [hσ0, CellLoopD.blankCellD, blankCell, nB1]
  have cl0 : σ0.cell = false := by simp [hσ0, CellLoopD.blankCellD, blankCell]
  -- A: measure, rewind
  have eA := preA_spec cap 0 w σ0 s0 sh0 (z0 _) (z0 _) (z0 _) cW
  set σ1 := σ0.setv LEN w.length with hσ1
  have z1 : ∀ r, r ≠ LEN → σ1.val r = 0 := fun r h => by rw [hσ1]; simp [Function.update_apply, h, z0]
  have s1 : σ1.st = σ0.st := by rw [hσ1]; rfl
  have sh1 : σ1.sh = σ0.sh := by rw [hσ1]; rfl
  -- the request
  obtain ⟨τ2, c2, eP, v2N, v2A, v2NC, v2F, v2C, v2P, v2T, v2K, k2, s2, sh2, cl2, c2le, hh2⟩ :=
    reqParse_spec2 cap 0 n true codes cc tl Kb hKb σ1 (by rw [s1, s0, hw]) (by rw [sh1, sh0])
      (z1 _ (by decide)) (z1 _ (by decide)) (z1 _ (by decide)) (z1 _ (by decide))
      (z1 _ (by decide)) (z1 _ (by decide)) (z1 _ (by decide)) (z1 _ (by decide)) cP
  have z2 : ∀ r, r ≠ dN → r ≠ dA → r ≠ dNC → r ≠ dK → r ≠ LEN → τ2.val r = 0 := fun r a b c d e => by
    rw [k2 r a b c d]; exact z1 r e
  have vL2 : τ2.val LEN = w.length := by rw [k2 _ (by decide) (by decide) (by decide) (by decide), hσ1]; simp
  -- B: rewind
  have eB := preB_spec cap 0 w.length τ2 vL2 (z2 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (z2 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [← hw, RepairOrdinary.frame_length] at hh2; exact hh2) cW
  set σ3 := τ2.seth (sk 0 0) 0 with hσ3
  have v3 : σ3.val = τ2.val := by rw [hσ3]; rfl
  have s3 : σ3.st = σ0.st := by rw [hσ3]; simp only [WState.seth_st]; rw [s2, s1]
  have sh3 : ∀ i, i ≠ sk 0 0 → σ3.sh i = σ0.sh i := fun i h => by
    rw [hσ3]; simp [Function.update_apply, h, sh2 i h, sh1]
  have sh30 : σ3.sh (sk 0 0) = 0 := by rw [hσ3]; simp
  have cl3 : σ3.cell = false := by rw [hσ3]; simp only [WState.seth_cell]; rw [cl2]; simp [hσ1, cl0]
  have vz3 : ∀ r : Fin LNR, r.val ≠ 320 → r.val ≠ 321 → r.val ≠ 322 → r.val ≠ 327 → r.val ≠ 369 → σ3.val r = 0 := by
    intro r a b c d e
    rw [v3]
    exact z2 r (fun h => a (by rw [h]; rfl)) (fun h => b (by rw [h]; rfl)) (fun h => c (by rw [h]; rfl))
      (fun h => d (by rw [h]; rfl)) (fun h => e (by rw [h]; rfl))
  have hB3 : ∀ q, σ3.val q ≤ cap := by
    have hb := wexec_le cap (WExec.seq eA (WExec.seq eP eB)) (fun q => by rw [z0]; omega)
    intro q; exact hb q
  -- C1
  have eC1 := hC1_run cap 0 σ3 (hs ++ (xs ++ [tg])) [] (by simp [hhs]) (by rw [s3]; exact s113)
    (by rw [sh3 _ (Ne.symm n0B)]; exact sh113)
    (fun i => vz3 _ (by rw [Hb_val]; omega) (by rw [Hb_val]; omega) (by rw [Hb_val]; omega) (by rw [Hb_val]; omega)
      (by rw [Hb_val]; have := i.isLt; omega)) hcl
  set σC1 := hC1Out 0 σ3 (hs ++ (xs ++ [tg])) with hσC1
  have c10 : σC1.val (Hb 0) = xs.length := by
    rw [hσC1, show (Hb 0 : Fin LNR) = Hb ⟨0, by omega⟩ from rfl, hC1_Hb _ _ 0 (by omega)]
    rw [List.getD_append _ _ _ _ (by omega)]; exact h0v
  have stC1 : σC1.st = σ0.st := by rw [hσC1]; unfold hC1Out; simp [s3]
  have shC1 : σC1.sh (sk 0 113) = (Data.unaryList ((hs ++ (xs ++ [tg])).take 16)).length := by
    rw [hσC1]; unfold hC1Out; simp
  have shC1o : ∀ s, s ≠ sk 0 113 → σC1.sh s = σ3.sh s := fun s hs => by
    rw [hσC1]; unfold hC1Out; simp [Function.update_apply, hs]
  have clC1 : σC1.cell = false := by rw [hσC1]; unfold hC1Out; simp [cl3]
  have hBC1 : ∀ q, σC1.val q ≤ cap := wexec_le cap eC1 hB3
  -- C2
  have zXA : σC1.val XA = 0 := by
    rw [hσC1, hC1_other _ _ _ (by rw [rv_XA]; omega)]
    exact vz3 _ (by rw [rv_XA]; omega) (by rw [rv_XA]; omega) (by rw [rv_XA]; omega) (by rw [rv_XA]; omega) (by rw [rv_XA]; omega)
  have zXB : σC1.val XB = 0 := by
    rw [hσC1, hC1_other _ _ _ (by rw [rv_XB]; omega)]
    exact vz3 _ (by rw [rv_XB]; omega) (by rw [rv_XB]; omega) (by rw [rv_XB]; omega) (by rw [rv_XB]; omega) (by rw [rv_XB]; omega)
  have zTM : σC1.val TM = 0 := by
    rw [hσC1, hC1_other _ _ _ (by rw [rv_TM]; omega)]
    exact vz3 _ (by rw [rv_TM]; omega) (by rw [rv_TM]; omega) (by rw [rv_TM]; omega) (by rw [rv_TM]; omega) (by rw [rv_TM]; omega)
  obtain ⟨τ, c5, eC2, c5le, tA, tB, kC2, stC2, shC2, clC2⟩ := hC2_run cap 0 σC1 hs xs tg [] hhs hxs
    (by rw [stC1]; exact s113) shC1 c10 (by rw [hσC1, hC1_other _ _ _ (by rw [rv_dK]; omega), v3]; exact v2K)
    zXA zXB zTM hcl hcs
  have kk : ∀ r : Fin LNR, r ≠ dK → r ≠ XA → r ≠ XB → (r.val < 337 ∨ 353 ≤ r.val) → τ.val r = τ2.val r := by
    intro r a b c d
    rw [kC2 r a b c, hσC1, hC1_other _ _ _ d, v3]
  refine ⟨τ, _, WExec.seq eA (WExec.seq eP (WExec.seq eB (WExec.seq eC1 eC2))), ?_, ?_, ?_, ?_, ?_, ?_, tA, tB,
    ?_, ?_, ?_, ?_⟩
  · unfold p1TCost; omega
  · rw [kk _ (by decide) (by decide) (by decide) (by rw [rv_dN]; omega)]; exact v2N
  · rw [kk _ (by decide) (by decide) (by decide) (by rw [rv_dA]; omega)]; exact v2A
  · rw [kk _ (by decide) (by decide) (by decide) (by rw [rv_dNC]; omega)]; exact v2NC
  · rw [kk _ (by decide) (by decide) (by decide) (by rw [rv_LEN]; omega)]; exact vL2
  · intro i hi
    have n1 : Hb i ≠ dK := fun e => by have := congrArg Fin.val e; rw [Hb_val, rv_dK] at this; omega
    have n2 : Hb i ≠ XA := fun e => by have := congrArg Fin.val e; rw [Hb_val, rv_XA] at this; omega
    have n3 : Hb i ≠ XB := fun e => by have := congrArg Fin.val e; rw [Hb_val, rv_XB] at this; omega
    rw [kC2 _ n1 n2 n3, hσC1, show i = ⟨i.val, by omega⟩ from rfl, hC1_Hb _ _ i.val hi,
      List.getD_append _ _ _ _ (by omega)]
  · intro r a b c d e f g hh
    have n1 : r ≠ dK := fun h => d (by rw [h]; rfl)
    have n2 : r ≠ XA := fun h => f (by rw [h]; rfl)
    have n3 : r ≠ XB := fun h => g (by rw [h]; rfl)
    rw [kk r n1 n2 n3 hh]
    exact z2 r (fun h => a (by rw [h]; rfl)) (fun h => b (by rw [h]; rfl)) (fun h => c (by rw [h]; rfl)) n1
      (fun h => e (by rw [h]; rfl))
  · rw [stC2, stC1]
  · intro s hs
    rw [shC2 s hs, shC1o s hs]
    by_cases h0 : s = sk 0 0
    · subst h0; rw [sh30, sh0]
    · exact sh3 s h0
  · rw [clC2, clC1]

end NearCubicWires.WireExponent3_5.PrimAsm.ThrNums
