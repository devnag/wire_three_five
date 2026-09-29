import Proof.Wire_3_5.Primitive.SeedFix.C4KWg

/-! # C4KW, part 8: the stage B3, run and cost

`b3P`: count `ℓ₀` and `p`, the bit loop, the terminators `[true, false, false]`, the value cleared. **`b3_run`**: the
kept word `71` framed on the output, the inputs kept, every register back at `0`. **`partB3 : PartB3`**.

Paper quantity of the main type: the elimination's field modulus word (P3:2268-2269). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.C4Hk (apd apd_nil apd_apd apd_seth apd_sh_d apd_st_d apd_st_ne apd_sh_ne
  wlist wlist_spec)

noncomputable section

/-- **B3's word program**. -/
def b3P : WM 2 4 :=
  .seq (cntW 1 0) (.seq (cntW 2 1) (.seq (.whr 0 b3Body) (.seq (wlist 0 [true, false, false]) (WM.clear 1))))

/-- B3's program steps. -/
def b3n (l p : ℕ) : ℕ := 7 * l + 7 * p + l * (20 * p + 60) + 3 * p + 30

theorem frame_frame (w : List Bool) : frame (frame w) = prs (prs w) ++ [true, false, false] := by
  rw [frame_prs (frame w), frame_prs w, prs_append]; simp [prs]

theorem b3_run (D : HashData) (cap : ℕ) :
    ∃ τ : WState 2 4, WExec (D.MP.ell0 + D.MP.refMod + 2) b3P (st0' (no := 1) iB3 D cap) τ
      (b3n D.MP.ell0 D.MP.refMod) ∧ τ.cell = false ∧ (∀ r, τ.val r = 0) ∧
      τ.st 0 = frame (kw D cap 71) ∧ τ.st 1 = kwIns D cap 2 ∧ τ.st 2 = kwIns D cap 3 := by
  set l := D.MP.ell0 with hl
  set p := D.MP.refMod with hp
  set wc := l + p + 2 with hwc
  set σ0 : WState 2 4 := st0' (no := 1) iB3 D cap with hσ0
  have s1 : σ0.st 1 = List.replicate l true := rfl
  have s2 : σ0.st 2 = List.replicate p true := rfl
  have s0 : σ0.st 0 = [] := rfl
  have rT : ∀ (a q : ℕ), q < a → readTapeBit (List.replicate a true) q = true := fun a q h => by
    simp only [readTapeBit]; rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
  have rF : ∀ a : ℕ, readTapeBit (List.replicate a true) a = false := fun a => by simp [readTapeBit]
  have t1 := cnt_loop wc (1 : Fin 3) (0 : Fin 4) (List.replicate l true) l (rT l) (rF l) l σ0 s1
    (by simp [hσ0, st0'])
    (by simp [hσ0, st0']; omega)
  set σ1 := (σ0.seth 1 l).setv 0 (σ0.val 0 + l) with hσ1
  have t2 := cnt_loop wc (2 : Fin 3) (1 : Fin 4) (List.replicate p true) p (rT p) (rF p) p σ1
    (by rw [hσ1]; simp [WState.setv, WState.seth, s2]) (by rw [hσ1]; simp [WState.setv, WState.seth, hσ0, st0'])
    (by rw [hσ1]; simp [WState.setv, WState.seth, hσ0, st0']; omega)
  set σ2 := (σ1.seth 2 p).setv 1 (σ1.val 1 + p) with hσ2
  have v2 : ∀ r : Fin 4, σ2.val r = ![l, p, 0, 0] r := by
    intro r; fin_cases r <;> simp [hσ2, hσ1, hσ0, st0', WState.setv, WState.seth]
  have hO2 : σ2.sh 0 = (σ2.st 0).length := by rw [hσ2, hσ1]; simp [WState.setv, WState.seth, hσ0, st0', stIn]
  have t3 := b3_loop wc l p σ2 (v2 0) (v2 1) (v2 2) (v2 3) hO2 (by omega) (by omega)
  set σ3 := ((apd σ2 0 (prs (prs (SignedSortKey.binary l p)))).setv 0 0).setv 1 (p / 2 ^ l) with hσ3
  have hO3 : σ3.sh 0 = (σ3.st 0).length := by
    rw [hσ3]; show (apd σ2 0 _).sh 0 = ((apd σ2 0 _).st 0).length; rw [apd_sh_d, apd_st_d, List.length_append]
  have t4 := wlist_spec wc (0 : Fin 3) [true, false, false] σ3 hO3
  have hpl : p / 2 ^ l ≤ p := Nat.div_le_self _ _
  have t5 := wclear_spec wc (1 : Fin 4) (p / 2 ^ l) (apd σ3 0 [true, false, false])
    (by rw [hσ3]; simp [apd, WState.setv]) (by rw [hσ3]; simp [apd, WState.setv]; omega)
  refine ⟨(apd σ3 0 [true, false, false]).setv 1 0,
    WExec.cast wc (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 (WExec.seq t4 t5)))) rfl ?_, rfl, ?_, ?_, ?_, ?_⟩
  · have : 3 * (p / 2 ^ l) ≤ 3 * p := Nat.mul_le_mul_left _ hpl
    unfold b3n; simp only [List.length_cons, List.length_nil]; nlinarith
  · intro r
    fin_cases r <;> simp [apd, WState.setv, hσ3, v2]
  · show (apd σ3 0 [true, false, false]).st 0 = _
    rw [apd_st_d, hσ3]
    show (apd σ2 0 _).st 0 ++ _ = _
    rw [apd_st_d, hσ2, hσ1]
    simp only [WState.setv, WState.seth]
    rw [s0, kw_mod, frame_frame]; rfl
  · show (apd σ3 0 [true, false, false]).st 1 = _
    rw [apd_st_ne _ _ _ (by decide), hσ3]
    show (apd σ2 0 (prs (prs (SignedSortKey.binary l p)))).st 1 = _
    rw [apd_st_ne _ _ _ (by decide), hσ2, hσ1]
    rfl
  · show (apd σ3 0 [true, false, false]).st 2 = _
    rw [apd_st_ne _ _ _ (by decide), hσ3]
    show (apd σ2 0 (prs (prs (SignedSortKey.binary l p)))).st 2 = _
    rw [apd_st_ne _ _ _ (by decide), hσ2, hσ1]
    rfl

theorem b3_le (D : HashData) (cap : ℕ) :
    2 * b3n D.MP.ell0 D.MP.refMod + 2 ≤ 400 * (kwS D cap + 1) ^ 2 + 400 * (kwT D + 1) ^ 2 := by
  have h1 : D.MP.ell0 ≤ kwT D := by unfold kwT; omega
  have h2 : D.MP.refMod ≤ kwT D := by unfold kwT; omega
  unfold b3n
  nlinarith

/-- **B3** (the elimination's modulus word). -/
def partB3 : PartB3 where
  x := 6
  s := _
  M := partM (no := 1) (ni := 2) (ns := 2) (nr := 4) (x := 6) (by norm_num) (by norm_num) b3P
  cost := fun D _ => 2 * b3n D.MP.ell0 D.MP.refMod + 2
  K := 400
  Dg := 2
  cost_le := b3_le
  run := fun D cap => by
    obtain ⟨τ, hw, hc, hv, h0, h1, h2⟩ := b3_run D cap
    refine part_run (no := 1) (ni := 2) (ns := 2) (nr := 4) (x := 6) (by norm_num) (by norm_num) (by norm_num) oB3
      iB3 b3P D cap (D.MP.ell0 + D.MP.refMod + 2) τ (b3n D.MP.ell0 D.MP.refMod) hw hc hv (by unfold b3n; nlinarith)
      (fun j => ?_) (fun k => ?_) (fun i hi => absurd i.isLt (by omega))
    · fin_cases j
      exact h0
    · fin_cases k
      · exact h1
      · exact h2

end

end NearCubicWires.WireExponent3_5.PrimT.C4KW
