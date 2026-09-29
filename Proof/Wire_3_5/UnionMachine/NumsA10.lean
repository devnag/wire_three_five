import Proof.Wire_3_5.UnionMachine.NumsA8

/-! # NW phase (a), part 10: the finish (`V`, the roles back, the counts' head rewound)

After the SYM numbers program on NW's bank (`numsBank`): the registers hold the program's values (each `≤ B₀`),
`G 21·G 41·KB 52 = V`; the stash streams hold `1^n`, `1^e`, `1^T`; every head is `0` except stream `113`'s, at most
`K₁·(|fpIn|+1)^{D₃}`. The finish clears every register but the three factors, multiplies them into `rV`, reads the
roles back from the stash, and rewinds stream `113` by the bound `K₁·(|fpIn|+1)^{D₃}` (computed from the input's
length), every other register `0`.

* `rsF`, `M1`, `M2`, `PX`, `finW`, `fval`, **`fin_run`**.

Paper quantity of the main type: `V = |E|·|FlatSeed|·Q` in `rV` (the denominator's unshifted value). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g powN powN_spec clearL clearL_spec zeroL mulStep
  mulStep_spec mulCost mulCost_le)

/-- Every register but the three factors of `V`. -/
def rsF : List (Fin LNR) := (List.finRange LNR).filter
  (fun q => !(decide (q = SymDec.G 21) || decide (q = SymDec.G 41) || decide (q = PrimT.C4Set.KB 52)))

theorem mem_rsF (q : Fin LNR) : q ∈ rsF ↔ q ≠ SymDec.G 21 ∧ q ≠ SymDec.G 41 ∧ q ≠ PrimT.C4Set.KB 52 := by
  unfold rsF
  simp only [List.mem_filter, List.mem_finRange, true_and, Bool.not_eq_true', Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  tauto

theorem rsF_length : rsF.length ≤ 512 := by
  unfold rsF
  exact le_trans (List.length_filter_le _ _) (by simp [LNR])

/-- `mulStep`'s registers: `G 21 := G 21·G 41`, then `G 21 := G 21·KB 52`; `powN`'s: `g 2 := g 2·g 0^k`. -/
def M1 : Fin 6 ↪ Fin LNR := ⟨![SymDec.G 21, SymDec.G 41, g 2, g 3, g 4, g 5], by decide⟩
def M2 : Fin 6 ↪ Fin LNR := ⟨![SymDec.G 21, PrimT.C4Set.KB 52, g 2, g 3, g 4, g 5], by decide⟩
def PX : Fin 6 ↪ Fin LNR := ⟨![g 2, g 0, g 3, g 4, g 5, g 6], by decide⟩

/-- The finish's step count, as a sum of atoms. -/
theorem fin_arith (c1 c13 m1 m2 V b1 q1 n e T F K1 Bb M Rc P2 P3 B0 : ℕ) (h1 : c1 ≤ Rc) (hcl : Rc ≤ 1536 * M)
    (hm1 : m1 ≤ 60 * P2) (hm2 : m2 ≤ 60 * P2) (hp : c13 ≤ 61 * P3) (hM : B0 + V + Bb + n + e + T + F + K1 + 2 ≤ M)
    (hb : b1 + 1 ≤ M) (hq : q1 + 1 ≤ M) (hMM : M ≤ P2) (hMMM : P2 ≤ P3) :
    c1 + 1 + (m1 + 1 + (m2 + 1 + (7 * V + 1 + 1 + (3 * b1 + 1 + 1 + (3 * q1 + 1 + 1 + (16 * n + 3 + 1 +
      (16 * e + 3 + 1 + (16 * T + 3 + 1 + (F * (17 + 2) + 1 + 1 + (5 * (2 * F) + 1) + 1 + (3 + 1 + (4 * K1 + 1 +
      (c13 + 1 + (5 * Bb + 1 + 1 + (3 * (F + 1) + 1)))))))))))))) ≤ 5000 * P3 := by
  linarith

section Bank
variable (x : ℕ) (hx : DataDock.DT + 3 ≤ x)

/-- **The finish program** at the rewind bound `K₁·(|fpIn|+1)^{D₃}`. -/
def finW (K1 D3 : ℕ) : WM (LNS x) LNR :=
  .seq (clearL rsF) (.seq (mulStep M1) (.seq (mulStep M2) (.seq (WM.move (SymDec.G 21) rV)
    (.seq (WM.clear (SymDec.G 41)) (.seq (WM.clear (PrimT.C4Set.KB 52))
    (.seq (readU (sNs x hx) rN (g 0)) (.seq (readU (sEs x hx) rE (g 0)) (.seq (readU (sTs x hx) rT (g 0))
    (.seq (frameLenW (sIn x) (g 0) (g 1)) (.seq (.inc (g 0)) (.seq (incK (g 2) K1) (.seq (powN PX D3)
    (.seq (WM.rewind (sk x 113) (g 2)) (WM.clear (g 0)))))))))))))))

/-- The registers after (a): the roles and `V`, every other register `0`. -/
def fval (n e T V : ℕ) : Fin LNR → ℕ := fun q =>
  if q = rN then n else if q = rE then e else if q = rT then T else if q = rV then V else 0

theorem fin_run (cap B0 K1 D3 h : ℕ) (w : List Bool) (n e T V : ℕ) (ω : St x)
    (hin : ω.st (sIn x) = frame w) (hSN : ω.st (sNs x hx) = List.replicate n true)
    (hSE : ω.st (sEs x hx) = List.replicate e true) (hST : ω.st (sTs x hx) = List.replicate T true)
    (hsh : ∀ i, i ≠ sk x 113 → ω.sh i = 0) (h113 : ω.sh (sk x 113) = h) (hh : h ≤ K1 * (w.length + 1) ^ D3)
    (hval : ∀ q, ω.val q ≤ B0)
    (hV : ω.val (SymDec.G 21) * ω.val (SymDec.G 41) * ω.val (PrimT.C4Set.KB 52) = V)
    (hGF : ω.val (SymDec.G 21) * ω.val (SymDec.G 41) ≤ B0) (hQ : ω.val (PrimT.C4Set.KB 52) ≤ w.length)
    (hc : B0 + V + K1 * (w.length + 1) ^ D3 + n + e + T + 2 * w.length + 2 ≤ cap) :
    ∃ c, WExec cap (finW x hx K1 D3) ω ⟨fun _ => 0, ω.st, fval n e T V, ω.cell⟩ c ∧
      c ≤ 5000 * (B0 + V + K1 * (w.length + 1) ^ D3 + n + e + T + w.length + K1 + D3 + 2) ^ 3 := by
  -- names
  obtain ⟨a1, ha1⟩ : ∃ v, v = ω.val (SymDec.G 21) := ⟨_, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ v, v = ω.val (SymDec.G 41) := ⟨_, rfl⟩
  obtain ⟨q1, hq1⟩ : ∃ v, v = ω.val (PrimT.C4Set.KB 52) := ⟨_, rfl⟩
  rw [← ha1, ← hb1, ← hq1] at hV
  rw [← ha1, ← hb1] at hGF
  rw [← hq1] at hQ
  obtain ⟨F, hF⟩ : ∃ v, v = w.length := ⟨_, rfl⟩
  rw [← hF] at hh hc hQ ⊢
  obtain ⟨Bb, hBb⟩ : ∃ v, v = K1 * (F + 1) ^ D3 := ⟨_, rfl⟩
  rw [← hBb] at hh hc ⊢
  -- the registers' distinctness
  have d1 : SymDec.G 21 ≠ SymDec.G 41 := by decide
  have d2 : SymDec.G 21 ≠ PrimT.C4Set.KB 52 := by decide
  have d3 : SymDec.G 41 ≠ PrimT.C4Set.KB 52 := by decide
  have dV1 : rV ≠ SymDec.G 21 := by decide
  have dV2 : rV ≠ SymDec.G 41 := by decide
  have dV3 : rV ≠ PrimT.C4Set.KB 52 := by decide
  have gG : ∀ j : Fin 10, g j ≠ SymDec.G 21 ∧ g j ≠ SymDec.G 41 ∧ g j ≠ PrimT.C4Set.KB 52 := by
    intro j
    have hv : (g j).val = 470 + j.val := rfl
    have h21 : (SymDec.G 21).val = 429 := rfl
    have h41 : (SymDec.G 41).val = 449 := rfl
    have h52 : (PrimT.C4Set.KB 52).val = 52 := rfl
    exact ⟨fne (by omega), fne (by omega), fne (by omega)⟩
  have hz0 : ∀ q, (zeroL ω rsF).val q =
      if q = SymDec.G 21 then a1 else if q = SymDec.G 41 then b1 else if q = PrimT.C4Set.KB 52 then q1 else 0 := by
    intro q
    show (if q ∈ rsF then 0 else ω.val q) = _
    by_cases e1 : q = SymDec.G 21
    · subst e1; rw [if_neg (fun hm => ((mem_rsF _).1 hm).1 rfl), if_pos rfl, ha1]
    · by_cases e2 : q = SymDec.G 41
      · subst e2; rw [if_neg (fun hm => ((mem_rsF _).1 hm).2.1 rfl), if_neg e1, if_pos rfl, hb1]
      · by_cases e3 : q = PrimT.C4Set.KB 52
        · subst e3; rw [if_neg (fun hm => ((mem_rsF _).1 hm).2.2 rfl), if_neg e1, if_neg e2, if_pos rfl, hq1]
        · rw [if_pos ((mem_rsF _).2 ⟨e1, e2, e3⟩), if_neg e1, if_neg e2, if_neg e3]
  -- f1: clear all but the factors
  obtain ⟨c1, e1, hc1⟩ := clearL_spec cap B0 (by omega) rsF ω (fun r _ => hval r)
  -- f2, f3: `G 21 := V`
  have m10 : M1 0 = SymDec.G 21 := rfl
  have m11 : M1 1 = SymDec.G 41 := rfl
  have m12 : M1 2 = g 2 := rfl
  have m13 : M1 3 = g 3 := rfl
  have m14 : M1 4 = g 4 := rfl
  have m15 : M1 5 = g 5 := rfl
  have e2 := mulStep_spec cap M1 (zeroL ω rsF) (by rw [m12, hz0, if_neg (gG 2).1, if_neg (gG 2).2.1, if_neg (gG 2).2.2]) (by rw [m13, hz0, if_neg (gG 3).1, if_neg (gG 3).2.1, if_neg (gG 3).2.2])
    (by rw [m14, hz0, if_neg (gG 4).1, if_neg (gG 4).2.1, if_neg (gG 4).2.2]) (by rw [m15, hz0, if_neg (gG 5).1, if_neg (gG 5).2.1, if_neg (gG 5).2.2])
    (by rw [m10, m11, hz0, hz0, if_pos rfl, if_neg d1.symm, if_pos rfl]; omega)
    (by rw [m10, hz0, if_pos rfl, ha1]; exact le_trans (hval _) (by omega))
    (by rw [m11, hz0, if_neg d1.symm, if_pos rfl, hb1]; exact le_trans (hval _) (by omega))
  rw [m10, m11, hz0, hz0, if_pos rfl, if_neg d1.symm, if_pos rfl] at e2
  have hcm1 := mulCost_le a1 b1 B0 (by rw [ha1]; exact hval _)
  obtain ⟨z1, hz1⟩ : ∃ s, s = (zeroL ω rsF).setv (SymDec.G 21) (a1 * b1) := ⟨_, rfl⟩
  rw [← hz1] at e2
  have v1 : ∀ q, z1.val q = if q = SymDec.G 21 then a1 * b1 else if q = SymDec.G 41 then b1 else
      if q = PrimT.C4Set.KB 52 then q1 else 0 := by
    intro q; rw [hz1, WState.setv_val]
    by_cases hq : q = SymDec.G 21
    · subst hq; rw [Function.update_self, if_pos rfl]
    · rw [Function.update_of_ne hq, hz0, if_neg hq, if_neg hq]
  have m20 : M2 0 = SymDec.G 21 := rfl
  have m21 : M2 1 = PrimT.C4Set.KB 52 := rfl
  have m22 : M2 2 = g 2 := rfl
  have m23 : M2 3 = g 3 := rfl
  have m24 : M2 4 = g 4 := rfl
  have m25 : M2 5 = g 5 := rfl
  have e3 := mulStep_spec cap M2 z1 (by rw [m22, v1, if_neg (gG 2).1, if_neg (gG 2).2.1, if_neg (gG 2).2.2]) (by rw [m23, v1, if_neg (gG 3).1, if_neg (gG 3).2.1, if_neg (gG 3).2.2])
    (by rw [m24, v1, if_neg (gG 4).1, if_neg (gG 4).2.1, if_neg (gG 4).2.2]) (by rw [m25, v1, if_neg (gG 5).1, if_neg (gG 5).2.1, if_neg (gG 5).2.2])
    (by rw [m20, m21, v1, v1, if_pos rfl, if_neg d2.symm, if_neg d3.symm, if_pos rfl, hV]; omega)
    (by rw [m20, v1, if_pos rfl]; omega) (by rw [m21, v1, if_neg d2.symm, if_neg d3.symm, if_pos rfl]; omega)
  rw [m20, m21, v1, v1, if_pos rfl, if_neg d2.symm, if_neg d3.symm, if_pos rfl, hV] at e3
  have hcm2 := mulCost_le (a1 * b1) q1 B0 hGF
  obtain ⟨z2, hz2⟩ : ∃ s, s = z1.setv (SymDec.G 21) V := ⟨_, rfl⟩
  rw [← hz2] at e3
  have v2 : ∀ q, z2.val q = if q = SymDec.G 21 then V else if q = SymDec.G 41 then b1 else
      if q = PrimT.C4Set.KB 52 then q1 else 0 := by
    intro q; rw [hz2, WState.setv_val]
    by_cases hq : q = SymDec.G 21
    · subst hq; rw [Function.update_self, if_pos rfl]
    · rw [Function.update_of_ne hq, v1, if_neg hq, if_neg hq]
  -- f4: `rV := V`
  have e4 := wmove_spec cap (SymDec.G 21) rV dV1.symm V z2 (by rw [v2, if_pos rfl])
    (by rw [v2, if_pos rfl]; omega) (by rw [v2, v2, if_neg dV1, if_neg dV2, if_neg dV3, if_pos rfl]; omega)
  rw [v2, v2, if_neg dV1, if_neg dV2, if_neg dV3, if_pos rfl, Nat.zero_add] at e4
  -- f5: clear the other factors
  have e5 := wclear_spec cap (SymDec.G 41) b1 ((z2.setv (SymDec.G 21) 0).setv rV V)
    (by rw [WState.setv_val, Function.update_of_ne dV2.symm, WState.setv_val, Function.update_of_ne d1.symm, v2,
        if_neg d1.symm, if_pos rfl])
    (by rw [WState.setv_val, Function.update_of_ne dV2.symm, WState.setv_val, Function.update_of_ne d1.symm, v2,
        if_neg d1.symm, if_pos rfl, hb1]; exact le_trans (hval _) (by omega))
  have e6 := wclear_spec cap (PrimT.C4Set.KB 52) q1 (((z2.setv (SymDec.G 21) 0).setv rV V).setv (SymDec.G 41) 0)
    (by rw [WState.setv_val, Function.update_of_ne d3.symm, WState.setv_val, Function.update_of_ne dV3.symm,
        WState.setv_val, Function.update_of_ne d2.symm, v2, if_neg d2.symm, if_neg d3.symm, if_pos rfl])
    (by rw [WState.setv_val, Function.update_of_ne d3.symm, WState.setv_val, Function.update_of_ne dV3.symm,
        WState.setv_val, Function.update_of_ne d2.symm, v2, if_neg d2.symm, if_neg d3.symm, if_pos rfl]; omega)
  obtain ⟨z6, hz6⟩ : ∃ s, s = ((((z2.setv (SymDec.G 21) 0).setv rV V).setv (SymDec.G 41) 0).setv
      (PrimT.C4Set.KB 52) 0) := ⟨_, rfl⟩
  rw [← hz6] at e6
  have v6 : ∀ q, z6.val q = if q = rV then V else 0 := by
    intro q; rw [hz6]; simp only [WState.setv_val]
    by_cases h1 : q = PrimT.C4Set.KB 52
    · subst h1; rw [Function.update_self, if_neg dV3.symm]
    · rw [Function.update_of_ne h1]
      by_cases h2 : q = SymDec.G 41
      · subst h2; rw [Function.update_self, if_neg dV2.symm]
      · rw [Function.update_of_ne h2]
        by_cases h3 : q = rV
        · subst h3; rw [Function.update_self, if_pos rfl]
        · rw [Function.update_of_ne h3, if_neg h3]
          by_cases h4 : q = SymDec.G 21
          · subst h4; rw [Function.update_self]
          · rw [Function.update_of_ne h4, v2, if_neg h4, if_neg h2, if_neg h1]
  have s6 : z6.st = ω.st := by rw [hz6, hz2, hz1]; rfl
  have sh6 : z6.sh = ω.sh := by rw [hz6, hz2, hz1]; rfl
  have cl6 : z6.cell = ω.cell := by rw [hz6, hz2, hz1]; rfl
  -- f6: the roles back
  have g0N : g 0 ≠ rN := by decide
  have g0E : g 0 ≠ rE := by decide
  have g0T : g 0 ≠ rT := by decide
  have e7 := readU_spec cap (sNs x hx) rN (g 0) g0N.symm n z6 (by rw [s6, hSN])
    (by rw [sh6]; exact hsh _ (fne (by rw [sNs_val, DT_val]; show 10063 ≠ 113; omega)))
    (by rw [v6, if_neg (by decide)]) (by rw [v6, if_neg (by decide)]) (by omega)
  have e8 := readU_spec cap (sEs x hx) rE (g 0) g0E.symm e (z6.setv rN n) (by simp [s6, hSE])
    (by simp only [WState.setv_sh]; rw [sh6]; exact hsh _ (fne (by rw [sEs_val, DT_val]; show 10064 ≠ 113; omega)))
    (by simp [v6, show rE ≠ rN by decide, show rE ≠ rV by decide])
    (by rw [WState.setv_val, Function.update_of_ne g0N, v6, if_neg (by decide)]) (by omega)
  have e9 := readU_spec cap (sTs x hx) rT (g 0) g0T.symm T ((z6.setv rN n).setv rE e) (by simp [s6, hST])
    (by simp only [WState.setv_sh]; rw [sh6]; exact hsh _ (fne (by rw [sTs_val, DT_val]; show 10065 ≠ 113; omega)))
    (by simp [v6, show rT ≠ rN by decide, show rT ≠ rE by decide, show rT ≠ rV by decide])
    (by rw [WState.setv_val, Function.update_of_ne g0E, WState.setv_val, Function.update_of_ne g0N, v6,
      if_neg (by decide)]) (by omega)
  obtain ⟨z9, hz9⟩ : ∃ s, s = ((z6.setv rN n).setv rE e).setv rT T := ⟨_, rfl⟩
  rw [← hz9] at e9
  have v9 : ∀ q, z9.val q = fval n e T V q := by
    intro q; rw [hz9]; unfold fval; simp only [WState.setv_val]
    by_cases h1 : q = rT
    · subst h1; rw [Function.update_self, if_neg (by decide), if_neg (by decide), if_pos rfl]
    · rw [Function.update_of_ne h1]
      by_cases h2 : q = rE
      · subst h2; rw [Function.update_self, if_neg (by decide), if_pos rfl]
      · rw [Function.update_of_ne h2]
        by_cases h3 : q = rN
        · subst h3; rw [Function.update_self, if_pos rfl]
        · rw [Function.update_of_ne h3, v6, if_neg h3, if_neg h2, if_neg h1]
  have s9 : z9.st = ω.st := by rw [hz9]; exact s6
  have sh9 : z9.sh = ω.sh := by rw [hz9]; exact sh6
  -- f7: the rewind bound `g 2 := K₁·(F+1)^{D₃}`
  have fg : ∀ j : Fin 10, fval n e T V (g j) = 0 := by
    intro j; unfold fval
    have hv : (g j).val = 470 + j.val := rfl
    have hj := j.isLt
    have hN' : rN.val = 505 := rfl
    have hE' : rE.val = 507 := rfl
    have hT' : rT.val = 508 := rfl
    have hV' : rV.val = 509 := rfl
    have a1' : g j ≠ rN := fne (by omega)
    have a2' : g j ≠ rE := fne (by omega)
    have a3' : g j ≠ rT := fne (by omega)
    have a4' : g j ≠ rV := fne (by omega)
    rw [if_neg a1', if_neg a2', if_neg a3', if_neg a4']
  have e10 := frameLen_spec cap (sIn x) (g 0) (g 1) (by decide) w z9 (by rw [s9, hin])
    (by rw [sh9]; exact hsh _ (fne (by show 150 ≠ 113; omega))) (by rw [v9, fg]) (by rw [v9, fg]) (by omega)
  rw [← hF] at e10
  have e11 := WExec.inc (cap := cap) (g 0) (z9.setv (g 0) F) (by rw [WState.setv_val, Function.update_self]; omega)
  simp only [WState.setv_val, Function.update_self] at e11
  have hKB : K1 ≤ Bb := by rw [hBb]; exact Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))
  have e12 := incK_spec cap (g 2) K1 ((z9.setv (g 0) F).setv (g 0) (F + 1))
    (by simp [Function.update_of_ne (show g 2 ≠ g 0 by decide), v9, fg]; omega)
  simp only [WState.setv_val, Function.update_of_ne (show g 2 ≠ g 0 by decide), v9, fg, Nat.zero_add] at e12
  have p0 : PX 0 = g 2 := rfl
  have p1 : PX 1 = g 0 := rfl
  obtain ⟨z12, hz12⟩ : ∃ s, s = ((z9.setv (g 0) F).setv (g 0) (F + 1)).setv (g 2) K1 := ⟨_, rfl⟩
  rw [← hz12] at e12
  have v12 : ∀ q, z12.val q = if q = g 2 then K1 else if q = g 0 then F + 1 else fval n e T V q := by
    intro q; rw [hz12]; simp only [WState.setv_val]
    by_cases h1 : q = g 2
    · subst h1; rw [Function.update_self, if_pos rfl]
    · rw [Function.update_of_ne h1, if_neg h1]
      by_cases h2 : q = g 0
      · subst h2; rw [Function.update_self, if_pos rfl]
      · rw [Function.update_of_ne h2, Function.update_of_ne h2, if_neg h2, v9]
  obtain ⟨c13, e13, hc13⟩ := powN_spec cap PX Bb (by omega) D3 z12
    (by show z12.val (g 3) = 0; rw [v12, if_neg (by decide), if_neg (by decide), fg])
    (by show z12.val (g 4) = 0; rw [v12, if_neg (by decide), if_neg (by decide), fg])
    (by show z12.val (g 5) = 0; rw [v12, if_neg (by decide), if_neg (by decide), fg])
    (by show z12.val (g 6) = 0; rw [v12, if_neg (by decide), if_neg (by decide), fg])
    (by rw [p1, v12, if_neg (by decide), if_pos rfl]; omega)
    (fun j hj => by
      rw [p0, p1, v12, v12, if_pos rfl, if_neg (by decide), if_pos rfl, hBb]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hj))
  rw [p0, p1, v12, v12, if_pos rfl, if_neg (show g 0 ≠ g 2 by decide), if_pos rfl, ← hBb] at e13
  rw [p1, v12, if_neg (show g 0 ≠ g 2 by decide), if_pos rfl] at hc13
  -- the rewind
  have e14 := wrewind_spec cap (sk x 113) (g 2) Bb (z12.setv (g 2) Bb) (by simp) (by simp; omega)
  have e15 := wclear_spec cap (g 0) (F + 1) (((z12.setv (g 2) Bb).setv (g 2) 0).seth (sk x 113)
    ((z12.setv (g 2) Bb).sh (sk x 113) - Bb))
    (by rw [WState.seth_val, WState.setv_val, Function.update_of_ne (show g 0 ≠ g 2 by decide), WState.setv_val,
        Function.update_of_ne (show g 0 ≠ g 2 by decide), v12, if_neg (show g 0 ≠ g 2 by decide), if_pos rfl])
    (by rw [WState.seth_val, WState.setv_val, Function.update_of_ne (show g 0 ≠ g 2 by decide), WState.setv_val,
        Function.update_of_ne (show g 0 ≠ g 2 by decide), v12, if_neg (show g 0 ≠ g 2 by decide), if_pos rfl]; omega)
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 (WExec.seq e11 (WExec.seq e12 (WExec.seq e13
    (WExec.seq e14 e15)))))))))))))) ?_ le_rfl, ?_⟩
  · apply WState.eq
    · funext i
      simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
      rw [hz12]
      simp only [WState.setv_sh]
      rw [sh9]
      split_ifs with hi
      · subst hi; rw [h113]; omega
      · exact hsh i hi
    · simp only [WState.setv_st, WState.seth_st]; rw [hz12]; simp only [WState.setv_st]; exact s9
    · funext q
      simp only [WState.setv_val, WState.seth_val]
      by_cases h1 : q = g 0
      · subst h1; rw [Function.update_self, fg]
      · rw [Function.update_of_ne h1]
        by_cases h2 : q = g 2
        · subst h2; rw [Function.update_self, fg]
        · rw [Function.update_of_ne h2, Function.update_of_ne h2, v12, if_neg h2, if_neg h1]
    · simp only [WState.setv_cell, WState.seth_cell]
      rw [hz12]; simp only [WState.setv_cell]; rw [hz9]; simp only [WState.setv_cell]; exact cl6
  · obtain ⟨M, hMd⟩ : ∃ v, v = B0 + V + Bb + n + e + T + F + K1 + D3 + 2 := ⟨_, rfl⟩
    rw [← hMd]
    have hM2 : 2 ≤ M := by omega
    have hMM : M ≤ M * M := Nat.le_mul_of_pos_left _ (by omega)
    have hMMM : M * M ≤ M * M * M := Nat.le_mul_of_pos_right _ (by omega)
    have hL := rsF_length
    obtain ⟨RL, hRL⟩ : ∃ v, v = rsF.length := ⟨_, rfl⟩
    rw [← hRL] at hc1 hL
    have hcl : RL * (3 * B0 + 2) ≤ 1536 * M := by
      calc RL * (3 * B0 + 2) ≤ 512 * (3 * B0 + 2) := Nat.mul_le_mul_right _ hL
        _ ≤ 512 * (3 * M) := Nat.mul_le_mul_left _ (by omega)
        _ = 1536 * M := by ring
    have hB0M : B0 + 1 ≤ M := by omega
    have hb1M : b1 + 1 ≤ M := by have := hval (SymDec.G 41); rw [← hb1] at this; omega
    have hq1M : q1 + 1 ≤ M := by omega
    have hm1 : mulCost a1 b1 ≤ 60 * (M * M) := by
      refine le_trans hcm1 ?_
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hB0M hb1M)
    have hm2 : mulCost (a1 * b1) q1 ≤ 60 * (M * M) := by
      refine le_trans hcm2 ?_
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hB0M hq1M)
    have hp : c13 ≤ 61 * (M * M * M) := by
      refine le_trans hc13 ?_
      have h1 : (Bb + 1) * (F + 1 + 1) ≤ M * M := Nat.mul_le_mul (by omega) (by omega)
      have h2 : D3 * ((Bb + 1) * (F + 1 + 1)) ≤ M * (M * M) := Nat.mul_le_mul (by omega) h1
      have h3 : D3 ≤ M * M * M := by omega
      have e' : D3 * (60 * (Bb + 1) * (F + 1 + 1) + 1) = 60 * (D3 * ((Bb + 1) * (F + 1 + 1))) + D3 := by ring
      have e'' : M * (M * M) = M * M * M := by ring
      rw [e']; rw [e''] at h2; omega
    have hpow3 : M ^ 3 = M * M * M := by ring
    rw [hpow3]
    have hMle : B0 + V + Bb + n + e + T + F + K1 + 2 ≤ M := by rw [hMd]; omega
    exact fin_arith c1 c13 _ _ V b1 q1 n e T F K1 Bb M _ (M * M) (M * M * M) B0 hc1 hcl hm1 hm2 hp hMle hb1M hq1M
      hMM hMMM

end Bank

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
