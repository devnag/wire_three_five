import Proof.Wire_3_5.Primitive.SeedFix.C4CapA
import Proof.Wire_3_5.Primitive.SeedFix.C4SN

/-! # C4 cap re-type, part 3: the SYM setup with the numbers machine at capacity `2^m`

P3:2929-2941, 2994-3000 (the seed field `ℓ ≥ max(k, ⌈log₂(Q+1)⌉)` and the sample count `Q` of `samp:q`, held in the
numbers machine's registers), P3:3011-3016 (the setup before the loop). The SYM setup (`C4Set.Lay.setup_run`) runs
the numbers machine at the fill count `C_W(n+1)^D`, a fixed polynomial, below `Q` and `n_T·2^w` at row B. Here the
front's third power is replaced by the capacity chain (`C4Cap.capM`, docked on the same region, its output on `gUW`), so
the numbers machine (`midM`, unchanged) runs at `2·2^m + 2`, `m = capExp C n = C·(B+1)²`:

* `offC`, `frontM2`, `frontCost2`, **`front_run2`** (the front, `D ≥ 16` a layout hypothesis);
* **`mid_run2`** (`mid_run` at any fill count `W`, same machine `midM`);
* `setupM2`, `setupCost2`, **`setup_run2`** (`setup_run` with the capacity `2^{capExp C n}`; the exit bank verbatim).

Paper quantities of the main type: the loop's entry words and the finisher's inputs on their tapes, with the
numbers at the call's `Q`, `n_T·2^w`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Cap
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Front
variable (L : Lay)

/-- The capacity chain's region: its tape `35` on `gUW`. -/
def offC : ℕ := 14 + 6 * L.D

theorem U_D : L.U = 14 + 2 * L.D := rfl
theorem outD : (UnaryCalc.outputTape L.D).val = 3 + 2 * L.D := rfl

end Front

section Mid
variable (L : Lay)

/-- **The numbers' run at any fill count `W`** (`mid_run`, whose proof never reads the form of `W`). -/
theorem mid_run2 (F : FreeProg) (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) (n CL Cd W : ℕ) (w : List Bool)
    (cs : List ℕ) (cD : ℕ)
    (hd : ∃ (tout : Fin (Data.DS + 2 + Data.DR) → List Bool) (m : ℕ), Step Data.dataM cD (fun _ => 0)
      (Fin.addCases (Data.rawIn w n (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n))
        (fun _ : Fin 1 => List.replicate 0 false))
      (fun _ => 0) (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape Data.sOUT) = Data.dataWord cs ∧ tout (sTape Data.sIN) = frame w)
    (τ : WState (LNS 0) LNR) (c : ℕ)
    (hx : WExec (2 * W + 2) (bigW F cr fe ζ Cδ C) (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList cs)) τ c)
    (hτ0 : τ.st (sk 0 0) = frame w) (wd : Fin 39 → List Bool) (hτ : ∀ j, τ.st (sk 0 (symO j)) = wd j)
    (B : Fin L.N → List Bool) (hP0 : B L.gP0 = frame w) (hN : B L.gN1 = List.replicate n true)
    (hL : B L.gUL = List.replicate (UnaryCalc.value L.D CL n) true)
    (hD : B L.gUD = List.replicate (UnaryCalc.value L.D Cd n) true)
    (hW : B L.gUW = List.replicate W true) (hbl : ∀ i : Fin L.N, L.oDA ≤ i.val → B i = []) :
    ∃ B' : Fin L.N → List Bool, Step (L.midM F cr fe ζ Cδ C)
        (Lay.midCost cD (Data.unaryList cs) W c) (fun _ => 0) B (fun _ => 0) B' ∧
      B' L.gP0 = frame w ∧ (∀ j, B' (L.gW j) = wd j) ∧ (∀ i : Fin L.N, i.val < 3 → i ≠ L.gP0 → B' i = B i) ∧
      (∀ i : Fin L.N, L.oM1 ≤ i.val → B' i = []) := by
  have hU := L.U_pos
  have ho := L.out_lt
  have hUe := L.U_eq
  have eDS : Data.DS = 9883 := rfl
  have eDR : Data.DR = 16 := rfl
  have eBX : BX = 676 := rfl
  have eBT : BT = 674 := rfl
  have eUC : UnaryCalc.tapes L.D = RepairSource.ProjectionNormalization.DimensionPolynomial.tapes L.D := rfl
  -- 6: the data stage
  obtain ⟨td, md, h6, e6o, e6i⟩ := hd
  obtain ⟨B6, s6, bl6, un6, pv6, ex6⟩ := stageE h6 L.oDA (by unfold Lay.oDA; rw [Lay.N_eq]; omega) L.extDA
    (fun i j g hi hj => by
      unfold Lay.extDA at hi hj
      split_ifs at hi hj <;> simp at hi hj <;> subst_vars <;>
        first
        | exact Fin.ext (by omega)
        | (exfalso; revert hj; lv))
    (fun i g hi => by
      unfold Lay.extDA at hi
      split_ifs at hi <;> simp at hi <;> subst hi <;> lv)
    B
    (fun j g hj => by
      unfold Lay.extDA at hj
      split_ifs at hj with a0 a2 a3 a4 <;> simp at hj <;> subst hj <;> rw [ac_lt _ _ j (by omega)]
      · rw [hP0]; simp [Data.rawIn, Fin.ext_iff, vIN, a0]
      · rw [hN]; simp [Data.rawIn, Fin.ext_iff, vIN, vNT, a2]
      · rw [hL]; simp [Data.rawIn, Fin.ext_iff, vIN, vNT, vLT, a3]
      · rw [hD]; simp [Data.rawIn, Fin.ext_iff, vIN, vNT, vLT, vCT, a4])
    hbl
    (fun j hj => by
      unfold Lay.extDA at hj
      split_ifs at hj with a0 a2 a3 a4 <;> simp at hj
      by_cases hlt : j.val < Data.DS + 2 + Data.DR
      · rw [ac_lt _ _ j hlt]
        simp [Data.rawIn, Fin.ext_iff, vIN, vNT, vLT, vCT, a0, a2, a3, a4]
      · rw [ac_ge _ _ j (by omega)]
        rfl)
  have f6P0 : B6 L.gP0 = frame w := by
    rw [ex6 ⟨0, by norm_num⟩ L.gP0 (by simp [Lay.extDA]), ac_lt _ _ _ (by norm_num)]
    exact e6i
  have f6DO : B6 L.gDO = Data.dataWord cs := by
    rw [pv6 ⟨6, by norm_num⟩ L.gDO (by simp [Lay.extDA]) (by lv), ac_lt _ _ _ (by norm_num)]
    exact e6o
  have f6W : B6 L.gUW = List.replicate W true :=
    (un6 _ (by lv) (L.extDA_ne _ (by lv) (by lv) (by lv) (by lv))).trans hW
  -- 7: the copy-in
  obtain ⟨t7, h7, e72⟩ := cpS (Data.unaryList cs)
  obtain ⟨B7, s7, bl7, un7, pv7, ex7⟩ := stage0 h7 (by norm_num) L.oCP (by unfold Lay.oCP; rw [Lay.N_eq]; omega) L.gDO (by lv) B6
    (by rw [f6DO]; unfold Data.dataWord; rw [Modulus.frame_eq_marks])
    (fun i hi => bl6 i (by unfold Lay.oCP at hi; unfold Lay.oDA; omega))
  have f7P0 : B7 L.gP0 = frame w := (un7 _ (by lv) (by lv)).trans f6P0
  have f7W : B7 L.gUW = List.replicate W true := (un7 _ (by lv) (by lv)).trans f6W
  have f7U : B7 L.gU = Data.unaryList cs := (pv7 ⟨2, by norm_num⟩ L.gU (by norm_num) (by lv)).trans e72
  -- 8: the numbers machine
  obtain ⟨m8, h8⟩ := big_step (bigW F cr fe ζ Cδ C) w (Data.unaryList cs) W τ c hx
  obtain ⟨B8, s8, bl8, un8, pv8, ex8⟩ := stageE h8 L.oBG (by unfold Lay.oBG; rw [Lay.N_eq]; omega) L.extBG
    (fun i j g hi hj => by
      unfold Lay.extBG at hi hj
      split_ifs at hi hj <;> simp at hi hj <;> subst_vars <;>
        first
        | exact Fin.ext (by omega)
        | (exfalso; revert hj; lv))
    (fun i g hi => by
      unfold Lay.extBG at hi
      split_ifs at hi <;> simp at hi <;> subst hi <;> lv)
    B7
    (fun j g hj => by
      unfold Lay.extBG at hj
      split_ifs at hj with a0 a2 a3 <;> simp at hj <;> subst hj <;> rw [ac_lt _ _ j (by omega)]
      · rw [f7P0]; simp [rawB, Fin.ext_iff, vb0, a0]
      · rw [f7U]; simp [rawB, Fin.ext_iff, vb0, vb113, a2]
      · rw [f7W]; simp [rawB, Fin.ext_iff, vb0, vb113, vcnt, a3])
    (fun i hi => bl7 i (by unfold Lay.oBG at hi; unfold Lay.oCP; omega))
    (fun j hj => by
      unfold Lay.extBG at hj
      split_ifs at hj with a0 a2 a3 <;> simp at hj
      by_cases hlt : j.val < BX
      · rw [ac_lt _ _ j hlt]
        simp [rawB, Fin.ext_iff, vb0, vb113, vcnt, a0, a2, a3]
      · rw [ac_ge _ _ j (by omega)])
  refine ⟨B8, s6.seq (s7.seq s8), ?_, ?_, ?_, ?_⟩
  · rw [ex8 ⟨0, by norm_num⟩ L.gP0 (by simp [Lay.extBG]), ac_lt _ _ _ (by norm_num), ac_lt _ _ _ (by norm_num)]
    have e : (⟨0, by norm_num⟩ : Fin BT) = sTape (nr := LNR) (sk 0 0) := rfl
    rw [e, wenc_A_s, hτ0]
  · intro j
    have hs1 := Lay.symO_ge j
    have hs2 := Lay.symO_le j
    have hne : symO j ≠ 0 := fun e => by rw [e] at hs1; simp at hs1
    have hx : L.extBG ⟨1 + (symO j).val, by omega⟩ = none := by
      unfold Lay.extBG
      simp only [Fin.val_mk]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [pv8 ⟨1 + (symO j).val, by omega⟩ (L.gW j) hx (by lv), ac_lt _ _ _ (by simp; omega),
      ac_lt _ _ _ (by simp; omega)]
    have e : (⟨1 + (symO j).val, by omega⟩ : Fin BT) = sTape (nr := LNR) (sk 0 (symO j)) :=
      Fin.ext (by simp [sTape, sk, hne] <;> omega)
    rw [e, wenc_A_s, hτ]
  · intro i hi hne
    have n2 : i ≠ L.gU := fun e => by rw [e] at hi; revert hi; lv
    have n3 : i ≠ L.gUW := fun e => by rw [e] at hi; revert hi; lv
    have n4 : i ≠ L.gDO := fun e => by rw [e] at hi; revert hi; lv
    have n5 : i ≠ L.gN1 := fun e => by rw [e] at hi; revert hi; lv
    have n6 : i ≠ L.gUL := fun e => by rw [e] at hi; revert hi; lv
    have n7 : i ≠ L.gUD := fun e => by rw [e] at hi; revert hi; lv
    rw [un8 i (by unfold Lay.oBG; omega) (L.extBG_ne i hne n2 n3), un7 i (by unfold Lay.oCP; omega) n4,
      un6 i (by unfold Lay.oDA; omega) (L.extDA_ne i hne n5 n6 n7)]
  · intro i hi
    exact bl8 i (by unfold Lay.oBG; unfold Lay.oM1 at hi; omega)

end Mid

section Setup

end Setup

end NearCubicWires.WireExponent3_5.PrimT.C4Cap
