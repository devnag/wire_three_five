import Proof.Wire_3_5.Primitive.SeedFix.C4HfJ

/-! # The HASH child family, part 11: the HASH child's run

`filt:soft`, P3:2331-2335, P3:3034-3037: **`core_stepH`**: from the child's entry bank at the prefix `p`, the three stages
(the Hb unit, the assembler, the printer child) leave `frame (binary W (chValH (p ++ [b])))` on the sum port, the kept
tapes unchanged.

Paper quantity of the main type: the recovered child sum `chValH` of the printed hash objective. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.HbM NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairRepresentation

noncomputable section

section Run
variable (A : C4Iface.AsmStage) (wa : WilliamsAlgorithm) (a : DecompositionAlgorithm)
  (R0 : CompilerMachine.Req.C3Req) (D : HashData) (c : HbCaps)

/-- The child's entry bank of the prefix `p`. -/
def hChInP (p : List Bool) : Fin (CTH A wa) → List Bool :=
  hChIn A wa (C4Child.pre a R0) (C4Child.post a R0) (hb0 (hbX D c 0 0)) (List.replicate R0.P.Q true)
    (List.replicate (2 ^ R0.dRow * 2 ^ R0.dRow) true) p

/-- The child's steps. -/
def hCoreSteps (Kc : ℕ) (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request) : ℕ :=
  unitCost D c Kc p b + 1 + (C4Iface.asmCost (C4Child.pre a R0) (C4Child.post a R0) (hV D (p ++ [b])) + 1 +
    C4Pipe.childCost wa a (hR R0 D (p ++ [b])) r)

/-- **The HASH child's three stages**: the sum port holds `frame (binary W (chValH (p ++ [b])))`; the kept tapes
are unchanged. -/
theorem core_stepH (E : Cost.Envelope) (Kc : ℕ) (b : Bool) (p : List Bool)
    (hplen : p.length + 1 ≤ 2 * D.MP.t * D.MP.ell0) (hcC : 2 * D.MP.t * D.MP.ell0 ≤ c.cC)
    (hok : (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).HbOk)
    (hcell : ∀ cc < (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).n,
      (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).CellOk cc)
    (hK : ∀ cc < (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).n,
      (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).cellCost cc ≤ Kc)
    (hRp : (hR R0 D (p ++ [b])).Pre a) (hQp : R0.P.Q ≤ R0.p) :
    ∃ r : MatrixScoreBatch.Request,
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord R0.dRow (R0.p + 1) R0.P.width R0.cols
        (CompilerMachine.Req.c3v2Ref a (hR R0 D (p ++ [b]))) ∧
      ∃ (H' : Fin (CTH A wa) → ℕ) (A' : Fin (CTH A wa) → List Bool),
        Step (coreMH A wa b) (hCoreSteps wa a R0 D c Kc p b r) (fun _ => 0) (hChInP A wa a R0 D c p) H' A' ∧
        A' (hSumT A wa) = frame (binary (C4Child.chW R0) (chValH R0 D (p ++ [b]))) ∧
        ∀ i, hKeepC A wa i = true → A' i = hChInP A wa a R0 D c p i := by
  set KW := hb0 (hbX D c 0 0) with hKW
  set B0 := hChInP A wa a R0 D c p with hB0
  -- 1: the Hb unit
  obtain ⟨Au, su, hOut, hLow⟩ := unit_step D c Kc p b hplen hcC hok hcell hK
  have h0 : ∀ u, B0 (hUnSl A wa u) = uIn KW p u := by
    intro u
    by_cases hu : u.val = 95
    · have e : hUnSl A wa u = Fin.castAdd _ A.pE := by rw [hUnSl, if_pos hu]
      rw [e]
      have h95 : uIn KW p u = [] := by
        simp only [uIn]; rw [dif_neg (by omega), if_neg (by omega)]
      rw [h95]
      simp [hB0, hChInP, hChIn, C4Child.asmK, Ne.symm A.hAE, Ne.symm A.hBE]
    · have e : hUnSl A wa u = Fin.natAdd A.t (Fin.castAdd (C4Pipe.CN wa) u) := by rw [hUnSl, if_neg hu]
      rw [e]
      simp [hB0, hChInP, hChIn, hKW]
  have s1 := su.dock (hUnSl A wa) (hUnSl_inj A wa) (fun _ => 0) B0 (fun _ => rfl) h0
  rw [C4Pipe.dockH_zero'] at s1
  set B1 := install (hUnSl A wa) B0 Au with hB1
  -- 2: the assembler
  obtain ⟨Aa, sa, haO, haA, haB⟩ := A.run (C4Child.pre a R0) (C4Child.post a R0) (hV D (p ++ [b])) []
  have h1 : ∀ i, B1 (hAsmSl A wa i) =
      C4Iface.asmIn A.pA A.pB A.pE (C4Child.pre a R0) (C4Child.post a R0) (hV D (p ++ [b])) [] i := by
    intro i
    by_cases hiE : i = A.pE
    · have e : hAsmSl A wa i = hUnSl A wa ⟨95, by rw [HU_eq]; omega⟩ := by
        rw [hUnSl, if_pos rfl, hiE]; rfl
      rw [e, hB1, install_slot _ (hUnSl_inj A wa), hOut, hiE]
      simp [C4Iface.asmIn, Ne.symm A.hAE, Ne.symm A.hBE]
    · rw [hB1, install_other _ _ _ _ (fun u => un_ne_asm A wa u i hiE)]
      simp [hB0, hChInP, hChIn, hAsmSl, C4Child.asmK, C4Iface.asmIn, hiE]
  have s2 := sa.dock (hAsmSl A wa) (hAsmSl_inj A wa) (fun _ => 0) B1 (fun _ => rfl) h1
  rw [C4Pipe.dockH_zero'] at s2
  set B2 := install (hAsmSl A wa) B1 Aa with hB2
  -- 3: the printer child
  obtain ⟨r, hw, hd, hpr, _, hcols, H', Ac, sc, hSum, hQQ, hUU⟩ :=
    C4Child.child_step_w wa a E (hR R0 D (p ++ [b])) hRp hQp
  have h2 : ∀ k, B2 (hCmSl A wa k) = C4Pipe.childIn wa
      (frame (CompilerMachine.Req.c3Input a (hR R0 D (p ++ [b]))))
      (List.replicate (hR R0 D (p ++ [b])).P.Q true)
      (List.replicate (2 ^ (hR R0 D (p ++ [b])).dRow * 2 ^ (hR R0 D (p ++ [b])).dRow) true) k := by
    intro k
    by_cases hk : k = C4Child.pdT wa
    · have e : hCmSl A wa k = hAsmSl A wa A.pO := by rw [hCmSl, if_pos hk]; rfl
      have hpd : ∀ X y z, C4Pipe.childIn wa X y z (C4Child.pdT wa) = X := fun X y z => by
        simp [C4Pipe.childIn, C4Child.pdT]
      rw [e, hB2, install_slot _ (hAsmSl_inj A wa), haO, hk, hpd, C4Child.c3Input_split]
      rfl
    · have e : hCmSl A wa k = Fin.natAdd A.t (Fin.natAdd HU k) := by rw [hCmSl, if_neg hk]
      have hne1 : ∀ i, hAsmSl A wa i ≠ hCmSl A wa k := fun i e' => by
        have hv := congrArg Fin.val e'
        rw [hAsmSl_val, hCmSl_val, if_neg hk] at hv
        have := i.isLt; omega
      have hne2 : ∀ u, hUnSl A wa u ≠ hCmSl A wa k := fun u e' => cm_ne_un A wa k u e'.symm
      rw [hB2, install_other _ _ _ _ hne1, hB1, install_other _ _ _ _ hne2, e]
      have hkv : k.val ≠ C4Pipe.PD wa := fun h => hk (Fin.ext h)
      simp [hB0, hChInP, hChIn, C4Pipe.childIn, hkv, hR]
  have s3 := sc.dock (hCmSl A wa) (hCmSl_inj A wa) (fun _ => 0) B2 (fun _ => rfl) h2
  refine ⟨r, hw, _, _, s1.seq (s2.seq s3), ?_, ?_⟩
  · -- the sum
    rw [hSumT, install_slot _ (hCmSl_inj A wa), hSum]
    have hW : RepairOrdinary.CompetitorSelectedCount.scalarWidth r (hR R0 D (p ++ [b])).P.Q = C4Child.chW R0 := by
      unfold RepairOrdinary.CompetitorSelectedCount.scalarWidth C4Child.chW
      rw [RepairOrdinary.CompetitorSelectedCount.extraWidth_eq, hd, hpr]
      rfl
    have hU : r.U = 2 ^ R0.dRow := by
      show 2 ^ r.d = 2 ^ R0.dRow
      rw [hd]
      rfl
    rw [hW, C4Child.sum_fin_range r.U (fun i j => C4Pipe.lres (2 ^ ((hR R0 D (p ++ [b])).m - 1) *
      Shared.IntExpression.eval (hR R0 D (p ++ [b])).V
        (CompilerMachine.Req.atomVal (hR R0 D (p ++ [b])).P (r.phi i) (r.phi j)))
      (hR R0 D (p ++ [b])).P.Q), hU]
    simp only [MatrixScoreBatch.Request.phi, hcols]
    rfl
  · -- the kept tapes
    intro i hi
    refine Fin.addCases (motive := fun i => hKeepC A wa i = true → install (hCmSl A wa) B2 Ac i = B0 i)
      (fun x hx => ?_) (fun y hy => ?_) i hi
    · simp only [hKeepC, Fin.addCases_left, decide_eq_true_eq] at hx
      have hxO : x ≠ A.pO := by
        rcases hx with h | h <;> rw [h]
        · exact A.hAO
        · exact A.hBO
      have hc : ∀ k, hCmSl A wa k ≠ Fin.castAdd _ x := fun k => cm_ne_asmH A wa k x hxO
      rw [install_other _ _ _ _ hc]
      have e : (Fin.castAdd _ x : Fin (CTH A wa)) = hAsmSl A wa x := rfl
      rw [e, hB2, install_slot _ (hAsmSl_inj A wa)]
      rcases hx with h | h
      · rw [h, haA]; simp [hB0, hChInP, hChIn, hAsmSl, C4Child.asmK]
      · rw [h, haB]; simp [hB0, hChInP, hChIn, hAsmSl, C4Child.asmK, A.hAB.symm]
    · refine Fin.addCases (motive := fun y => hKeepC A wa (Fin.natAdd A.t y) = true →
        install (hCmSl A wa) B2 Ac (Fin.natAdd A.t y) = B0 (Fin.natAdd A.t y)) (fun u hu => ?_) (fun k hk => ?_) y hy
      · -- the unit's kept tapes
        simp only [hKeepC, Fin.addCases_right, Fin.addCases_left, decide_eq_true_eq] at hu
        have hu95 : u.val ≠ 95 := by omega
        have e : Fin.natAdd A.t (Fin.castAdd (C4Pipe.CN wa) u) = hUnSl A wa u := by rw [hUnSl, if_neg hu95]
        have hc : ∀ k, hCmSl A wa k ≠ hUnSl A wa u := fun k => cm_ne_un A wa k u
        have ha : ∀ i', hAsmSl A wa i' ≠ hUnSl A wa u := fun i' e' => by
          have hv := congrArg Fin.val e'
          rw [hAsmSl_val, hUnSl_val, if_neg hu95] at hv
          have := i'.isLt; omega
        rw [e, install_other _ _ _ _ hc, hB2, install_other _ _ _ _ ha, hB1, install_slot _ (hUnSl_inj A wa),
          hLow u (by omega), ← h0 u]
      · -- the printer child's `1^Q` and mask
        simp only [hKeepC, Fin.addCases_right, decide_eq_true_eq] at hk
        have hkP : k ≠ C4Child.pdT wa := by
          rcases hk with h | h <;> rw [h]
          · exact C4Child.childQQ_ne wa
          · exact C4Child.childUU_ne wa
        have e : Fin.natAdd A.t (Fin.natAdd HU k) = hCmSl A wa k := by rw [hCmSl, if_neg hkP]
        have hl : install (hCmSl A wa) B2 Ac (Fin.natAdd A.t (Fin.natAdd HU k)) = Ac k := by
          rw [e, install_slot _ (hCmSl_inj A wa)]
        rw [hl]
        rcases hk with h | h
        · rw [h, hQQ]
          simp only [hB0, hChInP, hChIn, Fin.addCases_right]
          simp [C4Pipe.childIn, C4Pipe.childQQ, hR]
        · rw [h, hUU]
          simp only [hB0, hChInP, hChIn, Fin.addCases_right]
          simp [C4Pipe.childIn, C4Pipe.childUU, hR]

end Run

end

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
