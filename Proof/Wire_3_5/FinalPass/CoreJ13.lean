import Proof.Wire_3_5.FinalPass.CoreJ12

/-! # S5Core over the writers with arbitrary residues, part J13: the writers' stages (P3:3044-3048, 3170-3181)

* **`stageABNJ`**: S4's words part A (slots `0 … 3`), part B (slots `4 … 7`) and the numbers (`tN`, `tD`) written by
  their machine writers (`wstageJ`), the room invariant moved to the SYM block, the reference, the mode tape and every
  other tape kept;
* **`stageSJ`**: the branch on the mode tape: at a SYM request the SYM words written (`SymWordsMJ`), at a THR request
  nothing.

Paper quantities: S4's own words, the printed numbers' start, the SYM evaluator's call words (P3:3044-3048,
3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Run
variable {l : Literals} (W : CoreWritersJ l) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {mTh : ℕ}
  (L : S5Lay Sw0.nw) (hR : Bank.HalfRoom2 L mTh (mCoreOfJ W))

/-- The mode tape's index in the room. -/
def iMbJ : Fin (mCoreOfJ W) := ⟨9, Nat.lt_of_lt_of_le (by decide : 9 < 5 + (3 + 2 + 0)) (h10WJ W)⟩

theorem Mb_idxJ : MbJ W L hR = hR.coreE (iMbJ W) := by
  unfold MbJ blk iMbJ; congr 1

/-- **Parts A, B and the numbers.** -/
theorem stageABNJ (r : FReq l F kclk coef A a ha) (c : ℕ) (A2 : Fin L.t → List Bool)
    (hin : A2 (i0 L) = frame (fpIn l F kclk coef A a ha r)) (hT : A2 (TcJ W L hR) = sent c)
    (hinv : RInv L hR c A2 10) (hwd : ∀ k, ¬ thrSlot k → A2 (L.wd k) = []) (htN : A2 L.tN = []) (htD : A2 L.tD = [])
    (hKA : W.SA.Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SA.Dk F.filterErrDeg ≤ c)
    (hSA : W.SA.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SA.Ds F.filterErrDeg ≤ c)
    (hKB : W.SB.Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SB.Dk F.filterErrDeg ≤ c)
    (hSB : W.SB.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SB.Ds F.filterErrDeg ≤ c)
    (hKN : W.NW.Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.NW.Dk F.filterErrDeg ≤ c)
    (hSN : W.NW.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.NW.Ds F.filterErrDeg ≤ c) :
    ∃ A3 A4 A5 : Fin L.t → List Bool,
      Step (wstageM L hR (W.SA.M F) W.SA.sIn W.SA.sOut (outA L) 10 (hAWJ W) (TcJ W L hR))
        (W.SA.nr * (6 * c + 17) + 1 + 1 + 1 + W.SA.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^
          W.SA.Ds F.filterErrDeg) (fun _ => 0) A2 (fun _ => 0) A3 ∧
      Step (wstageM L hR (W.SB.M F) W.SB.sIn W.SB.sOut (outB L) (oBJ W) (hBWJ W) (TcJ W L hR))
        (W.SB.nr * (6 * c + 17) + 1 + 1 + 1 + W.SB.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^
          W.SB.Ds F.filterErrDeg) (fun _ => 0) A3 (fun _ => 0) A4 ∧
      Step (wstageM L hR (W.NW.M F) W.NW.sIn W.NW.sOut (outN L) (oNJ W) (hNWJ W) (TcJ W L hR))
        (W.NW.nr * (6 * c + 17) + 1 + 1 + 1 + W.NW.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^
          W.NW.Ds F.filterErrDeg) (fun _ => 0) A4 (fun _ => 0) A5 ∧
      (∀ k, A5 (outA L k) = frontWordsW2 l F kclk coef A a ha Sw0 r (s4SlotA k)) ∧
      (∀ k, A5 (outB L k) = frontWordsW2 l F kclk coef A a ha Sw0 r (s4SlotB k)) ∧
      (∀ i, A5 (outN L i) = frame (binary (Sd.R.Tf l F kclk coef A a ha r)
        ((![0, fpDen l F kclk coef A a ha r] : Fin 2 → ℕ) i))) ∧
      A5 (i0 L) = frame (fpIn l F kclk coef A a ha r) ∧ A5 (TcJ W L hR) = sent c ∧ RInv L hR c A5 (oSJ W) ∧
      A5 (MbJ W L hR) = A2 (MbJ W L hR) ∧
      (∀ y, (∀ i, hR.coreE i ≠ y) → (∀ k, y ≠ outA L k) → (∀ k, y ≠ outB L k) → (∀ k, y ≠ outN L k) →
        A5 y = A2 y) := by
  have hiT : (iTcJ W L).val < 10 := by have := iTc_ltJ W L; omega
  have hA2A : ∀ k, A2 (outA L k) = [] := fun k => hwd _ (by
    rintro ⟨h1, _⟩; simp [s4SlotA] at h1; have := k.isLt; omega)
  obtain ⟨A3, s3, a3o, a3in, a3inv, a3T, a3keep, a3room⟩ := wstageJ L hR (W.SA.M F) W.SA.sIn W.SA.sOut W.SA.out_ne
    (outA L) (outA_inj L) (fun k => wd_ne0 L _) (fun k i => wd_neRJ W L hR _ i) 10 (hAWJ W) (iTcJ W L) hiT c _ _
    hKA hSA _ (fun k => frontWordsW2 l F kclk coef A a ha Sw0 r (s4SlotA k))
    (fun σ h1 h2 h3 h4 h5 => W.SA.run F kclk coef A a ha r σ h1 h2 h3 h4 h5) A2 hin hA2A hinv hT
  have hA3B : ∀ k, A3 (outB L k) = [] := fun k => by
    rw [a3keep (outB L k) (fun i e => wd_neRJ W L hR _ i e.symm) (fun k' e => outA_ne_outB L k' k e.symm)]
    exact hwd _ (by rintro ⟨h1, _⟩; simp [s4SlotB] at h1; have := k.isLt; omega)
  have hiT2 : (iTcJ W L).val < oBJ W := by unfold oBJ; omega
  obtain ⟨A4, s4, a4o, a4in, a4inv, a4T, a4keep, a4room⟩ := wstageJ L hR (W.SB.M F) W.SB.sIn W.SB.sOut W.SB.out_ne
    (outB L) (outB_inj L) (fun k => wd_ne0 L _) (fun k i => wd_neRJ W L hR _ i) (oBJ W) (hBWJ W) (iTcJ W L) hiT2 c _ _
    hKB hSB _ (fun k => frontWordsW2 l F kclk coef A a ha Sw0 r (s4SlotB k))
    (fun σ h1 h2 h3 h4 h5 => W.SB.run F kclk coef A a ha r σ h1 h2 h3 h4 h5) A3 a3in hA3B a3inv a3T
  have hA4N : ∀ k, A4 (outN L k) = [] := fun k => by
    rw [a4keep (outN L k) (fun i e => outN_neRJ W L hR k i e.symm) (fun k' e => wd_ne_outN L _ k e.symm),
      a3keep (outN L k) (fun i e => outN_neRJ W L hR k i e.symm) (fun k' e => wd_ne_outN L _ k e.symm)]
    fin_cases k
    · exact htN
    · exact htD
  have hiT3 : (iTcJ W L).val < oNJ W := by unfold oNJ oBJ; omega
  obtain ⟨A5, s5, a5o, a5in, a5inv, a5T, a5keep, a5room⟩ := wstageJ L hR (W.NW.M F) W.NW.sIn W.NW.sOut W.NW.out_ne
    (outN L) (outN_inj L) (outN_ne0 L) (outN_neRJ W L hR) (oNJ W) (hNWJ W) (iTcJ W L) hiT3 c _ _
    hKN hSN _ (fun i => frame (binary (Sd.R.Tf l F kclk coef A a ha r)
      ((![0, fpDen l F kclk coef A a ha r] : Fin 2 → ℕ) i)))
    (fun σ h1 h2 h3 h4 h5 => W.NW.run F kclk coef A a ha r σ h1 h2 h3 h4 h5) A4 a4in hA4N a4inv a4T
  refine ⟨A3, A4, A5, s3, s4, s5, fun k => ?_, fun k => ?_, a5o, a5in, a5T, a5inv, ?_, fun y hy hA hB hN => ?_⟩
  · rw [a5keep (outA L k) (fun i e => wd_neRJ W L hR _ i e.symm) (fun k' e => wd_ne_outN L _ k' e),
      a4keep (outA L k) (fun i e => wd_neRJ W L hR _ i e.symm) (fun k' e => outA_ne_outB L k k' e), a3o]
  · rw [a5keep (outB L k) (fun i e => wd_neRJ W L hR _ i e.symm) (fun k' e => wd_ne_outN L _ k' e), a4o]
  · rw [Mb_idxJ, a5room _ (Or.inl (show 9 < oNJ W by unfold oNJ oBJ; omega)),
      a4room _ (Or.inl (show 9 < oBJ W by unfold oBJ; omega)), a3room _ (Or.inl (show 9 < 10 by omega))]
  · rw [a5keep y hy hN, a4keep y hy hB, a3keep y hy hA]

end Run

end NearCubicWires.WireExponent3_5.FinalPass.Core
