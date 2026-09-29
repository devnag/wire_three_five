import Proof.Wire_3_5.Primitive.Writers.C3WMachine

/-! # C3 request writer, part 12: the inner run

Paper quantity: `frame PRE` and `frame POST` of alg:compiler's request (P3:1886-1906) on the writer's output
streams. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.C3Phase NearCubicWires.WireExponent3_5.PrimAsm.C3Dock
open NearCubicWires.WireExponent3_5.PrimAsm.C3Asm NearCubicWires.WireExponent3_5.PrimAsm.C3Marks
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append)
open NearCubicWires.RepairRepresentation (natWord)

namespace Wr5
variable (P : Wr5) (Dv Cv : ℕ) {sA Ua : ℕ} (pA : Machine Ua sA) (iA oA : Fin Ua)

/-- The streams after the front and the writers. -/
def st8 (w : List Bool) (n h Q m pr W : ℕ) (GF SF WF FF CF : List Bool) : Fin (CN + 1) → List Bool :=
  wrSt (Function.update (Function.update (stIn w h Q m pr) cNT (List.replicate n true)) cCT
    (List.replicate W true)) GF SF WF FF CF

/-- The inner run's steps. -/
def runCost (w : List Bool) (n h Q m pr BG BS BW BF BC wd g wd' nc FL F gyl syl nA ysl atl S y10l : ℕ) : ℕ :=
  (P.lay Ua Dv Cv).frCost w n h Q m pr + 1 + wrCost BG BS BW BF BC + 1 +
    (2 * (11 * (P.lay Ua Dv Cv).fillW n h Q m pr + 20 + 1 + 1 + 1 +
      c1Cost (2 * (P.lay Ua Dv Cv).fillW n h Q m pr + 2) n h Q m pr wd g wd' nc FL F gyl syl) + 2) + 1 + nA + 1 +
    (2 * (5 * ysl + 11 * atl + 2 * UnaryPow.sq (2 * (P.lay Ua Dv Cv).fillW n h Q m pr + 2) +
      (nc + pr + 13) * (200 * (nc + pr + 1) + 400) + 40) + 2) + 1 +
    (2 * (5 * UnaryPow.sq (2 * (P.lay Ua Dv Cv).fillW n h Q m pr + 2) + 21 * (Q + m + h + (pr + 1) + wd) + 25 * S +
      60 * ysl + 70 * atl + 50 * ((natWord nc ++ natWord (pr + 1)).length + y10l) + 330) + 2)

/-- **The inner run**: from the writer's entry bank to `frame PRE` on `sPRE` and `frame POST` on `sPOST`, the
request and the numbers kept. -/
theorem inner_run (w sfx : List Bool) (n h Q m pr : ℕ) (hw : w = natWord n ++ sfx)
    (GF SF WF FF CF : List Bool) (BG BS BW BF BC : ℕ)
    (rG : WriterIfaceJ.WriterRun P.G.M BG P.G.inS P.G.outS w GF)
    (rS : WriterIfaceJ.WriterRun P.S.M BS P.S.inS P.S.outS w SF)
    (rW : WriterIfaceJ.WriterRun P.W.M BW P.W.inS P.W.outS w WF)
    (rF : WriterIfaceJ.WriterRun P.F.M BF P.F.inS P.F.outS w FF)
    (rC : WriterIfaceJ.WriterRun P.C.M BC P.C.inS P.C.outS w CF)
    (g wd wd' : ℕ) (gyr sy : List Bool) (flips : List (List Bool)) (cols : List ℕ)
    (hGF : GF = frame (natWord g ++ gyr)) (hSF : SF = frame sy) (hWF : WF = List.replicate wd true)
    (hne : ∀ f ∈ flips, f ≠ []) (hFF : FF = flips.flatMap frame ++ [false])
    (hCF : CF = frame (natWord wd' ++ cols.flatMap fun x => frame (SignedSortKey.binary wd' x)))
    (hio : iA ≠ oA) (nA : ℕ) (tA : Fin Ua → List Bool)
    (hA : Step pA nA (fun _ => 0) (fun j => if j = iA then frame (CompilerMachine.Top.loadRec
      (List.replicate n true) (frame (natWord g ++ gyr)) (frame sy) (List.replicate wd true)
      (flips.flatMap frame ++ [false]) (List.replicate h true) (List.replicate Q true) [] [] [] []) else [])
      (fun _ => 0) tA)
    (ys : List (List Bool)) (atoms : List (List (List Bool))) (hys : ∀ y ∈ ys, y ≠ [])
    (hat : ∀ E ∈ atoms, ∀ y ∈ E, y ≠ []) (hout : tA oA = ys.flatMap frame ++ false :: atomsStream atoms)
    (hatl : atoms.length = flips.length * g)
    (hpoly : wd + g + 4 * wd' + 2 + cols.length + 1 + 2 ^ (natBitLength g + 1) + 2 ^ (natBitLength wd' + 1) +
      21 * cols.length + 61 ≤ UnaryCalc.value Dv Cv n) :
    ∃ (τ : WState CN CR) (m' : ℕ) (R : Fin (P.lay Ua Dv Cv).X → List Bool),
      Step (P.innerM Dv Cv pA iA oA) (P.runCost Dv Cv (Ua := Ua) w n h Q m pr BG BS BW BF BC wd g wd' cols.length
          (flips.flatMap frame).length flips.length (natWord g ++ gyr).length sy.length nA (ys.flatMap frame).length
          (atomsStream atoms).length (atoms.map List.length).sum
          (natWord wd' ++ cols.flatMap fun x => frame (SignedSortKey.binary wd' x)).length)
        (fun _ => 0) (P.entry Dv Cv w h Q m pr) ((P.lay Ua Dv Cv).gHead (rs τ))
        ((P.lay Ua Dv Cv).gBank (2 * (P.lay Ua Dv Cv).fillW n h Q m pr + 2) (rs τ) m' R) ∧
      τ.st sPRE = preOut Q (atoms.map List.length).sum m h (pr + 1) wd ys atoms ∧
      τ.st sPOST = postOut (natWord cols.length ++ natWord (pr + 1))
        (natWord wd' ++ cols.flatMap fun x => frame (SignedSortKey.binary wd' x)) ∧
      τ.st cIN = frame w ∧ τ.st sH = List.replicate h true ∧ τ.st sQ = List.replicate Q true ∧
      τ.st sM = List.replicate m true ∧ τ.st sP = List.replicate pr true := by
  obtain ⟨A, hA'⟩ : ∃ A, A = 2 ^ (natBitLength g + 1) := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B', B' = 2 ^ (natBitLength wd' + 1) := ⟨_, rfl⟩
  rw [← hA', ← hB'] at hpoly
  -- the front and the writers
  obtain ⟨B1, s1, i1⟩ := (P.lay Ua Dv Cv).front_run w sfx n h Q m pr hw _ _ (P.entry_inv Dv Cv w h Q m pr)
    rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨B2, s2, i2⟩ := P.wr_run Ua Dv Cv w GF SF WF FF CF BG BS BW BF BC rG rS rW rF rC B1 _ i1
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
  -- the first program
  obtain ⟨τ1, e1, t1A, _, t1T, _, t1o, _, t1v, t1c⟩ := wm1_spec (2 * (P.lay Ua Dv Cv).fillW n h Q m pr + 2)
    (σF (st8 w n h Q m pr ((P.lay Ua Dv Cv).fillW n h Q m pr) GF SF WF FF CF) ((P.lay Ua Dv Cv).fillW n h Q m pr))
    n h Q m pr wd g wd' (natWord g ++ gyr) sy (marks gyr ++ [false]) flips cols hne (fun _ => rfl) (fun _ => rfl)
    rfl rfl rfl rfl rfl (by show WF = _; exact hWF) (by show GF = _; exact hGF)
    (by show GF = _; rw [hGF, frame_eq_marks, marks_append, List.append_assoc])
    (by show SF = _; exact hSF) (by show FF = _; exact hFF) (by show FF = _; exact hFF)
    (by show CF = _; rw [hCF, frame_eq_marks, marks_append, List.append_assoc]) rfl rfl
    (by show _ ≤ 2 * (UnaryCalc.value Dv Cv n + 32 * (h + Q + m + pr)) + 2; omega)
    (by show 2 ^ (natBitLength g + 1) ≤ 2 * (UnaryCalc.value Dv Cv n + 32 * (h + Q + m + pr)) + 2; rw [← hA']; omega)
    (by show 2 ^ (natBitLength wd' + 1) ≤ 2 * (UnaryCalc.value Dv Cv n + 32 * (h + Q + m + pr)) + 2; rw [← hB']; omega)
  obtain ⟨m1, s3⟩ := (P.lay Ua Dv Cv).ph1_run B2 _ i2 ((P.lay Ua Dv Cv).fillW n h Q m pr) rfl rfl τ1 _ e1
  -- C3a′
  obtain ⟨R2, s4⟩ := (P.lay Ua Dv Cv).c3_stage pA iA oA hio nA _ tA hA (2 * (P.lay Ua Dv Cv).fillW n h Q m pr + 2)
    (rs τ1) (fun _ => rfl) m1 (fun x => B2 (Fin.natAdd (WT + 1) x)) t1A
    (by show τ1.st sAOUT = []; rw [t1o _ (by decide) (by decide)]; rfl)
    (fun k hk => i2.2.2.2.2 _ (by simp only [Fin.val_natAdd]; omega))
  -- the second program, part a
  have q2st : ∀ s, s ≠ sAIN → s ≠ sAOUT → (((rs τ1).sets sAIN (tA iA)).sets sAOUT (tA oA)).st s = τ1.st s := by
    intro s a b
    simp only [WState.sets_st]
    rw [Function.update_of_ne b, Function.update_of_ne a]
    rfl
  have q2O : (((rs τ1).sets sAIN (tA iA)).sets sAOUT (tA oA)).st sAOUT = tA oA := by
    simp only [WState.sets_st, Function.update_self]
  have q2v : (((rs τ1).sets sAIN (tA iA)).sets sAOUT (tA oA)).val = τ1.val := rfl
  have z1 : ∀ q : Fin CR, q ≠ rh → q ≠ rQ → q ≠ rm → q ≠ rpr → q ≠ rw → q ≠ rg → q ≠ rX → q ≠ rD → q ≠ rdr →
      τ1.val q = 0 := by
    intro q a1 a2 a3 a4 a5 a6 a7 a8 a9
    rw [t1v]
    exact val1_zero _ _ _ _ _ _ _ _ _ a1 a2 a3 a4 a5 a6 a7 a8 a9
  have zP1 : τ1.val rP1 = 0 := z1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have zT : τ1.val rT = 0 := z1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have zK : τ1.val rK = 0 := z1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hO2 : (((rs τ1).sets sAIN (tA iA)).sets sAOUT (tA oA)).st sAOUT = ys.flatMap frame ++ false :: atomsStream atoms := by
    rw [q2O]; exact hout
  have hT2 : (((rs τ1).sets sAIN (tA iA)).sets sAOUT (tA oA)).st sAT = List.replicate atoms.length true := by
    rw [q2st _ (by decide) (by decide), t1T, hatl]
  have hS2 : (((rs τ1).sets sAIN (tA iA)).sets sAOUT (tA oA)).st sSH = [] := by
    rw [q2st _ (by decide) (by decide), t1o _ (by decide) (by decide)]; rfl
  have hN2 : (((rs τ1).sets sAIN (tA iA)).sets sAOUT (tA oA)).st sNW = [] := by
    rw [q2st _ (by decide) (by decide), t1o _ (by decide) (by decide)]; rfl
  have hRW2 : ∀ i : Fin 8, i ≠ 0 → (((rs τ1).sets sAIN (tA iA)).sets sAOUT (tA oA)).val (RW1 i) = 0 := by
    intro i hi
    rw [q2v]
    fin_cases i
    · exact absurd rfl hi
    all_goals exact z1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨τ2, e2, t2S, t2N, t2o, _, t2v, t2P, t2c⟩ := wm2a_spec (2 * (P.lay Ua Dv Cv).fillW n h Q m pr + 2)
    (((rs τ1).sets sAIN (tA iA)).sets sAOUT (tA oA)) ys atoms cols.length pr hys hat hO2 rfl hT2 rfl hS2 rfl hN2 rfl
    (by rw [q2v, t1v, val1_rdr]) (by rw [q2v, t1v, val1_rpr])
    (by rw [q2v]; exact zP1) (by rw [q2v]; exact zT)
    hRW2 (by show _ ≤ 2 * (UnaryCalc.value Dv Cv n + 32 * (h + Q + m + pr)) + 2; omega)
  obtain ⟨m2, s5⟩ := (P.lay Ua Dv Cv).ph_run wm2a.toProg (2 * (P.lay Ua Dv Cv).fillW n h Q m pr + 2) _
    (wenc (2 * (P.lay Ua Dv Cv).fillW n h Q m pr + 2) (((rs τ1).sets sAIN (tA iA)).sets sAOUT (tA oA))) τ2
    (selS_zero _ _ (fun _ => rfl)) (WExec.exec _ e2) m1 R2
  -- the second program, part b
  have k2 : ∀ s, s ≠ sSH → s ≠ sNW → s ≠ sAIN → s ≠ sAOUT → s ≠ sAT →
      τ2.st s = (σF (st8 w n h Q m pr ((P.lay Ua Dv Cv).fillW n h Q m pr) GF SF WF FF CF)
        ((P.lay Ua Dv Cv).fillW n h Q m pr)).st s := by
    intro s a1 a2 a3 a4 a5
    rw [t2o s a1 a2, q2st s a3 a4, t1o s a3 a5]
  have v2 : ∀ q : Fin CR, q ≠ rP1 → q ≠ RW1 7 → τ2.val q = τ1.val q := fun q a b => t2v q a b
  have hA3 : τ2.st sAOUT = ys.flatMap frame ++ false :: atomsStream atoms := by
    rw [t2o _ (by decide) (by decide)]; exact hO2
  have hT3 : τ2.st sAT = List.replicate atoms.length true := by
    rw [t2o _ (by decide) (by decide)]; exact hT2
  have hC3 : τ2.st sCF1 = frame (natWord wd' ++ cols.flatMap fun x => frame (SignedSortKey.binary wd' x)) := by
    rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    show CF = _; exact hCF
  have hPRE2 : τ2.st sPRE = [] := by rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  have hPOST2 : τ2.st sPOST = [] := by rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  obtain ⟨τ3, e3, t3pre, t3post, t3o, _, _, _, t3v, t3c⟩ := wm2b_spec (2 * (P.lay Ua Dv Cv).fillW n h Q m pr + 2)
    (rs τ2) (atoms.map List.length).sum Q m h (pr + 1) wd ys atoms (natWord cols.length ++ natWord (pr + 1))
    (natWord wd' ++ cols.flatMap fun x => frame (SignedSortKey.binary wd' x)) hys hat t2S rfl hA3 rfl hT3 rfl
    t2N rfl hC3 rfl
    (by show 0 = (τ2.st sPRE).length; rw [hPRE2]; rfl)
    (by show 0 = (τ2.st sPOST).length; rw [hPOST2]; rfl)
    (by show τ2.val rQ = Q; rw [v2 _ (by decide) (by decide), t1v, val1_rQ])
    (by show τ2.val rm = m; rw [v2 _ (by decide) (by decide), t1v, val1_rm])
    (by show τ2.val rh = h; rw [v2 _ (by decide) (by decide), t1v, val1_rh])
    t2P
    (by show τ2.val rw = wd; rw [v2 _ (by decide) (by decide), t1v, val1_rw])
    (by show τ2.val rK = 0; rw [v2 _ (by decide) (by decide)]; exact zK)
    (by show τ2.val rT = 0; rw [v2 _ (by decide) (by decide)]; exact zT)
    (by show _ ≤ 2 * (UnaryCalc.value Dv Cv n + 32 * (h + Q + m + pr)) + 2; omega)
  obtain ⟨m3, s6⟩ := (P.lay Ua Dv Cv).ph_run wm2b.toProg (2 * (P.lay Ua Dv Cv).fillW n h Q m pr + 2) _
    (wenc (2 * (P.lay Ua Dv Cv).fillW n h Q m pr + 2) (rs τ2)) τ3
    (selS_zero _ _ (fun _ => rfl)) (WExec.exec _ e3) m2 R2
  have k3 : ∀ s, s ≠ sPRE → s ≠ sPOST → s ≠ sSH → s ≠ sNW → s ≠ sAIN → s ≠ sAOUT → s ≠ sAT →
      τ3.st s = (σF (st8 w n h Q m pr ((P.lay Ua Dv Cv).fillW n h Q m pr) GF SF WF FF CF)
        ((P.lay Ua Dv Cv).fillW n h Q m pr)).st s := by
    intro s a1 a2 a3 a4 a5 a6 a7
    rw [t3o s a1 a2]
    exact k2 s a3 a4 a5 a6 a7
  refine ⟨τ3, m3, R2, Step.seq (Step.seq (Step.seq (Step.seq (Step.seq s1 s2) s3) s4)
    (Step.congr_in s5 rfl rfl)) (Step.congr_in s6 rfl rfl), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [t3pre]
    show (τ2.st sPRE) ++ _ = _
    rw [hPRE2]
    rfl
  · rw [t3post]
    show (τ2.st sPOST) ++ _ = _
    rw [hPOST2]
    rfl
  · rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  · rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  · rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  · rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  · rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl

end Wr5

end NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
