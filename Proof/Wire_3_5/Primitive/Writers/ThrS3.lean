import Proof.Wire_3_5.Primitive.Writers.ThrSet4
import Proof.Wire_3_5.Primitive.SeedFix.C4CapG

/-! # c4 THR block, the THR setup at capacity v2

The twin of `setupT`/`setupT_run` with the front at capacity `2^{⌊n/8⌋ + C}` (`C4Cap.frontM3`, `front_run3`,
`capExp2`): the data stage, the hash bits' machine and the numbers machine run at `2·2^{capExp2 Cc n} + 2`.
* `setupT3`, `setupT3Cost`, **`setupT3_run`**.

Paper quantities of the main type: the loop's entry words and the finisher's inputs on their tapes (P3:3011-3016,
3098-3100), with the THR call's numbers and hash bits. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimAsm.BigBank
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

variable (L : Lay)

/-- **The THR setup machine** on the big bank. -/
noncomputable def setupT3 (CL Cd Cc x3 s3 : ℕ) (M3 : Machine (Data.DS + 2 + Data.DR + 1 + x3) s3) (P : WM (LNS 0) LNR) :=
  Composition.machine (RecoveryFocus.machine (liftE (hxb L x3)) (C4Cap.frontM3 L CL Cd Cc))
    (Composition.machine (RecoveryFocus.machine (slx (offD L) (hoffD L x3) (extD L (hxb L x3) x3)) M3)
      (Composition.machine (RecoveryFocus.machine (slx (offH L x3) (hoffH L x3) (extH L (hxb L x3)))
        (bigM ThrHB.hbXW)) (RecoveryFocus.machine (liftE (hxb L x3)) (restM L P))))

/-- Its step bound. -/
def setupT3Cost (w : List Bool) (n CL Cd Cc n3 W ch : ℕ) (u : List Bool) (c ell d2 ρ B3 : ℕ) : ℕ :=
  C4Cap.frontCost3 L w n CL Cd Cc + 1 + (n3 + 1 + (bigCost W ch + 1 +
    (cbCost u W c + 1 + (Lay.tailCost ell d2 ρ B3 + 1 + (2 * 2 ^ ρ + 4)))))

/-- **The THR setup's run** on the big bank. -/
theorem setupT3_run (hDL : 16 ≤ L.D) (CL Cd Cc n : ℕ) (w sfx v : List Bool)
    (hw : w = RepairRepresentation.natWord n ++ sfx)
    (x3 s3 n3 : ℕ) (M3 : Machine (Data.DS + 2 + Data.DR + 1 + x3) s3)
    (tout : Fin (Data.DS + 2 + Data.DR) → List Bool) (m : ℕ) (J : Fin x3 → List Bool)
    (h3 : Step M3 n3 (fun _ => 0)
      (Fin.addCases (m := Data.DS + 2 + Data.DR + 1) (n := x3) (motive := fun _ => List Bool)
        (Fin.addCases (Data.rawIn w n (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n))
          (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => []))
      (fun _ => 0)
      (Fin.addCases (m := Data.DS + 2 + Data.DR + 1) (n := x3) (motive := fun _ => List Bool)
        (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) J))
    (cs : List ℕ) (hO : tout (sTape Data.sOUT) = Data.dataWord cs) (hI : tout (sTape Data.sIN) = frame w)
    (τh : WState (LNS 0) LNR) (ch : ℕ)
    (hxe : WExec (2 * 2 ^ C4Cap.capExp2 Cc n + 2) ThrHB.hbXW (CellLoopD.blankCellD 0 w [] 0 []) τh ch)
    (hτh0 : τh.st (sk 0 0) = frame w) (hbF : List Bool) (hZ : τh.st ThrHB.sZ = marks hbF)
    (P : WM (LNS 0) LNR) (τ : WState (LNS 0) LNR) (c : ℕ)
    (hx : WExec (2 * 2 ^ C4Cap.capExp2 Cc n + 2) P (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList cs)) τ c)
    (hτ0 : τ.st (sk 0 0) = frame w) (wd : Fin 39 → List Bool) (hτ : ∀ j, τ.st (sk 0 (symO j)) = wd j)
    (ell h Q' mm pr d2 ρ : ℕ) (hell : 1 ≤ ell)
    (h31 : wd 31 = List.replicate ell true) (h32 : wd 32 = List.replicate ell true)
    (h33 : wd 33 = List.replicate h true) (h34 : wd 34 = List.replicate Q' true)
    (h35 : wd 35 = List.replicate mm true) (h36 : wd 36 = List.replicate pr true)
    (h37 : wd 37 = NumsX.srcWord d2) (h38 : wd 38 = NumsX.srcWord ρ) (B3 : ℕ) (pre post : List Bool)
    (hc3 : C3ReqIface.C3Run L.S3.M B3 L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS w h Q' mm pr
      pre post) :
    ∃ B' : Fin (3 + thrXb L x3) → List Bool,
      Step (setupT3 L CL Cd Cc x3 s3 M3 P)
        (setupT3Cost L w n CL Cd Cc n3 (2 ^ C4Cap.capExp2 Cc n) ch (Data.unaryList cs) c ell d2 ρ B3) (fun _ => 0)
        (SeedFixTypes.stageIn (thrXb L x3) w v) (fun _ => 0) B' ∧
      B' (liftE (hxb L x3) L.gP0) = frame w ∧ B' (liftE (hxb L x3) L.gP1) = v ∧
      B' (liftE (hxb L x3) L.gP2) = [] ∧ (∀ j, B' (liftE (hxb L x3) (L.gW j)) = wd j) ∧
      B' (liftE (hxb L x3) L.gMA) = frame (binary ell (GF.firstPrimitive ell)) ∧
      B' (liftE (hxb L x3) L.gMB) = frame (binary ell (GF.firstPrimitive ell)) ∧
      B' (liftE (hxb L x3) L.gUU) = List.replicate (2 ^ d2) true ∧
      B' (liftE (hxb L x3) L.gRR) = List.replicate (2 ^ ρ) true ∧
      B' (liftE (hxb L x3) L.gPRE) = frame pre ∧ B' (liftE (hxb L x3) L.gPOST) = frame post ∧
      B' (liftE (hxb L x3) L.gLG) = List.replicate (2 ^ ρ + 1) false ∧
      (∀ i : Fin L.N, L.maskLP i = true → B' (liftE (hxb L x3) i) = List.replicate (2 ^ ρ) false) ∧
      (∀ i : Fin L.N, L.oLP + L.T ≤ i.val → B' (liftE (hxb L x3) i) = []) ∧
      B' (hbT L x3) = marks hbF ∧ (∀ i : Fin (3 + thrXb L x3), offT L x3 ≤ i.val → B' i = []) := by
  have hxB := hxb L x3
  have hN : L.N = 3 + L.X := rfl
  have hU := L.U_pos
  have ho := L.out_lt
  have hUe := L.U_eq
  set W := 2 ^ C4Cap.capExp2 Cc n with hWd
  set B0 := SeedFixTypes.stageIn (thrXb L x3) w v with hB0d
  set B0L := SeedFixTypes.stageIn L.X w v with hB0Ld
  have hB0 : ∀ j : Fin L.N, B0 (liftE hxB j) = B0L j := by
    intro j
    rw [hB0d, hB0Ld]
    unfold SeedFixTypes.stageIn
    by_cases hj : j.val < 3
    · rw [ac_lt _ _ _ (by rw [liftE_val]; exact hj), ac_lt _ _ _ hj]; rfl
    · rw [ac_ge _ _ _ (by rw [liftE_val]; omega), ac_ge _ _ _ (by omega)]
  have hB0hi : ∀ i : Fin (3 + thrXb L x3), 3 + L.X ≤ i.val → B0 i = [] := by
    intro i hi; rw [hB0d]; unfold SeedFixTypes.stageIn; rw [ac_ge _ _ i (by omega)]
  have b0 : ∀ i : Fin L.N, 3 ≤ i.val → B0L i = [] := fun i hi => by
    rw [hB0Ld]; unfold SeedFixTypes.stageIn; rw [ac_ge _ _ i hi]
  have b0P0 : B0L L.gP0 = frame w := by
    rw [hB0Ld]; unfold SeedFixTypes.stageIn; rw [ac_lt _ _ L.gP0 (by lv)]; rfl
  have b0P1 : B0L L.gP1 = v := by
    rw [hB0Ld]; unfold SeedFixTypes.stageIn; rw [ac_lt _ _ L.gP1 (by lv)]; rfl
  have b0P2 : B0L L.gP2 = [] := by
    rw [hB0Ld]; unfold SeedFixTypes.stageIn; rw [ac_lt _ _ L.gP2 (by lv)]; rfl
  -- 1: the front
  obtain ⟨B5L, s5, f5P0, f5N, f5L, f5D, f5W, un5, bl5⟩ := C4Cap.front_run3 L hDL CL Cd Cc n w sfx hw B0L b0P0 b0
  obtain ⟨S5, i5, o5⟩ := liftStep s5 hxB B0 hB0
  -- 2: the data stage
  obtain ⟨B6, S6, g6P0, g6DO, un6, bl6L, bl6hi⟩ := data_dock L hxB x3 s3 n3 M3 w n (UnaryCalc.value L.D CL n)
    (UnaryCalc.value L.D Cd n) tout m J h3 cs hO hI (hoffD L x3) _ B5L i5 f5P0 f5N f5L f5D bl5
    (fun i hi => by rw [o5 i (by omega)]; exact hB0hi i hi)
  have g6 : ∀ i : Fin L.N, i.val < 3 → i ≠ L.gP0 → B6 (liftE hxB i) = B0L i := fun i hi hne => by
    rw [un6 i (by lv) hne (fun e => by rw [e] at hi; revert hi; lv) (fun e => by rw [e] at hi; revert hi; lv)
      (fun e => by rw [e] at hi; revert hi; lv), un5 i hi hne]
  have g6W : B6 (liftE hxB L.gUW) = List.replicate W true := by
    rw [un6 _ (by lv) (by lv) (by lv) (by lv) (by lv)]; exact f5W
  -- 3: the hash bits
  obtain ⟨B7, S7, g7hb, un7, bl7⟩ := hb_dock L hxB W w τh ch hxe hτh0 hbF hZ (offH L x3) (hoffH L x3)
    (by unfold offH; omega) B6 g6P0 g6W (fun i hi => bl6hi i (by unfold offH at hi; omega))
  have e76 : ∀ i : Fin L.N, B7 (liftE hxB i) = B6 (liftE hxB i) := fun i => by
    apply un7; rw [liftE_val]; unfold offH; have := i.isLt; omega
  set B7L : Fin L.N → List Bool := fun i => B7 (liftE hxB i) with hB7L
  -- 4: the copy-in and the numbers machine
  obtain ⟨B8L, s8, f8P0, f8W, un8, bl8⟩ := cb_run L P W w cs τ c hx hτ0 wd hτ B7L
    (by rw [hB7L]; simp only; rw [e76, g6P0]) (by rw [hB7L]; simp only; rw [e76, g6DO])
    (by rw [hB7L]; simp only; rw [e76, g6W]) (fun i hi => by rw [hB7L]; simp only; rw [e76]; exact bl6L i hi)
  -- 5: the tail
  obtain ⟨B13, s13, f13P0, f13W, fMA, fMB, fUU, fRR, fPRE, fPOST, un13, bl13⟩ :=
    L.tail_run w wd ell h Q' mm pr d2 ρ hell h31 h32 h33 h34 h35 h36 h37 h38 B3 pre post hc3 B8L f8P0 f8W bl8
  -- 6: the pads
  have hC3 : L.oC3 + L.S3.t ≤ L.oLP := by unfold Lay.oC3 Lay.oLP; omega
  have hmR : L.maskLP L.gRR = false := L.maskLP_false _ (by lv)
  have hmL : L.maskLP L.gLG = false := L.maskLP_false _ (by lv)
  have se := eraseS L.maskLP L.gRR L.gLG hmR hmL (by lv) (2 ^ ρ) B13
    (fun i hi => by
      unfold Lay.maskLP at hi
      simp only [decide_eq_true_eq] at hi
      rw [bl13 i (by omega)]
      simp)
    fRR (bl13 _ (by lv))
  obtain ⟨S8, i8, o8⟩ := liftStep (s8.seq (s13.seq se)) hxB B7 (fun j => rfl)
  have keep : ∀ i : Fin L.N, i.val < L.oLP → i ≠ L.gLG →
      CloseoutWitness.SelectedErase.output L.maskLP L.gLG (2 ^ ρ) B13 i = B13 i := fun i h1 h2 => by
    simp [CloseoutWitness.SelectedErase.output, L.maskLP_false i h1, h2]
  have gP1B : B13 L.gP1 = v := by
    rw [un13 _ (by lv) (by lv), un8 _ (by lv) (by lv), hB7L]; simp only; rw [e76, g6 _ (by lv) (by lv), b0P1]
  have gP2B : B13 L.gP2 = [] := by
    rw [un13 _ (by lv) (by lv), un8 _ (by lv) (by lv), hB7L]; simp only; rw [e76, g6 _ (by lv) (by lv), b0P2]
  have ho := L.S3.preS.isLt
  have ho2 := L.S3.postS.isLt
  refine ⟨_, S5.seq (S6.seq (S7.seq S8)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [i8, keep _ (by lv) (by lv), f13P0]
  · rw [i8, keep _ (by lv) (by lv), gP1B]
  · rw [i8, keep _ (by lv) (by lv), gP2B]
  · intro j
    have := Lay.symO_le j
    rw [i8, keep _ (by lv) (by lv), f13W]
  · rw [i8, keep _ (by lv) (by lv), fMA]
  · rw [i8, keep _ (by lv) (by lv), fMB]
  · rw [i8, keep _ (by lv) (by lv), fUU]
  · rw [i8, keep _ (by lv) (by lv), fRR]
  · rw [i8, keep _ (by lv) (by lv), fPRE]
  · rw [i8, keep _ (by lv) (by lv), fPOST]
  · rw [i8]; simp [CloseoutWitness.SelectedErase.output, hmL]
  · intro i hi
    rw [i8]; simp [CloseoutWitness.SelectedErase.output, hi]
  · intro i hi
    have n1 : L.maskLP i = false := by
      unfold Lay.maskLP
      simp only [decide_eq_false_iff_not, not_and, not_lt]
      intro _
      exact hi
    have n2 : i ≠ L.gLG := fun e => by rw [e] at hi; revert hi; lv
    rw [i8]
    simp [CloseoutWitness.SelectedErase.output, n1, n2]
    exact bl13 i (by omega)
  · rw [o8 _ (by unfold hbT offH; simp; omega)]; exact g7hb
  · intro i hi
    rw [o8 _ (by unfold offT offH at hi; omega)]
    exact bl7 i (by unfold offT at hi; exact hi)

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
