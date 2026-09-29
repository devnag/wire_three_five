import Proof.Wire_3_5.Primitive.SeedFix.C4CapC
import Proof.Wire_3_5.Primitive.SeedFix.C4CapF

/-! # C4 capacity v2, part 2: the SYM setup with the numbers machine at capacity `2^{⌊n/8⌋ + C}`

P3:2929-2941, 2994-3000, 3011-3016, 3098-3100: the twin of `C4Cap.front_run2`/`setup_run2` with the capacity
chain v2 (`capM2`, from the front's `1^n` on `gN1`, same region, output on `gUW`): the numbers machine (`midM`,
`mid_run2`) runs at `2·2^m + 2`, `m = capExp2 C n = ⌊n/8⌋ + C`.

* `frontM3`, `frontCost3`, **`front_run3`**; `setupM3`, `setupCost3`, **`setup_run3`**.

Paper quantities of the main type: the loop's entry words and the finisher's inputs on their tapes, with the
numbers at the capacity `2^{⌊n/8⌋ + C}`. -/

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

/-- **The front at capacity `2^m`, v2** (`m = ⌊n/8⌋ + C`): the raw request, `1^n`, two powers `C(n+1)^D`, the capacity
chain v2 read from `1^n`. -/
noncomputable def frontM3 (CL Cd C : ℕ) :=
  Composition.machine (RecoveryFocus.machine (slx 3 (by rw [Lay.N_eq]; omega) (ext0 L.gP0)) unM)
  (Composition.machine (RecoveryFocus.machine (slx 6 (by rw [Lay.N_eq]; omega) (ext0 L.gRAW)) crM)
  (Composition.machine (RecoveryFocus.machine (slx 18 (by have := L.U_eq; rw [Lay.N_eq]; omega) (ext0 L.gN1))
      (PCPSerializerCapacity.Power.machine L.D CL))
  (Composition.machine (RecoveryFocus.machine (slx L.oU2 (by have := L.U_eq; unfold Lay.oU2; rw [Lay.N_eq]; omega)
      (ext0 L.gN1)) (PCPSerializerCapacity.Power.machine L.D Cd))
    (RecoveryFocus.machine (slx (offC L) (by have := U_D L; unfold offC; rw [Lay.N_eq]; omega) (ext0 L.gN1))
      (capM2 C)))))

/-- The front's step bound. -/
def frontCost3 (w : List Bool) (n CL Cd C : ℕ) : ℕ :=
  2 * (2 * w.length + 1) + 2 + 1 + (crCost n + 1 + (PCPSerializerCapacity.Power.budget L.D CL n + 1 +
    (PCPSerializerCapacity.Power.budget L.D Cd n + 1 + capCost2 C n)))

/-- **The front's run at capacity `2^m`, v2**: as `front_run2`, with `gUW = 1^{2^{capExp2 C n}}`. -/
theorem front_run3 (hD : 16 ≤ L.D) (CL Cd C n : ℕ) (w sfx : List Bool) (hw : w = RepairRepresentation.natWord n ++ sfx)
    (B : Fin L.N → List Bool) (hP0 : B L.gP0 = frame w) (hbl : ∀ i : Fin L.N, 3 ≤ i.val → B i = []) :
    ∃ B' : Fin L.N → List Bool, Step (frontM3 L CL Cd C) (frontCost3 L w n CL Cd C) (fun _ => 0) B (fun _ => 0) B' ∧
      B' L.gP0 = frame w ∧ B' L.gN1 = List.replicate n true ∧
      B' L.gUL = List.replicate (UnaryCalc.value L.D CL n) true ∧
      B' L.gUD = List.replicate (UnaryCalc.value L.D Cd n) true ∧
      B' L.gUW = List.replicate (2 ^ capExp2 C n) true ∧
      (∀ i : Fin L.N, i.val < 3 → i ≠ L.gP0 → B' i = B i) ∧ (∀ i : Fin L.N, L.oDA ≤ i.val → B' i = []) := by
  have hU := L.U_pos
  have ho := L.out_lt
  have hUe := L.U_eq
  have hUD := U_D L
  have hoD := outD L
  have hoi : (UnaryCalc.outputTape L.D).val ≠ 0 := fun e => UnaryCalc.output_ne_input L.D (Fin.ext e)
  -- 1: the raw request
  obtain ⟨t1, h1, e10, e11⟩ := unS w
  obtain ⟨B1, s1, bl1, un1, pv1, ex1⟩ := stage0 h1 (by norm_num) 3 (by rw [Lay.N_eq]; omega) L.gP0 (by lv) B hP0 hbl
  have f1P0 : B1 L.gP0 = frame w := ex1.trans e10
  have f1R : B1 L.gRAW = w := (pv1 ⟨1, by norm_num⟩ L.gRAW (by norm_num) (by lv)).trans e11
  -- 2: `1^n`
  obtain ⟨t2, h2, e20, e28, e29⟩ := crS n sfx
  obtain ⟨B2, s2, bl2, un2, pv2, ex2⟩ := stage0 h2 (by norm_num) 6 (by rw [Lay.N_eq]; omega) L.gRAW (by lv) B1
    (by rw [f1R, hw]) bl1
  have f2P0 : B2 L.gP0 = frame w := (un2 _ (by lv) (by lv)).trans f1P0
  have f2N : B2 L.gN1 = List.replicate n true := (pv2 ⟨8, by norm_num⟩ L.gN1 (by norm_num) (by lv)).trans e28
  have f2R : B2 L.gRAW = RepairRepresentation.natWord n ++ sfx := ex2.trans (e20.trans rfl)
  -- 3: `C_L(n+1)^D`
  obtain ⟨t3, h3, e3i, e3o⟩ := UnaryCalc.poly_step L.D CL n
  obtain ⟨B3, s3, bl3, un3, pv3, ex3⟩ := stage0 h3 hU 18 (by have := L.U_eq; rw [Lay.N_eq]; omega) L.gN1 (by lv) B2 f2N bl2
  have f3P0 : B3 L.gP0 = frame w := (un3 _ (by lv) (by lv)).trans f2P0
  have f3N : B3 L.gN1 = List.replicate n true := ex3.trans e3i
  have f3R : B3 L.gRAW = RepairRepresentation.natWord n ++ sfx := (un3 _ (by lv) (by lv)).trans f2R
  have f3L : B3 L.gUL = List.replicate (UnaryCalc.value L.D CL n) true :=
    (pv3 (UnaryCalc.outputTape L.D) L.gUL hoi (by lv)).trans e3o
  -- 4: `C_d(n+1)^D`
  obtain ⟨t4, h4, e4i, e4o⟩ := UnaryCalc.poly_step L.D Cd n
  obtain ⟨B4, s4, bl4, un4, pv4, ex4⟩ := stage0 h4 hU L.oU2 (by have := L.U_eq; unfold Lay.oU2; rw [Lay.N_eq]; omega) L.gN1 (by lv) B3 f3N
    (fun i hi => bl3 i (by unfold Lay.oU2 at hi; omega))
  have f4P0 : B4 L.gP0 = frame w := (un4 _ (by lv) (by lv)).trans f3P0
  have f4N : B4 L.gN1 = List.replicate n true := ex4.trans e4i
  have f4R : B4 L.gRAW = RepairRepresentation.natWord n ++ sfx := (un4 _ (by lv) (by lv)).trans f3R
  have f4L : B4 L.gUL = List.replicate (UnaryCalc.value L.D CL n) true := (un4 _ (by lv) (by lv)).trans f3L
  have f4D : B4 L.gUD = List.replicate (UnaryCalc.value L.D Cd n) true :=
    (pv4 (UnaryCalc.outputTape L.D) L.gUD hoi (by lv)).trans e4o
  -- 5: the capacity chain v2
  obtain ⟨t5, h5, e50, e535⟩ := cap_run2 C n
  obtain ⟨B5, s5, bl5, un5, pv5, ex5⟩ := stage0 h5 (by norm_num) (offC L) (by unfold offC; rw [Lay.N_eq]; omega) L.gN1
    (by simp only [Lay.gN1, offC]; omega) B4 f4N
    (fun i hi => bl4 i (by unfold Lay.oU2; unfold offC at hi; omega))
  refine ⟨B5, s1.seq (s2.seq (s3.seq (s4.seq s5))), (un5 _ (by simp only [Lay.gP0, offC]; omega) (by lv)).trans f4P0,
    ex5.trans e50,
    (un5 _ (by simp only [Lay.gUL, offC]; omega) (by lv)).trans f4L,
    (un5 _ (by simp only [Lay.gUD, offC]; omega) (by lv)).trans f4D,
    (pv5 ⟨35, by norm_num⟩ L.gUW (by norm_num) (by simp only [Lay.gUW, offC]; omega)).trans e535, ?_, ?_⟩
  · intro i hi hne
    have n1 : i ≠ L.gRAW := fun e => by rw [e] at hi; revert hi; lv
    have n2 : i ≠ L.gN1 := fun e => by rw [e] at hi; revert hi; lv
    rw [un5 i (by unfold offC; omega) n2, un4 i (by unfold Lay.oU2; omega) n2, un3 i (by omega) n2, un2 i (by omega) n1,
      un1 i (by omega) hne]
  · intro i hi
    exact bl5 i (by unfold offC; unfold Lay.oDA at hi; omega)

end Front

section Setup
variable (L : Lay)

/-- **The SYM setup machine at capacity `2^m`, v2** (`m = ⌊n/8⌋ + Cc`). -/
noncomputable def setupM3 (CL Cd Cc : ℕ) (F : FreeProg) (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) :=
  Composition.machine (frontM3 L CL Cd Cc) (Composition.machine (L.midM F cr fe ζ Cδ C)
    (Composition.machine L.tailM (CloseoutWitness.SelectedErase.machine L.maskLP L.gRR L.gLG)))

/-- The setup's step bound. -/
def setupCost3 (w : List Bool) (n CL Cd Cc cD : ℕ) (u : List Bool) (c ell d2 ρ B3 : ℕ) : ℕ :=
  frontCost3 L w n CL Cd Cc + 1 + (Lay.midCost cD u (2 ^ capExp2 Cc n) c + 1 +
    (Lay.tailCost ell d2 ρ B3 + 1 + (2 * 2 ^ ρ + 4)))

/-- **The SYM setup's run at capacity `2^m`, v2** (`m = capExp2 Cc n = ⌊n/8⌋ + Cc`): `setup_run2`'s statement at
the new capacity; the exit bank verbatim. -/
theorem setup_run3 (hDL : 16 ≤ L.D) (CL Cd Cc : ℕ) (F : FreeProg) (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams)
    (n : ℕ) (w sfx v : List Bool) (hw : w = RepairRepresentation.natWord n ++ sfx) (cs : List ℕ) (cD : ℕ)
    (hd : ∃ (tout : Fin (Data.DS + 2 + Data.DR) → List Bool) (m : ℕ), Step Data.dataM cD (fun _ => 0)
      (Fin.addCases (Data.rawIn w n (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n))
        (fun _ : Fin 1 => List.replicate 0 false))
      (fun _ => 0) (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape Data.sOUT) = Data.dataWord cs ∧ tout (sTape Data.sIN) = frame w)
    (τ : WState (LNS 0) LNR) (c : ℕ)
    (hx : WExec (2 * 2 ^ capExp2 Cc n + 2) (bigW F cr fe ζ Cδ C)
      (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList cs)) τ c)
    (hτ0 : τ.st (sk 0 0) = frame w) (wd : Fin 39 → List Bool) (hτ : ∀ j, τ.st (sk 0 (symO j)) = wd j)
    (ell h Q' mm pr d2 ρ : ℕ) (hell : 1 ≤ ell)
    (h31 : wd 31 = List.replicate ell true) (h32 : wd 32 = List.replicate ell true)
    (h33 : wd 33 = List.replicate h true) (h34 : wd 34 = List.replicate Q' true)
    (h35 : wd 35 = List.replicate mm true) (h36 : wd 36 = List.replicate pr true)
    (h37 : wd 37 = NumsX.srcWord d2) (h38 : wd 38 = NumsX.srcWord ρ) (B3 : ℕ) (pre post : List Bool)
    (hc3 : C3ReqIface.C3Run L.S3.M B3 L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS w h Q' mm pr
      pre post) :
    ∃ B' : Fin L.N → List Bool,
      Step (setupM3 L CL Cd Cc F cr fe ζ Cδ C) (setupCost3 L w n CL Cd Cc cD (Data.unaryList cs) c ell d2 ρ B3)
        (fun _ => 0) (SeedFixTypes.stageIn L.X w v) (fun _ => 0) B' ∧
      B' L.gP0 = frame w ∧ B' L.gP1 = v ∧ B' L.gP2 = [] ∧ (∀ j, B' (L.gW j) = wd j) ∧
      B' L.gMA = frame (binary ell (GF.firstPrimitive ell)) ∧ B' L.gMB = frame (binary ell (GF.firstPrimitive ell)) ∧
      B' L.gUU = List.replicate (2 ^ d2) true ∧ B' L.gRR = List.replicate (2 ^ ρ) true ∧
      B' L.gPRE = frame pre ∧ B' L.gPOST = frame post ∧ B' L.gLG = List.replicate (2 ^ ρ + 1) false ∧
      (∀ i : Fin L.N, L.maskLP i = true → B' i = List.replicate (2 ^ ρ) false) ∧
      (∀ i : Fin L.N, L.oLP + L.T ≤ i.val → B' i = []) := by
  set B0 := SeedFixTypes.stageIn L.X w v with hB0
  have b0 : ∀ i : Fin L.N, 3 ≤ i.val → B0 i = [] := fun i hi => by
    rw [hB0]; unfold SeedFixTypes.stageIn; rw [ac_ge _ _ i hi]
  have b0P0 : B0 L.gP0 = frame w := by
    rw [hB0]; unfold SeedFixTypes.stageIn; rw [ac_lt _ _ L.gP0 (by lv)]; rfl
  have b0P1 : B0 L.gP1 = v := by
    rw [hB0]; unfold SeedFixTypes.stageIn; rw [ac_lt _ _ L.gP1 (by lv)]; rfl
  have b0P2 : B0 L.gP2 = [] := by
    rw [hB0]; unfold SeedFixTypes.stageIn; rw [ac_lt _ _ L.gP2 (by lv)]; rfl
  obtain ⟨B5, s5, f5P0, f5N, f5L, f5D, f5W, un5, bl5⟩ := front_run3 L hDL CL Cd Cc n w sfx hw B0 b0P0 b0
  obtain ⟨B8, s8, f8P0, f8W, un8, bl8⟩ :=
    mid_run2 L F cr fe ζ Cδ C n CL Cd (2 ^ capExp2 Cc n) w cs cD hd τ c hx hτ0 wd hτ B5 f5P0 f5N f5L f5D f5W bl5
  obtain ⟨B13, s13, f13P0, f13W, fMA, fMB, fUU, fRR, fPRE, fPOST, un13, bl13⟩ :=
    L.tail_run w wd ell h Q' mm pr d2 ρ hell h31 h32 h33 h34 h35 h36 h37 h38 B3 pre post hc3 B8 f8P0 f8W bl8
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
  have keep : ∀ i : Fin L.N, i.val < L.oLP → i ≠ L.gLG →
      CloseoutWitness.SelectedErase.output L.maskLP L.gLG (2 ^ ρ) B13 i = B13 i := fun i h1 h2 => by
    simp [CloseoutWitness.SelectedErase.output, L.maskLP_false i h1, h2]
  have gP1B : B13 L.gP1 = v := by
    rw [un13 _ (by lv) (by lv), un8 _ (by lv) (by lv), un5 _ (by lv) (by lv), b0P1]
  have gP2B : B13 L.gP2 = [] := by
    rw [un13 _ (by lv) (by lv), un8 _ (by lv) (by lv), un5 _ (by lv) (by lv), b0P2]
  have ho := L.S3.preS.isLt
  have ho2 := L.S3.postS.isLt
  refine ⟨_, s5.seq (s8.seq (s13.seq se)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [keep _ (by lv) (by lv), f13P0]
  · rw [keep _ (by lv) (by lv), gP1B]
  · rw [keep _ (by lv) (by lv), gP2B]
  · intro j
    have := Lay.symO_le j
    rw [keep _ (by lv) (by lv), f13W]
  · rw [keep _ (by lv) (by lv), fMA]
  · rw [keep _ (by lv) (by lv), fMB]
  · rw [keep _ (by lv) (by lv), fUU]
  · rw [keep _ (by lv) (by lv), fRR]
  · rw [keep _ (by lv) (by lv), fPRE]
  · rw [keep _ (by lv) (by lv), fPOST]
  · simp [CloseoutWitness.SelectedErase.output, hmL]
  · intro i hi
    simp [CloseoutWitness.SelectedErase.output, hi]
  · intro i hi
    have n1 : L.maskLP i = false := by
      unfold Lay.maskLP
      simp only [decide_eq_false_iff_not, not_and, not_lt]
      intro _
      exact hi
    have n2 : i ≠ L.gLG := fun e => by rw [e] at hi; revert hi; lv
    simp [CloseoutWitness.SelectedErase.output, n1, n2]
    exact bl13 i (by omega)

end Setup

end NearCubicWires.WireExponent3_5.PrimT.C4Cap
