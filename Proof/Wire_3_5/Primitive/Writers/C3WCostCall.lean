import Proof.Wire_3_5.Primitive.Writers.C3WSizes

/-! # C3 request writer, part 20: the call's steps in one size `S`

`Gm a Dv S`: the writer's steps at a call whose base sizes (the request word, `n`, the four numbers, the writers'
budgets, the fill polynomial) are at most `S` (**`call_cost_le`**), polynomially bounded in `S` (`pb_Gm`).

Paper quantity: the request writer's steps within the preprocessing class (P3:3108). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch NearCubicWires.LocalBitMultitape
open NearCubicWires.PolynomialSchedule NearCubicWires.SourceInterfaces NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.DecBound
open NearCubicWires.WireExponent3_5.PrimAsm.C3Asm NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
open NearCubicWires.WireExponent3_5.PrimAsm.C3Field
open NearCubicWires.RepairOrdinary (frame frame_length)
open NearCubicWires.RepairRepresentation (natWord)

/-- C3a′'s steps as a polynomial in the size `S`. -/
def PnA (a : RepairRepresentation.DecompositionAlgorithm) (S : ℕ) : ℕ :=
  10246 * ((20 * S + 12) * (20 * S + 12) * ((SourceEnvelope.coefficient a + 1) * (S + 2) ^ (2 * degD a + 2) + 1)) ^ 4 +
    Kd a * (S + 2) ^ (2 * degD a + 3)

/-- **The call's steps as a polynomial in the size `S`.** -/
noncomputable def Gm (a : RepairRepresentation.DecompositionAlgorithm) (Dv S : ℕ) : ℕ :=
  2 * (cR Dv * (S + PnA a S + 1) ^ dR Dv) + 2

theorem pb_Gm (a : RepairRepresentation.DecompositionAlgorithm) (Dv : ℕ) : PolynomiallyBounded (fun S => Gm a Dv S) := by
  simp only [Gm, PnA]
  iterate 60 (all_goals (try (first
    | with_reducible exact polynomiallyBounded_id
    | with_reducible exact polynomiallyBounded_constant _
    | with_reducible apply polynomiallyBounded_add
    | with_reducible apply polynomiallyBounded_mul
    | with_reducible apply polynomiallyBounded_pow)))

noncomputable def cGm (a : RepairRepresentation.DecompositionAlgorithm) (Dv : ℕ) : ℕ :=
  Classical.choose (pb_Gm a Dv)
noncomputable def dGm (a : RepairRepresentation.DecompositionAlgorithm) (Dv : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (pb_Gm a Dv))

theorem Gm_le (a : RepairRepresentation.DecompositionAlgorithm) (Dv S : ℕ) : Gm a Dv S ≤ cGm a Dv * (S + 1) ^ dGm a Dv :=
  (Classical.choose_spec (Classical.choose_spec (pb_Gm a Dv))).2 S

section Call
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
variable (l : Literals) (F : GateFree l) (EG : Envelope) (cG kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The call's steps within `Gm`** at any size `S0` above the request word, `n`, the numbers, the writers'
budgets and the fill polynomial. -/
theorem call_cost_le (Gs : WriterIface.WriterStage) (sA : PrimT.GeoIface2.SideWriterAt l F EG cG kclk coef A a ha)
    (wA : PrimT.GeoIface2.WidthWriterAt l F EG cG kclk coef A a ha)
    (cA : PrimT.GeoIface2.ColsWriterAt l F EG cG kclk coef A a ha) (Dv Cv : ℕ) (req : PrimRequest)
    (hcall : (callInputs l F kclk coef A a ha).Call req) (hs : (callInputs l F kclk coef A a ha).StarAt req.n)
    (gates : List (NormalizedThresholdGate ((callInputs l F kclk coef A a ha).starParams req.n hs).n)) (BG : ℕ)
    (hG : WriterIfaceJ.WriterRun Gs.M BG Gs.inS Gs.outS req.word (PrimT.C4Geo.gateField gates))
    (h Q m pr : ℕ) (hh : 1 ≤ h)
    (hfit : CoefFit (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs)
      (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0))
    (S0 : ℕ) (hw : req.word.length ≤ S0) (hn : req.n ≤ S0) (hhQ : h + Q + m + pr ≤ S0) (hBG : BG ≤ S0)
    (hBS : cG * classBound EG .preprocessing req.n (((gate0 l F).budget kclk coef A a ha).kOf req.n)
      (((gate0 l F).budget kclk coef A a ha).psiOf req.n) ≤ S0)
    (hBF : 2 * (GeoFront.frontCost req.word req.n PrimT.FlipsPack.flD (PrimT.FlipsPack.flCv (gate0 l F).row.cr) +
        PrimT.Flips.flipsCost req ((callInputs l F kclk coef A a ha).starParams req.n hs) (gate0 l F).row.cr) + 2 ≤ S0)
    (hV : UnaryCalc.value Dv Cv req.n ≤ S0) (hCv : Cv ≤ S0) :
    2 * callCost (wr5 l F EG cG kclk coef A a ha Gs sA wA cA) Dv Cv (gate0 l F).alg
      ((callInputs l F kclk coef A a ha).starParams req.n hs)
      (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates req.word
      h Q m pr BG (cG * classBound EG .preprocessing req.n (((gate0 l F).budget kclk coef A a ha).kOf req.n)
        (((gate0 l F).budget kclk coef A a ha).psiOf req.n))
      (2 * (GeoFront.frontCost req.word req.n PrimT.FlipsPack.flD (PrimT.FlipsPack.flCv (gate0 l F).row.cr) +
        PrimT.Flips.flipsCost req ((callInputs l F kclk coef A a ha).starParams req.n hs) (gate0 l F).row.cr) + 2) + 2 ≤
      Gm (gate0 l F).alg Dv S0 := by
  have hn1 := PrimT.GeoPack.star_n_pos hs
  -- the writers' outputs
  have oG := wr_out_le Gs.hio hG
  have oS := wr_out_le sA.hio (sA.ready req hcall hs)
  have oW := wr_out_le wA.hio (wA.ready req hcall hs)
  have oC := wr_out_le cA.hio (cA.ready req hcall hs)
  obtain ⟨hW, hcap⟩ := PrimT.FlipsPack.fill_ok (gate0 l F).row.cr req.n req.word.length
    (PrimAsm.CallSize.gate_word_length_le l F kclk coef A a ha req hcall)
  have oF := wr_out_le (GeoFront.gInP_ne_out PrimT.FlipsPack.flD) (PrimT.Flips.flips_run (gate0 l F).row.cr
    PrimT.FlipsPack.flD (PrimT.FlipsPack.flCv (gate0 l F).row.cr) ((callInputs l F kclk coef A a ha).starParams req.n hs) (PrimT.GeoPack.starParams_r l F kclk coef A a ha req.n hs)
    req rfl hcall.2.2.2.2.1.1 hcall.2.2.2.2.1.2 hW hcap _ le_rfl)
  rw [gateField_eq, frame_length, List.length_append] at oG
  rw [PrimT.C4Geo.sideField, frame_length] at oS
  rw [List.length_replicate] at oW
  simp only [PrimT.C4Geo.colsField, RepairOrdinary.MatrixScorePhi.columnsWord, frame_length, List.length_append] at oC
  simp only [PrimT.C4Geo.flipsField, CompilerMachine.Kit.streamTape, List.length_append, List.length_cons,
    List.length_nil] at oF
  have ePn : ((callInputs l F kclk coef A a ha).starParams req.n hs).n = req.n := rfl
  rw [ePn] at oF
  have hgy := flatMap_frame_len' (gates.map PrimT.C4Geo.suppG) RepairOrdinary.CloseoutRowsCircuitBottom.nativeWord
  have hgyr : (gates.map PrimT.C4Geo.suppG).length ≤ (gyrOf gates).length := by
    unfold gyrOf; rw [List.length_append]; omega
  have hcl := flatMap_frame_len' (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams req.n hs)) fun x => RepairOrdinary.SignedSortKey.binary (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) x
  have hfl := flatMap_frame_len (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation))
  -- C3a′
  obtain ⟨A3, hA3, hA3o⟩ := C3a.Word.c3a_run (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0) (poolReq_pre _ _ gates h Q 0) hfit hn1 hh
  have oA0 := step_out_le hA3 (C3a.Word.c3aOut (gate0 l F).alg) rfl (by simp [C3a.Word.c3aOut])
  rw [hA3o] at oA0
  have oA : ((poolRecs (gate0 l F).alg h (gates.map PrimT.C4Geo.suppG) (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams req.n hs))
      (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation))).flatMap frame).length +
      ((atomsStream (childTable Q (shapeOf (densePool (gate0 l F).alg (gates.map PrimT.C4Geo.suppG)
      (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams req.n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation)))))).length + 1) ≤
      C3a.Lay.c3aCost (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0) := by
    have := oA0
    rw [List.length_append, List.length_cons] at this
    exact this
  have ey10 : (natWord (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) ++ (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams req.n hs)).flatMap
      fun x => frame (RepairOrdinary.SignedSortKey.binary (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) x)).length =
      (natWord (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs))).length + ((PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams req.n hs)).flatMap
      fun x => frame (RepairOrdinary.SignedSortKey.binary (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) x)).length := List.length_append
  have egyl : (natWord (gates.map PrimT.C4Geo.suppG).length ++ gyrOf gates).length =
      (natWord (gates.map PrimT.C4Geo.suppG).length).length + (gyrOf gates).length := List.length_append
  have hsum := sum_len_le (childTable Q (shapeOf (densePool (gate0 l F).alg (gates.map PrimT.C4Geo.suppG)
      (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams req.n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation)))))
  have eatoms : (atomsStream (childTable Q (shapeOf (densePool (gate0 l F).alg (gates.map PrimT.C4Geo.suppG)
      (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams req.n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation)))))).length =
      ((childTable Q (shapeOf (densePool (gate0 l F).alg (gates.map PrimT.C4Geo.suppG)
      (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams req.n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation))))).flatMap atomStream).length := rfl
  -- C3a′'s steps
  have hseg : (C3a.Lay.segR (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0)).length ≤ S0 := by
    show (ExtDecompositionBatch.segment (gates.map PrimT.C4Geo.suppG) (List.replicate req.n true)).length ≤ S0
    have e : ExtDecompositionBatch.segment (gates.map PrimT.C4Geo.suppG) (List.replicate req.n true) =
        natWord (gates.map PrimT.C4Geo.suppG).length ++ gyrOf gates := by
      unfold ExtDecompositionBatch.segment gyrOf; rw [List.append_assoc]; rfl
    rw [e, List.length_append]; omega
  have hseg2 : ExtDecompositionBatch.segment (gates.map PrimT.C4Geo.suppG) (List.replicate req.n true) =
      natWord (gates.map PrimT.C4Geo.suppG).length ++ gyrOf gates := by
    unfold ExtDecompositionBatch.segment gyrOf; rw [List.append_assoc]; rfl
  have hin : (C3a.c3aInput (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0)).length ≤ 20 * S0 + 12 := by
    have e : C3a.c3aInput (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0) = Top.loadRec (List.replicate req.n true)
        (frame (natWord (gates.map PrimT.C4Geo.suppG).length ++ gyrOf gates)) (frame (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams req.n hs)))
        (List.replicate (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) true) ((PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation)).flatMap frame ++ [false])
        (List.replicate h true) (List.replicate Q true) [] [] [] [] := by
      unfold C3a.c3aInput C3a.c3aTop
      rw [← hseg2]
      rfl
    rw [e, loadRec_len]
    simp only [List.length_replicate, frame_length, List.length_nil, List.length_append, List.length_cons]
    omega
  have hnA : C3a.Lay.c3aCost (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0) ≤ PnA (gate0 l F).alg S0 := by
    have c := c3a_cost_le2 (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0) (poolReq_pre _ _ gates h Q 0) (20 * S0 + 12) hin
      (by have e : (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0).n = req.n := rfl
          omega)
      (by have e : (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0).width = PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs) := rfl
          omega)
      (by have e : (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0).h = h := rfl
          omega)
      (by have e : (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0).Q = Q := rfl
          omega)
      (by have e : (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0).gates.length = (gates.map PrimT.C4Geo.suppG).length := rfl
          have e2 : (natWord (gates.map PrimT.C4Geo.suppG).length ++ gyrOf gates).length = _ := List.length_append
          omega)
      (by have e : (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0).flips.length = (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation)).length := rfl
          omega) (by omega)
    refine le_trans c ?_
    unfold PnA
    gcongr
  -- the run's steps
  have hZ := runCost_le (wr5 l F EG cG kclk coef A a ha Gs sA wA cA) Dv Cv (Ua := C3a.Lay.U (gate0 l F).alg) req.word
    req.n h Q m pr BG (cG * classBound EG .preprocessing req.n (((gate0 l F).budget kclk coef A a ha).kOf req.n)
      (((gate0 l F).budget kclk coef A a ha).psiOf req.n))
    (cG * classBound EG .preprocessing req.n (((gate0 l F).budget kclk coef A a ha).kOf req.n)
      (((gate0 l F).budget kclk coef A a ha).psiOf req.n))
    (2 * (GeoFront.frontCost req.word req.n PrimT.FlipsPack.flD (PrimT.FlipsPack.flCv (gate0 l F).row.cr) +
        PrimT.Flips.flipsCost req ((callInputs l F kclk coef A a ha).starParams req.n hs) (gate0 l F).row.cr) + 2)
    (cG * classBound EG .preprocessing req.n (((gate0 l F).budget kclk coef A a ha).kOf req.n)
      (((gate0 l F).budget kclk coef A a ha).psiOf req.n))
    (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) (gates.map PrimT.C4Geo.suppG).length (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams req.n hs)).length
    ((PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation)).flatMap frame).length (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation)).length
    (natWord (gates.map PrimT.C4Geo.suppG).length ++ gyrOf gates).length (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams req.n hs)).length
    (C3a.Lay.c3aCost (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0))
    ((poolRecs (gate0 l F).alg h (gates.map PrimT.C4Geo.suppG) (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams req.n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs))
      (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation))).flatMap frame).length
    (atomsStream (childTable Q (shapeOf (densePool (gate0 l F).alg (gates.map PrimT.C4Geo.suppG)
      (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams req.n hs)) (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation)))))).length
    ((childTable Q (shapeOf (densePool (gate0 l F).alg (gates.map PrimT.C4Geo.suppG) (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams req.n hs))
      (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation))))).map List.length).sum
    (natWord (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) ++ (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams req.n hs)).flatMap
      fun x => frame (RepairOrdinary.SignedSortKey.binary (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) x)).length
    (S0 + C3a.Lay.c3aCost (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hR' := Rm_le Dv (S0 + C3a.Lay.c3aCost (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0))
  have hpow : (S0 + C3a.Lay.c3aCost (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs) (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0) + 1) ^ dR Dv ≤ (S0 + PnA (gate0 l F).alg S0 + 1) ^ dR Dv :=
    Nat.pow_le_pow_left (by omega) _
  have hmul := Nat.mul_le_mul_left (cR Dv) hpow
  have fin := le_trans hZ (le_trans hR' hmul)
  unfold Gm callCost
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 fin) 2

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
