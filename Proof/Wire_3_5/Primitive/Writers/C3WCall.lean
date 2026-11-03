import Lean
import Proof.Wire_3_5.Primitive.Writers.C3WFieldsB
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.GeoIface2
import Proof.Wire_3_5.Primitive.SeedFix.GeoPack
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.C3WCallBase


noncomputable section
set_option maxRecDepth 4096


/-! # C3 request writer, part 16: the run at a call

Paper quantities: the fields `preW`, `postW` of the call's request (P3:1886-1906, 1636-1664). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Field
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.PrimAsm.C3Asm NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
open NearCubicWires.RepairOrdinary (frame)
open NearCubicWires.RepairRepresentation (natWord)

section Call
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
variable (l : Literals) (F : GateFree l) (EG : Envelope) (cG kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The five writers of a call family: the given gate-field writer, the geometry writers, the flips machine. -/
noncomputable def wr5 (Gs : WriterIface.WriterStage) (sA : PrimT.GeoIface2.SideWriterAt l F EG cG kclk coef A a ha)
    (wA : PrimT.GeoIface2.WidthWriterAt l F EG cG kclk coef A a ha)
    (cA : PrimT.GeoIface2.ColsWriterAt l F EG cG kclk coef A a ha) : Wr5 :=
  ⟨Gs, sA.toWriterStage, wA.toWriterStage, flipsStage (gate0 l F).row.cr, cA.toWriterStage⟩

/-- **The C3 request writer at a call**: from the call's request word and the numbers, `frame (preW …)` and
`frame (postW …)` of the call's request at its pool `gates`. -/
theorem call_run (Gs : WriterIface.WriterStage) (sA : PrimT.GeoIface2.SideWriterAt l F EG cG kclk coef A a ha)
    (wA : PrimT.GeoIface2.WidthWriterAt l F EG cG kclk coef A a ha)
    (cA : PrimT.GeoIface2.ColsWriterAt l F EG cG kclk coef A a ha) (Dv Cv : ℕ) (req : PrimRequest)
    (hcall : (callInputs l F kclk coef A a ha).Call req) (hs : (callInputs l F kclk coef A a ha).StarAt req.n)
    (gates : List (NormalizedThresholdGate ((callInputs l F kclk coef A a ha).starParams req.n hs).n)) (BG : ℕ)
    (hG : WriterIfaceJ.WriterRun Gs.M BG Gs.inS Gs.outS req.word (PrimT.C4Geo.gateField gates))
    (h Q m pr : ℕ) (hh : 1 ≤ h)
    (hfit : CoefFit (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs)
      (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0))
    (hpoly : PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs) +
      (gates.map PrimT.C4Geo.suppG).length + 4 * PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs) +
      2 + (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams req.n hs)).length + 1 +
      2 ^ (natBitLength (gates.map PrimT.C4Geo.suppG).length + 1) +
      2 ^ (natBitLength (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) + 1) +
      21 * (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams req.n hs)).length + 61 ≤
        BlockPlatform.UnaryCalc.value Dv Cv req.n)
    (Bud : ℕ)
    (hB : 2 * callCost (wr5 l F EG cG kclk coef A a ha Gs sA wA cA) Dv Cv (gate0 l F).alg
      ((callInputs l F kclk coef A a ha).starParams req.n hs)
      (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates req.word
      h Q m pr BG (cG * classBound EG .preprocessing req.n (((gate0 l F).budget kclk coef A a ha).kOf req.n)
        (((gate0 l F).budget kclk coef A a ha).psiOf req.n))
      (2 * (GeoFront.frontCost req.word req.n PrimT.FlipsPack.flD (PrimT.FlipsPack.flCv (gate0 l F).row.cr) +
        PrimT.Flips.flipsCost req ((callInputs l F kclk coef A a ha).starParams req.n hs) (gate0 l F).row.cr) + 2) +
      2 ≤ Bud) :
    PrimT.C3ReqIface.C3Run ((wr5 l F EG cG kclk coef A a ha Gs sA wA cA).c3M Dv Cv (C3a.Lay.c3aM (gate0 l F).alg)
        (c3aIn (gate0 l F).alg) (C3a.Word.c3aOut (gate0 l F).alg)) Bud
      ((wr5 l F EG cG kclk coef A a ha Gs sA wA cA).port Dv Cv (Ua := C3a.Lay.U (gate0 l F).alg) C3Phase.cIN)
      ((wr5 l F EG cG kclk coef A a ha Gs sA wA cA).port Dv Cv (Ua := C3a.Lay.U (gate0 l F).alg) C3Phase.sH)
      ((wr5 l F EG cG kclk coef A a ha Gs sA wA cA).port Dv Cv (Ua := C3a.Lay.U (gate0 l F).alg) C3Phase.sQ)
      ((wr5 l F EG cG kclk coef A a ha Gs sA wA cA).port Dv Cv (Ua := C3a.Lay.U (gate0 l F).alg) C3Phase.sM)
      ((wr5 l F EG cG kclk coef A a ha Gs sA wA cA).port Dv Cv (Ua := C3a.Lay.U (gate0 l F).alg) C3Phase.sP)
      ((wr5 l F EG cG kclk coef A a ha Gs sA wA cA).port Dv Cv (Ua := C3a.Lay.U (gate0 l F).alg) C3Phase.sPRE)
      ((wr5 l F EG cG kclk coef A a ha Gs sA wA cA).port Dv Cv (Ua := C3a.Lay.U (gate0 l F).alg) C3Phase.sPOST)
      req.word h Q m pr
      (PrimT.C3ReqIface.preW (gate0 l F).alg (PrimT.C3ReqIface.r0 ((callInputs l F kclk coef A a ha).starParams req.n hs)
        (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0 m 0 pr 0))
      (PrimT.C3ReqIface.postW (gate0 l F).alg (PrimT.C3ReqIface.r0 ((callInputs l F kclk coef A a ha).starParams req.n hs)
        (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0 m 0 pr 0)) := by
  obtain ⟨sfx, hw⟩ := PrimT.GeoPack.call_word req
  have hn1 := PrimT.GeoPack.star_n_pos hs
  obtain ⟨hW, hcap⟩ := PrimT.FlipsPack.fill_ok (gate0 l F).row.cr req.n req.word.length
    (PrimAsm.CallSize.gate_word_length_le l F kclk coef A a ha req hcall)
  have rF := PrimT.Flips.flips_run (gate0 l F).row.cr PrimT.FlipsPack.flD (PrimT.FlipsPack.flCv (gate0 l F).row.cr)
    ((callInputs l F kclk coef A a ha).starParams req.n hs) (PrimT.GeoPack.starParams_r l F kclk coef A a ha req.n hs)
    req rfl hcall.2.2.2.2.1.1 hcall.2.2.2.2.1.2 hW hcap _ le_rfl
  obtain ⟨A3, hA3, hA3o⟩ := C3a.Word.c3a_run (gate0 l F).alg
    (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs)
      (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0)
    (poolReq_pre _ _ gates h Q 0) hfit hn1 hh
  have hseg : ExtDecompositionBatch.segment (gates.map PrimT.C4Geo.suppG) (List.replicate req.n true) =
      natWord (gates.map PrimT.C4Geo.suppG).length ++ gyrOf gates := by
    unfold ExtDecompositionBatch.segment gyrOf; rw [List.append_assoc]; rfl
  have hA : Step (C3a.Lay.c3aM (gate0 l F).alg) (C3a.Lay.c3aCost (gate0 l F).alg
      (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs)
        (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0))
      (fun _ => 0) (fun j => if j = c3aIn (gate0 l F).alg then frame (Top.loadRec (List.replicate req.n true)
        (frame (natWord (gates.map PrimT.C4Geo.suppG).length ++ gyrOf gates))
        (frame (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams req.n hs)))
        (List.replicate (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) true)
        ((PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs)
          (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation)).flatMap frame
          ++ [false]) (List.replicate h true) (List.replicate Q true) [] [] [] []) else []) (fun _ => 0) A3 := by
    refine Step.congr_in hA3 rfl ?_
    funext j
    have e : (j.val = 0) = (j = c3aIn (gate0 l F).alg) := propext ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩
    simp only [e]
    congr 2
    unfold C3a.c3aInput C3a.c3aTop
    rw [← hseg]
    rfl
  have ex := (wr5 l F EG cG kclk coef A a ha Gs sA wA cA).c3_run Dv Cv (C3a.Lay.c3aM (gate0 l F).alg)
    (c3aIn (gate0 l F).alg) (C3a.Word.c3aOut (gate0 l F).alg) req.word sfx req.n h Q m pr hw
    _ _ _ _ _ _ _ _ _ _ hG (sA.ready req hcall hs) (wA.ready req hcall hs) rF (cA.ready req hcall hs)
    (gates.map PrimT.C4Geo.suppG).length (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs))
    (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) (gyrOf gates)
    (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams req.n hs))
    (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs)
      (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation))
    (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams req.n hs))
    (gateField_eq gates) rfl rfl
    (by
      intro f hf e
      have h1 := (poolReq_pre _ _ gates h Q 0).2.1 f hf
      have h0 : (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams req.n hs)
          (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation) gates h Q 0).n =
          req.n := rfl
      rw [e, List.length_nil, h0] at h1
      omega)
    rfl rfl (c3aIn_ne (gate0 l F).alg) _ A3 hA
    (poolRecs (gate0 l F).alg h (gates.map PrimT.C4Geo.suppG)
      (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams req.n hs))
      (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs))
      (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs)
        (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation)))
    (childTable Q (shapeOf (densePool (gate0 l F).alg (gates.map PrimT.C4Geo.suppG)
      (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams req.n hs))
      (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs))
      (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams req.n hs)
        (((callInputs l F kclk coef A a ha).starParams req.n hs).translationOfCodes req.translation)))))
    (poolRecs_ne _ h hh _ _ _ _) (childTable_ne _ _) (by rw [hA3o]; rfl)
    (C3a.PO.childTable_length _ Q _ _ _ _) hpoly Bud hB
  rw [preW_eq, postW_eq]
  exact ex

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.C3Field

end
