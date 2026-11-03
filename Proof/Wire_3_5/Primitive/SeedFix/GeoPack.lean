import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymBBase
import Proof.Wire_3_5.Primitive.Writers.GeoColsRun
import Proof.Wire_3_5.Primitive.Writers.GeoSide
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.GeoIface2
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.GeoPackBase


noncomputable section
set_option maxRecDepth 4096


/-! # The geometry writers packaged at every call: columns, halves, width

P3:1212-1216 (star:partition: "Assign `r/2` whole blocks to each side [...] A fixed linear basis of each code gives
polynomial-time encoding") and P3:3105-3115 (`prim:runtime`: the preprocessing is polynomial): the register-language
writers on the request word (`GeoColsRun.cols_run`, `GeoSide.side_run`, `GeoSide.width_run`, each a
`WriterRun (geoM prog Dv Cv) Bud …` under the fill hypotheses and an explicit step bound) become T's
`GeoIface2` writers at every call of the family:

* the fill count `W = (c_r + 25)·(n+1)^2` (`geoW_ok`);
* `numsN`, `nums_le` (the numbers' cost by a polynomial in `n` and `c_r`); `geoCostN`, `geo_cost_le` (every
  writer's steps); `geoRest_mono`, `pb_geoRest`, **`geoCost_poly`**: `geoCostN c_r n ≤ geoC c_r·(n+1)^geoD` with the
  degree `geoD` independent of `c_r` (`(n + c_r + 1) ≤ (c_r+1)(n+1)`);
* **`colsAt`**, **`sideAt`**, **`widthAt`**: `GeoIface2.{Cols,Side,Width}WriterAt l F E_G c_G kclk coef A a ha` under
  `geoD ≤ E_G.Apre` and `geoC c_r·2^geoD ≤ c_G` (`c_r` the gate's row constant).

Paper quantities of the main types: the columns of `φ` (C3's column header), the halves, the dense width. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.GeoPack
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline
open NearCubicWires.PolynomialSchedule NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (geoM gInP gOutP gInP_ne_out frontCost)
open NearCubicWires.WireExponent3_5.PrimT.C4GateSym (mkStage stage_run pre_class_le)

/-! ## The fill count -/

/-! ## The steps -/

/-! ## The writers at every call -/

section Pack
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
variable (l : Literals) (F : GateFree l) (EG : Envelope) (cG kclk coef A a ha) (ha : a ≤ kclk + 1)

/-- The call's star multiplier is the ledger's `rowBr c_r n` (the gate's row constant). -/
theorem starParams_r (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ((callInputs l F kclk coef A a ha).starParams n hs).r = Ledger.rowBr (gate0 l F).row.cr
      ((callInputs l F kclk coef A a ha).starParams n hs).n := rfl

/-- The machines' bound at a call, into the preprocessing class. -/
theorem geo_budget (hA : geoD ≤ EG.Apre) (hc : geoC (gate0 l F).row.cr * 2 ^ geoD ≤ cG) (req : PrimRequest)
    (hcall : (callInputs l F kclk coef A a ha).Call req) (hs : (callInputs l F kclk coef A a ha).StarAt req.n)
    (c : ℕ) (hcb : c ≤ 40 * req.n + 21 + 2000 * (req.n + 2) ^ 4 + 200 * (req.n + 3) + 1) :
    2 * (frontCost req.word req.n 2 (geoCv (gate0 l F).row.cr) +
      (PrimAsm.GeoNums.numsGCostE ((callInputs l F kclk coef A a ha).starParams req.n hs) (gate0 l F).row.cr + c)) +
      2 ≤ cG * classBound EG .preprocessing req.n (((gate0 l F).budget kclk coef A a ha).kOf req.n)
        (((gate0 l F).budget kclk coef A a ha).psiOf req.n) := by
  have c1 := geo_cost_le (gate0 l F).row.cr ((callInputs l F kclk coef A a ha).starParams req.n hs) req.word
    (PrimAsm.CallSize.gate_word_length_le l F kclk coef A a ha req hcall) c hcb
  have c2 := geoCost_poly (gate0 l F).row.cr req.n
  have c3 := pre_class_le EG (geoC (gate0 l F).row.cr) geoD cG req.n
    (((gate0 l F).budget kclk coef A a ha).kOf req.n) (((gate0 l F).budget kclk coef A a ha).psiOf req.n)
    (star_n_pos hs) hA hc
  exact le_trans c1 (le_trans c2 c3)

/-- **The columns writer** at every call (`GeoIface2.ColsWriterAt`). -/
noncomputable def colsAt (hA : geoD ≤ EG.Apre) (hc : geoC (gate0 l F).row.cr * 2 ^ geoD ≤ cG) :
    GeoIface2.ColsWriterAt l F EG cG kclk coef A a ha :=
  ⟨mkStage (geoM (PrimAsm.GeoColsRun.colsW (gate0 l F).row.cr) 2 (geoCv (gate0 l F).row.cr)) (gInP 2) (gOutP 2)
    (gInP_ne_out 2), fun req hcall hs => by
    refine stage_run _ _ _ _ _ _ _ ?_
    obtain ⟨sfx, hw⟩ := call_word req
    obtain ⟨hW, hW2⟩ := geoW_ok (gate0 l F).row.cr req.n
    refine PrimAsm.GeoColsRun.cols_run (gate0 l F).row.cr 2 (geoCv (gate0 l F).row.cr) _
      ((callInputs l F kclk coef A a ha).starParams req.n hs)
      (starParams_r l F kclk coef A a ha req.n hs) sfx req.word hw hW hW2 ?_
    have hb := geo_budget l F EG cG kclk coef A a ha hA hc req hcall hs (40 * req.n + 21 + 2000 * (req.n + 2) ^ 4) (by omega)
    show 2 * (frontCost req.word req.n 2 (geoCv (gate0 l F).row.cr) + (PrimAsm.GeoNums.numsGCostE
      ((callInputs l F kclk coef A a ha).starParams req.n hs) (gate0 l F).row.cr + 40 * req.n + 21 + 2000 * (req.n + 2) ^ 4)) + 2 ≤ _
    omega⟩

/-- **The halves writer** at every call (`GeoIface2.SideWriterAt`). -/
noncomputable def sideAt (hA : geoD ≤ EG.Apre) (hc : geoC (gate0 l F).row.cr * 2 ^ geoD ≤ cG) :
    GeoIface2.SideWriterAt l F EG cG kclk coef A a ha :=
  ⟨mkStage (geoM (PrimAsm.GeoNums.sideW (gate0 l F).row.cr) 2 (geoCv (gate0 l F).row.cr)) (gInP 2) (gOutP 2)
    (gInP_ne_out 2), fun req hcall hs => by
    refine stage_run _ _ _ _ _ _ _ ?_
    obtain ⟨sfx, hw⟩ := call_word req
    obtain ⟨hW, _⟩ := geoW_ok (gate0 l F).row.cr req.n
    refine PrimAsm.GeoSide.side_run (gate0 l F).row.cr 2 (geoCv (gate0 l F).row.cr) _
      ((callInputs l F kclk coef A a ha).starParams req.n hs)
      (starParams_r l F kclk coef A a ha req.n hs) sfx req.word hw hW ?_
    have hb := geo_budget l F EG cG kclk coef A a ha hA hc req hcall hs (1 + 200 * (req.n + 3)) (by omega)
    show 2 * (frontCost req.word req.n 2 (geoCv (gate0 l F).row.cr) + (PrimAsm.GeoNums.numsGCostE
      ((callInputs l F kclk coef A a ha).starParams req.n hs) (gate0 l F).row.cr + 1 + 200 * (req.n + 3))) + 2 ≤ _
    omega⟩

/-- **The width writer** at every call (`GeoIface2.WidthWriterAt`). -/
noncomputable def widthAt (hA : geoD ≤ EG.Apre) (hc : geoC (gate0 l F).row.cr * 2 ^ geoD ≤ cG) :
    GeoIface2.WidthWriterAt l F EG cG kclk coef A a ha :=
  ⟨mkStage (geoM (PrimAsm.GeoNums.widthW (gate0 l F).row.cr) 2 (geoCv (gate0 l F).row.cr)) (gInP 2) (gOutP 2)
    (gInP_ne_out 2), fun req hcall hs => by
    refine stage_run _ _ _ _ _ _ _ ?_
    obtain ⟨sfx, hw⟩ := call_word req
    obtain ⟨hW, _⟩ := geoW_ok (gate0 l F).row.cr req.n
    refine PrimAsm.GeoSide.width_run (gate0 l F).row.cr 2 (geoCv (gate0 l F).row.cr) _
      ((callInputs l F kclk coef A a ha).starParams req.n hs)
      (starParams_r l F kclk coef A a ha req.n hs) sfx req.word hw hW ?_
    have hb := geo_budget l F EG cG kclk coef A a ha hA hc req hcall hs (1 + 100 * (req.n + 3)) (by omega)
    show 2 * (frontCost req.word req.n 2 (geoCv (gate0 l F).row.cr) + (PrimAsm.GeoNums.numsGCostE
      ((callInputs l F kclk coef A a ha).starParams req.n hs) (gate0 l F).row.cr + 1 + 100 * (req.n + 3))) + 2 ≤ _
    omega⟩

end Pack

end NearCubicWires.WireExponent3_5.PrimT.GeoPack

end
