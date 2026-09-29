import Proof.Wire_3_5.Primitive.Writers.GeoNums
import Proof.Wire_3_5.Primitive.SeedFix.C4Geo

/-! # PA (d): the halves and width writers for the C4.L (`C4Geo.sideField P`, `1^(C4Geo.width P)`)

P3:1213-1215 (star:partition): "Assign `r/2` whole blocks to each side. [...] Split the remaining `n−rb` coordinates as
evenly as possible": the left half is the `r/2` left blocks and the first `⌈(n−rb)/2⌉` unblocked coordinates
(`centerSide`, `C4Geo.side`), and the printer's dense width is `(r/2)·b + ⌈(n−rb)/2⌉` (`C4Geo.width`, P3:1709-1737).
The writers are `GeoFront.geoM` around PA's `GeoNums.widthW` / `GeoNums.sideW`.

* `side_eq` (`side P = 1^A 0^A 1^h 0^rest`), **`sideField_eq`** (its marks = `GeoNums.sideWord`), `width_eq`;
* **`width_run`**: `WriterRun (geoM (widthW c_r) Dv Cv) … w (1^(C4Geo.width P))`;
* **`side_run`**: `WriterRun (geoM (sideW c_r) Dv Cv) … w (C4Geo.sideField P)`.

Paper quantities of the main types: the halves `centerSide` (P3:1213-1215) and the printer's dense width. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.GeoSide
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront NearCubicWires.WireExponent3_5.PrimAsm.GeoNums
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.BlockPlatform

theorem ofFn_blocks (n a c d : ℕ) (h : 2 * a + c + d = n) :
    List.ofFn (fun x : Fin n => decide (x.val < a ∨ (2 * a ≤ x.val ∧ x.val < 2 * a + c))) =
      List.replicate a true ++ List.replicate a false ++ List.replicate c true ++ List.replicate d false := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_append, List.length_append, List.length_replicate,
      List.getElem_replicate]
    split_ifs <;> simp <;> omega

/-- **The halves**: `1^A 0^A 1^h 0^rest`. -/
theorem side_eq (P : StarParams) : PrimT.C4Geo.side P = List.replicate (aOf P) true ++ List.replicate (aOf P) false ++
    List.replicate (hLv P) true ++ List.replicate (P.n - P.r * P.b - hLv P) false := by
  have hr := rb_eq P
  have hrb := P.r_mul_b_le
  have hl : hLv P ≤ P.n - P.r * P.b := by unfold hLv; omega
  rw [← ofFn_blocks P.n (aOf P) (hLv P) (P.n - P.r * P.b - hLv P) (by omega)]
  unfold PrimT.C4Geo.side
  congr 1
  funext x
  simp only [StarParams.centerSide, hLv]
  rw [decide_eq_decide]
  unfold aOf at hr ⊢
  constructor <;> intro h <;> omega

theorem marks_replicate (k : ℕ) (b : Bool) : marks (List.replicate k b) = reps k [true, b] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ', RepairOrdinary.Streaming.marks_append, ih, reps_succ]; rfl

/-- **The halves' field is the writer's word.** -/
theorem sideField_eq (P : StarParams) :
    PrimT.C4Geo.sideField P = sideWord (aOf P) (hLv P) (P.n - P.r * P.b - hLv P) := by
  unfold PrimT.C4Geo.sideField sideWord
  rw [frame_marksG, side_eq]
  simp only [RepairOrdinary.Streaming.marks_append, marks_replicate]

/-- The printer's dense width. -/
theorem width_eq (P : StarParams) : PrimT.C4Geo.width P = aOf P + hLv P := rfl

/-- **The width writer's run**: `frame w ↦ 1^(C4Geo.width P)`. -/
theorem width_run (cr Dv Cv Bud : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hW : 2 * P.n + cr + 20 ≤ UnaryCalc.value Dv Cv P.n)
    (hB : 2 * (frontCost w P.n Dv Cv + (numsGCostE P cr + 1 + 100 * (P.n + 3))) + 2 ≤ Bud) :
    WriterIfaceJ.WriterRun (geoM (widthW cr) Dv Cv) Bud (gInP Dv) (gOutP Dv) w
      (List.replicate (PrimT.C4Geo.width P) true) := by
  obtain ⟨σF, c, hx, hO, hI, hc⟩ := widthW_spec cr (UnaryCalc.value Dv Cv P.n) P hrP sfx w hw hW
  exact geo_run (widthW cr) Dv Cv P.n c Bud w sfx _ hw σF hx hI (by rw [hO, width_eq]) (by omega)

/-- **The halves writer's run**: `frame w ↦ C4Geo.sideField P`. -/
theorem side_run (cr Dv Cv Bud : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hW : 2 * P.n + cr + 20 ≤ UnaryCalc.value Dv Cv P.n)
    (hB : 2 * (frontCost w P.n Dv Cv + (numsGCostE P cr + 1 + 200 * (P.n + 3))) + 2 ≤ Bud) :
    WriterIfaceJ.WriterRun (geoM (sideW cr) Dv Cv) Bud (gInP Dv) (gOutP Dv) w (PrimT.C4Geo.sideField P) := by
  obtain ⟨σF, c, hx, hO, hI, hc⟩ := sideW_spec cr (UnaryCalc.value Dv Cv P.n) P hrP sfx w hw hW
  exact geo_run (sideW cr) Dv Cv P.n c Bud w sfx _ hw σF hx hI (by rw [hO, sideField_eq]) (by omega)

end NearCubicWires.WireExponent3_5.PrimAsm.GeoSide
