import Proof.Wire_3_5.Primitive.ThresholdWriter.Joins
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.Primitive.Writers.SymFlat
import Proof.Wire_3_5.Primitive.Writers.CellUnit

/-! # queue item 2: the THR FILTER rows dock `FiltSetupSpec5` (C6's v5)

P3:1523-1526 (row:matrix, the THR rows): "A regular filter is one more Boolean polynomial of degree `O_D(L)`, by
\cref{filt:gap}, hence fits the same base-degree" bound; P3:2019-2030 (filt:gap): the filter `F_e(Z)` of seed `e`.
A THR entry's FILTER row `jr < |carriers|` is `Records.filtRow (thrSlices …) FP e G row nw jr` (`Records.thrGroups`),
printed by the FILTER pipeline (`UnitReady.filtPipe_ready`) from `FiltReady`, which C6's setup machine establishes from
`FsIn2` at the eight values `Joins.thrFiltVals`. v5 fixes the walk bank's rulers at `rulerW FP`, so the pipeline's bound
is the explicit **`Bp = filtPipeBound FP e L (4·row) |thrPool| off (rulerW FP) (rulerW FP)`**; the unit budget bounds it.

* **`FiltOK cap W σ out e Bp`**: the FILTER-ready disjunct of a unit's decode (verbatim the third disjunct of PA's
  `CellUnit.DecOK`: FILTER flag up, POP/RADIX flag down, `FiltReady`, the body `e` named, the pipeline within `Bp`);
  `FiltOK.toDecOK`;
* `thrFilt_body`: the THR FILTER row's printed body (`SymFlat.unitBody`) is `filtRefC` at the slice's labels;
* **`thrFilt_dock5`**: from `FsIn2` at the seed `e`'s index and the THR row's slice, `FiltSetupSpec5.run` reaches
  `FiltOK` with the row's body and `Bp` at the rulers `rulerW FP`, the request and the counter kept.

Paper quantity of the main type: the THR FILTER row's printed expression (C2's `filtRefC`, the filter `F_e` of
filt:gap at the slice's labels). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.FiltDock5
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.UnitReady
open NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.SupplierPipeline

/-- **The FILTER-ready disjunct of a unit's decode**: FILTER flag `151` up, flag `150` down, `FiltReady` at some filter,
seed and slice, the unit's body `e` the printed `filtRefC`, the pipeline within `Bp`. -/
def FiltOK (cap : ℕ) (W : WalkBankProducer) (σ : WState (LNS W.x) LNR) (out e : List Bool) (Bp : ℕ) : Prop :=
  σ.st (sk W.x 150) = [] ∧ σ.sh (sk W.x 150) = 0 ∧ σ.st (sk W.x 151) = [true] ∧ σ.sh (sk W.x 151) = 0 ∧
    ∃ (P : GapParams) (e' : GapSeed P) (L r4 G off Mlab RW LW : ℕ)
      (sample : SupplierWalk.MargulisWalkSample (2 ^ (wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1)),
      FiltReady cap W σ out P e' L r4 G off Mlab RW LW sample ∧
      e = (filtRefC (filterTable P e' L) (SupplierWalk.majorityThreshold P.walkLen) L true
        (sliceLabs r4 G off L)).flatMap (fun t => true :: ListMachine.Rec.termWord t) ∧
      filtPipeBound P e' L r4 G off RW LW ≤ Bp

section Thr
variable (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
  (carriers : List (Stars.Carrier P.n))

/-- **The THR FILTER row's printed body** is `filtRefC` at the slice's labels. -/
theorem thrFilt_body (FP : GapParams) (e : GapSeed FP) (G row nw jr : ℕ) :
    SymFlat.unitBody (Records.filtRow (Records.thrSlices P Cs carriers) FP e G row nw jr) =
      (filtRefC (filterTable FP e ((Records.thrSlices P Cs carriers).getD jr []).length)
        (SupplierWalk.majorityThreshold FP.walkLen) ((Records.thrSlices P Cs carriers).getD jr []).length true
        (sliceLabs (4 * row) G (Records.sliceOff (Records.thrSlices P Cs carriers) jr)
          ((Records.thrSlices P Cs carriers).getD jr []).length)).flatMap
        (fun t => true :: ListMachine.Rec.termWord t) := by
  unfold SymFlat.unitBody
  rw [Joins.thrFilt_emit]

/-- **The THR FILTER dock, v5**: from `FsIn2` at the seed `e`'s index and row `jr`'s slice of the THR pool, C6's setup
reaches `FiltOK` with the row's printed body and the pipeline bound at the rulers `rulerW FP`, within `bound cap`;
the request and the counter kept. -/
theorem thrFilt_dock5 (W : WalkBankProducer) (F5 : FiltSetup.FiltSetupSpec5 W) (cap : ℕ) (FP : GapParams)
    (e : GapSeed FP) (row nw jr : ℕ) (w out u : List Bool) (j : ℕ) (σ : WState (LNS W.x) LNR) (hcap1 : 1 ≤ FP.cap)
    (hneed : F5.need FP.len FP.cap FP.errExp ((Records.thrSlices P Cs carriers).getD jr []).length (4 * row)
      (Records.thrPool P Cs carriers).length (Records.sliceOff (Records.thrSlices P Cs carriers) jr)
      (Fintype.card (GapSeed FP)) ≤ cap)
    (hd : FiltSetup.FsIn2 W.x σ w out j u FP.len FP.cap FP.errExp (Enum.gapSeedEquiv FP e) (4 * row)
      (Records.thrPool P Cs carriers).length (Records.sliceOff (Records.thrSlices P Cs carriers) jr)
      ((Records.thrSlices P Cs carriers).getD jr []).length) :
    ∃ τ m, WExec cap F5.prog σ τ m ∧ m ≤ F5.bound cap ∧
      FiltOK cap W τ out
        (SymFlat.unitBody (Records.filtRow (Records.thrSlices P Cs carriers) FP e (Records.thrPool P Cs carriers).length
          row nw jr))
        (filtPipeBound FP e ((Records.thrSlices P Cs carriers).getD jr []).length (4 * row)
          (Records.thrPool P Cs carriers).length (Records.sliceOff (Records.thrSlices P Cs carriers) jr)
          (FiltSetup.rulerW FP) (FiltSetup.rulerW FP)) ∧
      τ.st (sk W.x 0) = frame w ∧ τ.sh (sk W.x 0) = 0 ∧ τ.st (sk W.x 2) = List.replicate j true ∧
      τ.sh (sk W.x 2) = 0 := by
  obtain ⟨τ, m, hx, hm, h0, h0h, h2, h2h, f150, f150h, f151, f151h, Mlab, RW, LW, sample, hRW, hLW, hR⟩ :=
    F5.run cap FP (Enum.gapSeedEquiv FP e) (Enum.gapSeedEquiv FP e).isLt
      ((Records.thrSlices P Cs carriers).getD jr []).length (4 * row) (Records.thrPool P Cs carriers).length
      (Records.sliceOff (Records.thrSlices P Cs carriers) jr) w out u j σ hcap1 (Joins.thrFilt_labs _ _ _ _) hneed hd
  have he : (Enum.gapSeedEquiv FP).symm ⟨(Enum.gapSeedEquiv FP e : ℕ), (Enum.gapSeedEquiv FP e).isLt⟩ = e := by simp
  rw [he] at hR
  subst hRW hLW
  refine ⟨τ, m, hx, hm, ⟨f150, f150h, f151, f151h, FP, e, _, _, _, _, Mlab, _, _, sample, hR,
    thrFilt_body P Cs carriers FP e _ row nw jr, le_rfl⟩, h0, h0h, h2, h2h⟩

end Thr

end NearCubicWires.WireExponent3_5.PrimThrW.FiltDock5
