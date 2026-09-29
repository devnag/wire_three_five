import Proof.Wire_3_5.UnionMachine.FiltSetupIface3

/-! # The FILTER-setup interface, v5: the walk bank's rulers are explicit

`FiltSetupSpec4` gives the walk bank's ruler lengths `RW`, `LW` only existentially inside `FiltReady`,
with lower bounds; the FILTER pipeline's cost (`FiltPipe.filtPipeBound`) grows with both (`walkBankCost … RW LW`,
stage 6's `bodyCost … RW`), so no consumer could bound it. The setup writes both at exactly the lower bound
(**`rulerW P = 2·(wOf fieldBits labelBits · 128) + 1`**).

* **`FiltSetupSpec5 W`**: `FiltSetupSpec4` with the run concluding `RW = rulerW P` and `LW = rulerW P`.

Paper quantities of the main type: as `FiltSetupSpec` (the regular filter's parameters and seed, the row's labels),
with the seeds' count `|GapSeed P|` and the walk bank's rulers (the walk's side `2^{128·wOf}`, P3:2083-2100). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.UnitReady NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.Emit

/-- **The walk bank's ruler length**: `2·(wOf fieldBits labelBits · 128) + 1` (`FiltReady.hRW`, `hLW` at equality). -/
def rulerW (P : GapParams) : ℕ := 2 * (FinalPass.Filt.wOf P.fieldBits P.labelBits * 128) + 1

/-- **The FILTER-setup machine, v5**: `FiltSetupSpec4` with both rulers at `rulerW P`. -/
structure FiltSetupSpec5 (W : WalkBankProducer) where
  prog : WM (LNS W.x) LNR
  need : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  bound : ℕ → ℕ
  Cn : ℕ
  Dn : ℕ
  need_poly : ∀ len cap err L r4 G off S : ℕ,
    ValidatorPolynomialDomination.PolyBounded (need len cap err L r4 G off S)
      (len + cap + err + L + r4 + G + off + S) Cn Dn
  Cb : ℕ
  Db : ℕ
  bound_poly : ∀ c : ℕ, ValidatorPolynomialDomination.PolyBounded (bound c) c Cb Db
  run : ∀ (cap : ℕ) (P : GapParams) (g : ℕ) (hg : g < Fintype.card (GapSeed P)) (L r4 G off : ℕ)
    (w out u : List Bool) (j : ℕ) (σ : WState (LNS W.x) LNR),
    1 ≤ P.cap → (sliceLabs r4 G off L).length = 4 * L →
    need P.len P.cap P.errExp L r4 G off (Fintype.card (GapSeed P)) ≤ cap →
    FsIn2 W.x σ w out j u P.len P.cap P.errExp g r4 G off L →
    ∃ τ m, WExec cap prog σ τ m ∧ m ≤ bound cap ∧
      τ.st (sk W.x 0) = frame w ∧ τ.sh (sk W.x 0) = 0 ∧ τ.st (sk W.x 2) = List.replicate j true ∧
      τ.sh (sk W.x 2) = 0 ∧
      τ.st (sk W.x 150) = [] ∧ τ.sh (sk W.x 150) = 0 ∧ τ.st (sk W.x 151) = [true] ∧ τ.sh (sk W.x 151) = 0 ∧
      ∃ (Mlab RW LW : ℕ) (sample : SupplierWalk.MargulisWalkSample
          (2 ^ (FinalPass.Filt.wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1)),
        RW = rulerW P ∧ LW = rulerW P ∧
        FiltReady cap W τ out P ((Enum.gapSeedEquiv P).symm ⟨g, hg⟩) L r4 G off Mlab RW LW sample

end NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup
