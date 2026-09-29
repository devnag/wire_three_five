import Proof.Wire_3_5.Primitive.Writers.CellUnit

/-! # The POP setup's interface, (iii)

A SYM POP unit (circuit row `r ≥ |carriers|`, target `s` in the clamp preimage) hands the unit machine a POP-ready state
(`UnitReady.PopReady`), whose pipeline (`CellUnit.unitM`'s branch `150`, `PopPipe.popPipe_ready`) prints the POP row's
body. The decode writes the row's values into the POP setup's entry bank; the setup machine builds `PopReady`.

* the entry registers `ppM … ppL` (`400 … 409`) and **`PopIn`** (the unit's streams as in `FsIn2`, the ten values
  `M, B, errExp` of the flat list, the list seed's index `f`, the sign bit, the target `s`, `r4`, `G`, `off`, `L`;
  registers below `250` and from `410` on zero);
* the pipeline's parameters, explicit (the pipeline bound must be boundable): `popMlab = off + L + (r4+4)·G`,
  `popLw`, `popCAP`, `popLL`, `popR`, `popCp`, the rulers `popRW = 2·sideB(rank) + 1`;
* **`PopSetupSpec W`**: a program, a capacity need, a bound, and the run from `PopIn` to `PopReady` at the list seed
  `(flatSeedEquiv Pl).symm f` and the explicit parameters, the POP flag raised, the request and counter kept.

Paper quantity of the main type: the POP-ready unit state of the flat list's row `[report = s]` at the call's list seed
(list:flatten P3:1491-1498, row:sym P3:2477-2496). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopSetup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.UnitReady
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
open NearCubicWires.WireExponent3_5.PrimAsm.PopLink NearCubicWires.WireExponent3_5.PrimAsm.PopParams
open NearCubicWires.WireExponent3_5.PrimT.WalkBank

/-! ## The entry bank -/

def ppM : Fin LNR := ⟨400, by decide⟩
def ppB : Fin LNR := ⟨401, by decide⟩
def ppErr : Fin LNR := ⟨402, by decide⟩
def ppSeed : Fin LNR := ⟨403, by decide⟩
def ppSgn : Fin LNR := ⟨404, by decide⟩
def ppS : Fin LNR := ⟨405, by decide⟩
def ppR4 : Fin LNR := ⟨406, by decide⟩
def ppG : Fin LNR := ⟨407, by decide⟩
def ppOff : Fin LNR := ⟨408, by decide⟩
def ppL : Fin LNR := ⟨409, by decide⟩

/-- **The POP setup's entry bank**: the unit's streams (request `frame w` at `0`, output `out ++ [false]` at `|out|`,
counter `1^j` at `0`, data `u`, every other stream blank), the cell `false`, the ten values in `400 … 409`, every
register below `250` and from `410` on `0`. -/
structure PopIn (x : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool)
    (M B err f sg s r4 G off L : ℕ) : Prop where
  s0 : σ.st (sk x 0) = frame w
  h0 : σ.sh (sk x 0) = 0
  s1 : σ.st (sk x 1) = out ++ [false]
  h1 : σ.sh (sk x 1) = out.length
  s2 : σ.st (sk x 2) = List.replicate j true
  h2 : σ.sh (sk x 2) = 0
  s113 : σ.st (sk x 113) = u
  blank : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 → σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0
  blankT : ∀ k : Fin x, σ.st (sT x k) = [] ∧ σ.sh (sT x k) = 0
  cell : σ.cell = false
  vM : σ.val ppM = M
  vB : σ.val ppB = B
  vErr : σ.val ppErr = err
  vSeed : σ.val ppSeed = f
  vSgn : σ.val ppSgn = sg
  vS : σ.val ppS = s
  vR4 : σ.val ppR4 = r4
  vG : σ.val ppG = G
  vOff : σ.val ppOff = off
  vL : σ.val ppL = L
  zLow : ∀ r : Fin LNR, r.val < 250 → σ.val r = 0
  zHigh : ∀ r : Fin LNR, 410 ≤ r.val → σ.val r = 0

/-! ## The pipeline's parameters, explicit -/

/-- The labels' bound `off + L + (r4 + 4)·G` (`PopReady.hM` at equality). -/
def popMlab (r4 G off L : ℕ) : ℕ := off + L + (r4 + 4) * G

/-- The level words' width (`PopReady.hlw`). -/
def popLw (Pl : FlatListParams) (L : ℕ) : ℕ :=
  lwSumF (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J L + Pl.M + 2

/-- The labels' capacity (`PopReady.hCAP`). -/
def popCAP (r4 G off L : ℕ) : ℕ := labSum (sliceLabs r4 G off L)

/-- The labels' word length (`PopReady.hLL`). -/
def popLL (r4 G off L : ℕ) : ℕ := ((sliceLabs r4 G off L).flatMap labE).length

/-- The scrub capacity of the POP row (`PopReady.hR`). -/
def popR (Pl : FlatListParams) (r4 G off L : ℕ) : ℕ :=
  PopCap.popKc L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L)
    (PopNums.blF L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) (popLw Pl L) Pl.M) + 1

/-- The log capacity of the POP row (`PopReady.hcp`). -/
def popCp (Pl : FlatListParams) (r4 G off L : ℕ) : ℕ :=
  PopCap.popCapB Pl.walkLen (popR Pl r4 G off L) (PopCap.popPW L (3 * lbP Pl) (popMlab r4 G off L))

/-- The walk bank's rulers at the lower bound `2·sideB(rank) + 1` (`PopReady.hRW`, `hLW`). -/
def popRW (Pl : FlatListParams) : ℕ := 2 * sideB Pl.base.rank + 1

/-! ## The setup -/

/-- **The POP-setup machine** (interface; builds it): from `PopIn` with the flat list's parameters, the
list seed's index `f < |FlatSeed|`, the sign, the target `s ≤ M` and the slice, within `bound cap` at every capacity
`≥ need`, the request and counter kept, the POP flag raised, and `PopReady` at the list seed `(flatSeedEquiv Pl).symm f`
and the explicit parameters. -/
structure PopSetupSpec (W : WalkBankProducer) where
  prog : WM (LNS W.x) LNR
  need : FlatListParams → ℕ → ℕ → ℕ → ℕ → ℕ
  bound : ℕ → ℕ
  run : ∀ (cap : ℕ) (Pl : FlatListParams) (f : ℕ) (hf : f < Fintype.card Pl.FlatSeed) (L r4 G off : ℕ) (sgn : Bool)
    (s : ℕ) (hs : s < Pl.M + 1) (w out u : List Bool) (j : ℕ) (σ : WState (LNS W.x) LNR),
    need Pl L r4 G off ≤ cap →
    PopIn W.x σ w out j u Pl.M Pl.B Pl.errExp f (if sgn then 1 else 0) s r4 G off L →
    ∃ τ m, WExec cap prog σ τ m ∧ m ≤ bound cap ∧
      τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 ∧
      τ.st (sk W.x 150) = [true] ∧ τ.sh (sk W.x 150) = 0 ∧
      ∃ hlabs : 4 * L ≤ (sliceLabs r4 G off L).length,
        PopReady cap W τ out Pl ((Enum.flatSeedEquiv Pl).symm ⟨f, hf⟩) L r4 G off (popMlab r4 G off L) (popLw Pl L)
          (popCAP r4 G off L) (popLL r4 G off L) (popR Pl r4 G off L) (popCp Pl r4 G off L) (popRW Pl) (popRW Pl) sgn
          ⟨s, hs⟩ hlabs

end NearCubicWires.WireExponent3_5.PrimAsm.PopSetup
