import Proof.Wire_3_5.Primitive.Writers.CellState
import Proof.Wire_3_5.Primitive.Writers.Enum

/-! # PA (d): the FILTER-setup machine's interface (built once by C6; docked by SYM, THR, HASH)

P3:2019-2054, 2096-2100 (filt:gap, the regular filter at a call: its parameters `M` (`len`), `U` (`cap`),
`ε = 2^{−errExp}`, a seed walk) and P3:1519-1526 (a printed row's labels): a writer cell prints a FILTER row through
`UnitReady.filtPipe_ready` once its state is `UnitReady.FiltReady` for the filter's `GapParams P`, the seed `e` and the
row's labels `sliceLabs r4 G off L`. The SYM FILTER rows, the THR FILTER rows and the HASH aux row
(C6's `CellState.HashReqSpec`) differ only in those values, so ONE machine reaches `FiltReady` from them:

* the entry bank **`FsIn`**: the cell's kept streams (request `sk 0`, output `sk 1`, counter `sk 2`, data `sk 113`),
  every other stream blank, the cell `false`; the values in the input registers `fsLen … fsL` (`400 … 407`): `P.len`,
  `P.cap`, `P.errExp`, the seed index `g` (base's enumeration, `Enum.gapSeedEquiv`), `r4`, `G`, `off`, `L`; registers
  `< 250` and `≥ 408` at `0`, registers `250 … 399` arbitrary (the callers' decode scratch, e.g. `QE`/`QR`/`QS`);
* **`FiltSetupSpec W`**: a program, a capacity need and a cost bound (both `PolyBounded` in the values' sum), and the
  run: from `FsIn`, within the bound, the request and counter kept, the FILTER flag raised, and `FiltReady` for the seed
  `(gapSeedEquiv P).symm g`, with the FILTER pipeline's own bound within the same bound (as `HashReqSpec`);
* the twin **`fsBank`** / **`fsIn_fsBank`**: the bank the callers' decode leaves (`blankCellD` plus the eight values)
  meets `FsIn`.

Paper quantities of the main type: the regular filter's parameters and seed (filt:gap) and the row's labels. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.UnitReady NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.PopPipe (sk_ne)

/-! ## The input registers -/

def fsLen : Fin LNR := ⟨400, by decide⟩
def fsCap : Fin LNR := ⟨401, by decide⟩
def fsErr : Fin LNR := ⟨402, by decide⟩
def fsSeed : Fin LNR := ⟨403, by decide⟩
def fsR4 : Fin LNR := ⟨404, by decide⟩
def fsG : Fin LNR := ⟨405, by decide⟩
def fsOff : Fin LNR := ⟨406, by decide⟩
def fsL : Fin LNR := ⟨407, by decide⟩

/-- **The FILTER setup's entry bank** (the cell `w`, `out`, `j`, data `u`; the eight values). -/
structure FsIn (x : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool)
    (len cap err g r4 G off L : ℕ) : Prop where
  s0 : σ.st (sk x 0) = frame w
  s1 : σ.st (sk x 1) = out ++ [false]
  h1 : σ.sh (sk x 1) = out.length
  s2 : σ.st (sk x 2) = List.replicate j true
  h2 : σ.sh (sk x 2) = 0
  s113 : σ.st (sk x 113) = u
  blank : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 → σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0
  blankT : ∀ k : Fin x, σ.st (sT x k) = [] ∧ σ.sh (sT x k) = 0
  cell : σ.cell = false
  vLen : σ.val fsLen = len
  vCap : σ.val fsCap = cap
  vErr : σ.val fsErr = err
  vSeed : σ.val fsSeed = g
  vR4 : σ.val fsR4 = r4
  vG : σ.val fsG = G
  vOff : σ.val fsOff = off
  vL : σ.val fsL = L
  zLow : ∀ r : Fin LNR, r.val < 250 → σ.val r = 0
  zHigh : ∀ r : Fin LNR, 408 ≤ r.val → σ.val r = 0

/-! ## The twin: the callers' bank -/

end NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup
