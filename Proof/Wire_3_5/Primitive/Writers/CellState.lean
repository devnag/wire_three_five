import Proof.Wire_3_5.Primitive.Writers.UnitReady
import Proof.Wire_3_5.Primitive.Writers.HashFlat

/-! # PA (d), the writers' cell states (the shared loop's interface)

The SYM and HASH writers (and the THR writer's FILTER rows) are one bounded `Cells.ofScrub` loop over a flat unit
index `j` on the cell layout `WState (LNS x) LNR` (`SymLayout`). This module fixes the states the loop's stages meet:

* **`blankCell x w out j`**: the entry of unit `j`: the request word `frame w` on stream `0` (head `0`), the output so
  far with its closing `false`, `out ++ [false]`, on stream `1` (head on that `false`), the counter `1^j` on stream `2`
  (head `0`); every other stream empty, every register `0`, the cell `false`;
* **`reqCell x w out j e r s`**: the entry of a REQUEST unit: `blankCell` with the unit's entry `e`, printed row `r` and
  target `s` in the registers `QE = 300`, `QR = 301`, `QS = 302` (the loop's decode writes them; `symEmit`'s layout);
* the branch flags: stream `150` (`[true]`: the POP pipeline), stream `151` (`[true]`: the FILTER pipeline);
* **`HashReqSpec`**: the HASH writer's request decode (C6's piece): from `reqCell` of the HASH entry `e` (unit
  `5e + 2`, row `0`, target `0`) to a `UnitReady.FiltReady` state of the aux FILTER row `hashRowQ e` (C5's aux filter
  params `auxP`, seed `auxEnum (e % nE)`, `L = 2Σ|carriers|`, labels `sliceLabs (4·(e / nE)) |thrPool| 0 L`), the
  FILTER flag raised, the request and counter kept, within `bound` (which also bounds the FILTER pipeline).

Paper quantity of the main types: the HASH writer's unit (the HASH tape, `HashFlat.hashTape_flat`) printed by the FILTER
pipeline at the aux row (`UnitReady.filtPipe_ready`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.UnitReady NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimT.WalkBank NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.PopPipe NearCubicWires.WireExponent3_5.Stars


/-- **The blank cell state of unit `j`**. -/
def blankCell (x : ℕ) (w out : List Bool) (j : ℕ) : WState (LNS x) LNR :=
  ⟨fun i => if i = sk x 1 then out.length else 0,
    fun i => if i = sk x 0 then frame w else if i = sk x 1 then out ++ [false] else
      if i = sk x 2 then List.replicate j true else [],
    fun _ => 0, false⟩

theorem blankCell_st0 (x : ℕ) (w out : List Bool) (j : ℕ) : (blankCell x w out j).st (sk x 0) = frame w := by
  simp [blankCell]

theorem blankCell_st1 (x : ℕ) (w out : List Bool) (j : ℕ) : (blankCell x w out j).st (sk x 1) = out ++ [false] := by
  simp [blankCell, sk_ne (x := x) 1 0 (by decide)]

theorem blankCell_st2 (x : ℕ) (w out : List Bool) (j : ℕ) :
    (blankCell x w out j).st (sk x 2) = List.replicate j true := by
  simp [blankCell, sk_ne (x := x) 2 0 (by decide), sk_ne (x := x) 2 1 (by decide)]

section Hash
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIface NearCubicWires.WireExponent3_5.PrimAsm.HashFlat
open NearCubicWires.WireExponent3_5.PrimAsm.Records

end Hash

end NearCubicWires.WireExponent3_5.PrimAsm.CellState
