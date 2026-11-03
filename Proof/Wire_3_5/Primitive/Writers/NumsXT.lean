import Proof.Wire_3_5.Primitive.ThresholdWriter.Shell2
import Proof.Wire_3_5.Primitive.Writers.SparseNum

/-! # for THR (v2): the THR dimension stage at `mOfT KL P = mOf P + KL·L²`

P3:2621-2623 (row:radix, the RADIX rows' `2^{O(L²)}` expansion) and THR's `PrimThrW.Shell2.mOfT`: the THR writer's
loop and scrub are dimensioned by `n' = 2^{mOf P + KL·L²}`. ShellX's dimension program (`NumsX.numsW`: `n`, the star
numbers, `m = 2·kh + L`, the CapReader source) with one more stage before the source: `m += (L·KL)·L`.

* `klW` (the extra stage), **`numsWT`**, **`numsWT_spec`** (from the filled state: the source `srcWord (mOfT KL P)`, the
  request and the fill count kept, within `numsCostT`);
* `numsPT`, **`numsMT`** (the stage, every head back at `0`), `numsStageCostT`, **`nums_stepT`**.

Paper quantity of the main type: the dimension `2^{mOf P + KL·L²}` of the THR writer (`kh = s·(r/2)` of star:partition,
`L` of the ledger). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.NumsXT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimAsm.NumsX
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-! ## The program -/

def rA : Fin NR := 27
def rB : Fin NR := 28
def rQ : Fin NR := 29
def rX : Fin NR := 30
def rY : Fin NR := 31

/-- `rB := L·KL` (`L` in `SN 1`, `KL` in `rQ`). -/
def mLK : Fin 5 ↪ Fin NR := ⟨![SN 1, rQ, rB, rX, rY], by decide⟩

/-- `rM := rM + rB·L` (`L` copied to `rA`). -/
def mML : Fin 5 ↪ Fin NR := ⟨![rB, rA, rM, rX, rY], by decide⟩

/-- The extra stage: `m += (L·KL)·L`. -/
def klW (KL : ℕ) : WM NS NR :=
  .seq (FinalPass.Hash4.wcopyR (SN 1) rA rT) (.seq (StarNums.incN rQ KL) (.seq (mulAddW mLK) (mulAddW mML)))

/-- The program's cost bound. -/
def numsCostT (n cr KL W : ℕ) : ℕ :=
  numsCost n cr + 60 * (KL * (n + 2) * (n + 2)) + 4 * UnaryPow.sq (2 * W + 2)

theorem mOfT_eq (KL : ℕ) (P : Shared.StarParams) :
    mOf P + (0 + Nat.clog 2 (P.n + 2) * KL) * Nat.clog 2 (P.n + 2) = PrimThrW.Shell2.mOfT KL P := by
  unfold PrimThrW.Shell2.mOfT
  ring

/-! ## The stage as one run -/

/-- The stage's cost before the teardown. -/
def numsStageCostT (n cr KL W : ℕ) : ℕ := 11 * W + 20 + 1 + 1 + 1 + numsCostT n cr KL W


end NearCubicWires.WireExponent3_5.PrimAsm.NumsXT
