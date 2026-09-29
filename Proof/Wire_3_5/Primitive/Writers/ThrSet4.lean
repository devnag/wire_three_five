import Proof.Wire_3_5.Primitive.Writers.ThrSet1
import Proof.Wire_3_5.Primitive.Writers.ThrSet2
import Proof.Wire_3_5.Primitive.Writers.ThrSet3

/-! # c4 THR block, the THR setup on the big bank

The THR stage runs on `3 + x'` tapes, `x' = thrXb L x3`. The first `3 + L.X` tapes are the SYM layout `L`; above them
sit the data stage's scratch region, the hash bits' machine's region and the finisher's region. The setup `setupT`:
1. The front (`C4Cap.frontM2`, lifted);
2. The v4 data stage `M3` (`data_dock`);
3. the hash bits' machine (`hb_dock`);
4. on the layout (lifted): the copy-in and the numbers machine of program `P` (`cb_run`), the tail (`tail_run`: the
   modulus words, the big unary words, the compiler request's fields), the pads (`eraseS`).
Its exit (**`setupT_run`**): on the first tapes, the setup exit bank (`C4Cap.setup_run2`'s list); the marked hash
bits on `hbT`; the bank blank from the finisher's region up.

Paper quantities of the main type: the loop's entry words and the finisher's inputs on their tapes (P3:3011-3016),
with the THR call's numbers and hash bits. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimAsm.BigBank
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

variable (L : Lay)

/-- The big bank's scratch count: the layout, the data stage's region, the hash bits' machine, the finisher. -/
def thrXb (x3 : ℕ) : ℕ := L.X + (Data.DS + 2 + Data.DR + 1 + x3) + (BX + 1) + 34

theorem hxb (x3 : ℕ) : 3 + L.X ≤ 3 + thrXb L x3 := by unfold thrXb; omega

/-- The data stage's region. -/
def offD : ℕ := 3 + L.X
/-- The hash bits' machine's region. -/
def offH (x3 : ℕ) : ℕ := 3 + L.X + (Data.DS + 2 + Data.DR + 1 + x3)
/-- **The finisher's region.** -/
def offT (x3 : ℕ) : ℕ := offH L x3 + (BX + 1)

theorem hoffD (x3 : ℕ) : offD L + (Data.DS + 2 + Data.DR + 1 + x3) ≤ 3 + thrXb L x3 := by
  unfold offD thrXb; omega
theorem hoffH (x3 : ℕ) : offH L x3 + (BX + 1) ≤ 3 + thrXb L x3 := by unfold offH thrXb; omega
theorem hoffT (x3 : ℕ) : offT L x3 + 34 ≤ 3 + thrXb L x3 := by unfold offT offH thrXb; omega

/-- **The hash bits' tape.** -/
def hbT (x3 : ℕ) : Fin (3 + thrXb L x3) := ⟨offH L x3 + 122, by unfold offH thrXb; have : BX = 676 := rfl; omega⟩

/-- The layout part after the front: the copy-in, the numbers machine, the tail, the pads. -/
noncomputable def restM (P : WM (LNS 0) LNR) :=
  Composition.machine (cbM L P) (Composition.machine L.tailM
    (CloseoutWitness.SelectedErase.machine L.maskLP L.gRR L.gLG))

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
