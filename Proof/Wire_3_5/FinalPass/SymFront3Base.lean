import Proof.Wire_3_5.FinalPass.SymFront2
import Proof.Wire_3_5.UnionMachine.NumsA13Base
import Proof.Wire_3_5.UnionMachine.NumsA12Base
import Proof.Wire_3_5.UnionMachine.NumsC6Base
import Proof.Wire_3_5.UnionMachine.NumsPh3Base

/-! # The SYM front, part 3: the front at a SYM request (root #265, build once)

**`frontM`**: the phase (c) (`NumsC.phC3`: `n` and the roles), the width and the data stage's inputs (`prepW`), PA's
data stage docked (`dataDockM`, part 1 with the tapes exported), the counts unframed onto `113`, the SYM numbers
program lifted (the `numsBankG`: the whole register export), stream `113` rewound (part 2). The composition and its
arithmetic are the `NumsA12.aRun` with `numsBankG` and the rewind in place of `numsBank` and the finish.

**`front_run`**: from `CoreWordsMJ`'s entry at a SYM request, within `CF·(|fpIn|+1)^{DFs}` steps at every capacity above
`KF·(|fpIn|+1)^{DF}` (degrees on `fe`, coefficients on `F`), the exit **`FrontOut`**: the input kept, every head `0`,
the flat list's `M, B, errExp, |FlatSeed|` in `G 32, 33, 34, 41` (`symListParams` exactly), `n` in `dN`, the population
lengths `|symGates C_j|` (`0` past the tuple) in `330 + j`, every register within the bound, every filled slot's scan
word and gate table on the data tapes, the empty slots' scan tapes blank, the streams past the data region blank,
every residue within the bound.

Paper quantity of the main type: the SYM call's flat list `symListParams` (P3:1491-1498, 3049-3050) and its slices,
at the request, in the bank. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFront
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g g_ne npow_le)
open NearCubicWires.SupplierPipeline

section Gate
variable (x : ℕ) (hx : DataDock.DT + 3 ≤ x) (l : Literals)


/-- **The front's exit.** -/
structure FrontOut {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (Pl : FlatListParams)
    (w : List Bool) (B : ℕ) (τ : St x) : Prop where
  hin : τ.st (sIn x) = frame w
  heads : ∀ i, τ.sh i = 0
  cell : τ.cell = false
  vM : τ.val (SymDec.G 32) = Pl.M
  vB : τ.val (SymDec.G 33) = Pl.B
  vE : τ.val (SymDec.G 34) = Pl.errExp
  vK : τ.val (SymDec.G 41) = Fintype.card Pl.FlatSeed
  vN : τ.val SymDec.dN = n
  vL : ∀ (j : Fin 4) (h : j.val < a'), τ.val ⟨330 + j.val, by have := j.isLt; show 330 + j.val < 512; omega⟩ =
    (Stars.symGates (Cs ⟨j.val, h⟩)).length
  vL0 : ∀ j : Fin 4, a' ≤ j.val → τ.val ⟨330 + j.val, by have := j.isLt; show 330 + j.val < 512; omega⟩ = 0
  vle : ∀ q, τ.val q ≤ B
  scan : ∀ (i : Fin 4) (h : i.val < a'), τ.st (tmapA x hx (DataDock.iOf (Data.sSym i (PrimT.SymTab.scanSl 0)))) =
    Out.DataW.scanWord (Cs ⟨i.val, h⟩)
  gates : ∀ (i : Fin 4) (h : i.val < a'), τ.st (tmapA x hx (DataDock.iSym i)) =
    FinalPass.Corner.gatesW (PrimT.tabH (Stars.symGates (Cs ⟨i.val, h⟩))) (Stars.symGates (Cs ⟨i.val, h⟩))
  scan0 : ∀ i : Fin 4, a' ≤ i.val → τ.st (tmapA x hx (DataDock.iOf (Data.sSym i (PrimT.SymTab.scanSl 0)))) = []
  hi : ∀ k : Fin x, DataDock.DT + 3 ≤ k.val → τ.st (sT x k) = []
  resid : ∀ i, i ≠ sIn x → (τ.st i).length ≤ B

theorem cy_getD_zero {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (j : ℕ) (h : a' ≤ j) :
    (SymDec.cyOf Cs).getD j 0 = 0 := by
  rw [List.getD_eq_default]
  rw [SymDec.cyOf_length]
  exact h

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFront
