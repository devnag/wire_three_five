import Proof.Wire_3_5.Selection.CosFin

/-! # C1.5: the c1 node's residual fills, named (P3:1324-1362, 3673)

The producer `c1Impl_of` takes the machine (`t` tapes, `s` states), `2 ≤ t`, the output tape `o ≠ 0`, the cost, the run
residual and, per input-size degree, the envelope, the coefficient and the class residual (`C1Impl`: C1 implements
`star:selection` at every degree). Each is named here: `selT`, `selS`, `selM` (the one register machine `Pw`,
compiled), `selHt`, `selO` (stream `1`), `selHo`, `selCost`, **`selRunF`**, **`selWithinF`**, and the assembled
**`selImplF`**. Paper quantity: the selected coset's word, within the selection time. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5.Machine
open NearCubicWires.WireExponent3_5.SelectionMachine.Plan (C1Run C1Within c1Impl_of)
open NearCubicWires.WireExponent3_5.UnionMachine.Plan (C1Impl)

/-- The tape count: `49 + 1` streams, the result cell, `112` registers. -/
def selT : ℕ := 49 + 2 + 112

/-- The state count of the compiled program. -/
def selS : ℕ := (FinalPass.Tm.WM.toProg Pw).size

/-- **The machine**: the register machine `Pw`, compiled. -/
def selM : Machine selT selS := (FinalPass.Tm.WM.toProg Pw).compile

theorem selHt : 2 ≤ selT := by unfold selT; norm_num

/-- The output tape: stream `1`. -/
def selO : Fin selT := FinalPass.Tm.sTape (nr := 112) (1 : Fin 50)

theorem selHo : selO.val ≠ 0 := Top.sTape_ne_zero (nr := 112) (1 : Fin 50) (by decide)

/-- The machine's cost. -/
def selCost : SelectionReq → ℕ := costF parseCostF

/-- **The run residual** at the named fills. -/
theorem selRunF : C1Run selM selO selCost := selRun

/-- **The class residual** at the named fills. -/
theorem selWithinF (d : ℕ) : C1Within d (selEnv d) (selCoef d) selCost := selWithin d

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
