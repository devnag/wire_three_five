import Proof.Wire_3_5.FinalPass.ThrPtRS33

/-! # S2 (THR per point), part 48: the evaluator's capacity and step bound, polynomial in the size

`RWb U`: RowW's polynomial bound at size `6U`. **`needE`**: every capacity of the run (the rows', the setup's, the
loops') at a size bound `U`; **`boundE`**: the run's step bound at `U` (the setup `setupE`, one row `rowE`, the
cleanup `cleanE`). **`nb_le`**: both are at most `thrC · (U + 1)^thrD` (`PolyB`). Paper quantity: the per-point
evaluator's time `poly(ptSize)` (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- RowW's bound at size `6U`. -/
noncomputable def RWb (U : ℕ) : ℕ := DigsBody.rowWImpl.C * (6 * U + 1) ^ DigsBody.rowWImpl.D

/-- **The capacities** at a size bound. -/
noncomputable def needE (U : ℕ) : ℕ :=
  RWb U + popCap U U U U U + 4 * (U + U + 1) + (2 * U * (U + 1) + 2 * (U + 1) + U) + capTU U +
    (rowWordU U + U + U) + (2 * U + 10 * U + 2 * U + 2) + 2 * U + U * (1 + (U + 1) * (2 * (2 * U + 1))) + U +
    U * U + (U + 2 * U + 8 * U + U + 1)

/-- The setup's bound at a size bound. -/
def setupE (U : ℕ) : ℕ := setupCost U U U (Corner.cwCost U U U)

/-- The cleanup's bound at a size bound. -/
def cleanE (U : ℕ) : ℕ := cleanCost U U U U

/-- The digits' bound at a size bound. -/
def dlE (U : ℕ) : ℕ := digLoopCost U U U U U U U (4 * (U + U + 1))

/-- The row eraser's bound at a size bound. -/
def erE (U : ℕ) : ℕ := eraseRowCost U U U U U (rowWordU U)

/-- One row's bound at a size bound. -/
noncomputable def rowE (U : ℕ) : ℕ :=
  RWb U + 1 + (dlE U + 1 + ((7 * U + 1) + 1 + ((5 * (U * (U + 1) + U * (U + 1)) + 1) + 1 +
    ((costTU U + 2) + 1 + (8 + 1 + ((U * (18 * U + 50) + 1 + 1 + ((7 * U + 1) + 1 +
    (5 * (U * (U + 1) + U * (U + 1)) + 1))) + 1 + erE U))))))

theorem rowE_eq (U : ℕ) : rowCostU (RWb U) U (4 * (U + U + 1)) = rowE U := rfl

/-- **The step bound** at a size bound. -/
noncomputable def boundE (U : ℕ) : ℕ :=
  setupE U + 1 + ((U * ((U * (14 * U + 13 + rowE U) + 1) + 5 * U + 11) + 1) + 1 + cleanE U)

macro "polyb" : tactic => `(tactic| repeat (first | apply DigsBody.PolyB.add | apply DigsBody.PolyB.mul | apply PolyB_pow | exact DigsBody.PolyB.id | exact DigsBody.PolyB.const _))

theorem needE_poly : DigsBody.PolyB needE := by
  unfold needE RWb popCap capTU rowWordU
  polyb

theorem setupE_poly : DigsBody.PolyB setupE := by
  unfold setupE setupCost Corner.cwCost Corner.gateCost Corner.coreCost fmtCost
  polyb

theorem cleanE_poly : DigsBody.PolyB cleanE := by
  unfold cleanE cleanCost fmtCost
  polyb

theorem dlE_poly : DigsBody.PolyB dlE := by
  unfold dlE digLoopCost digCost popCost occCost bitDCost repCost repBodyCost ListEval.mainCost
  polyb

theorem costTE_poly : DigsBody.PolyB costTU := by
  unfold costTU
  polyb

theorem erE_poly : DigsBody.PolyB erE := by
  unfold erE eraseRowCost rowWordU
  polyb

theorem RWb_poly : DigsBody.PolyB RWb := by
  unfold RWb
  polyb

theorem rowE_poly : DigsBody.PolyB rowE := by
  have p7 : DigsBody.PolyB fun U : ℕ => 7 * U + 1 := by polyb
  have p5 : DigsBody.PolyB fun U : ℕ => 5 * (U * (U + 1) + U * (U + 1)) + 1 := by polyb
  have pX : DigsBody.PolyB fun U : ℕ =>
      U * (18 * U + 50) + 1 + 1 + ((7 * U + 1) + 1 + (5 * (U * (U + 1) + U * (U + 1)) + 1)) := by polyb
  have pT : DigsBody.PolyB fun U => costTU U + 2 := DigsBody.PolyB.add costTE_poly (DigsBody.PolyB.const 2)
  unfold rowE
  exact DigsBody.PolyB.add (DigsBody.PolyB.add RWb_poly (DigsBody.PolyB.const 1))
    (DigsBody.PolyB.add (DigsBody.PolyB.add dlE_poly (DigsBody.PolyB.const 1))
    (DigsBody.PolyB.add (DigsBody.PolyB.add p7 (DigsBody.PolyB.const 1))
    (DigsBody.PolyB.add (DigsBody.PolyB.add p5 (DigsBody.PolyB.const 1))
    (DigsBody.PolyB.add (DigsBody.PolyB.add pT (DigsBody.PolyB.const 1))
    (DigsBody.PolyB.add (DigsBody.PolyB.add (DigsBody.PolyB.const 8) (DigsBody.PolyB.const 1))
    (DigsBody.PolyB.add (DigsBody.PolyB.add pX (DigsBody.PolyB.const 1)) erE_poly))))))

theorem boundE_poly : DigsBody.PolyB boundE := by
  have y1 : DigsBody.PolyB fun U => 14 * U + 13 + rowE U :=
    DigsBody.PolyB.add (DigsBody.PolyB.add (DigsBody.PolyB.mul (DigsBody.PolyB.const 14) DigsBody.PolyB.id)
      (DigsBody.PolyB.const 13)) rowE_poly
  have y2 : DigsBody.PolyB fun U => U * (14 * U + 13 + rowE U) + 1 :=
    DigsBody.PolyB.add (DigsBody.PolyB.mul DigsBody.PolyB.id y1) (DigsBody.PolyB.const 1)
  have y3 : DigsBody.PolyB fun U => U * (14 * U + 13 + rowE U) + 1 + 5 * U + 11 :=
    DigsBody.PolyB.add (DigsBody.PolyB.add y2 (DigsBody.PolyB.mul (DigsBody.PolyB.const 5) DigsBody.PolyB.id))
      (DigsBody.PolyB.const 11)
  have y4 : DigsBody.PolyB fun U => U * (U * (14 * U + 13 + rowE U) + 1 + 5 * U + 11) + 1 :=
    DigsBody.PolyB.add (DigsBody.PolyB.mul DigsBody.PolyB.id y3) (DigsBody.PolyB.const 1)
  unfold boundE
  exact DigsBody.PolyB.add (DigsBody.PolyB.add setupE_poly (DigsBody.PolyB.const 1))
    (DigsBody.PolyB.add (DigsBody.PolyB.add y4 (DigsBody.PolyB.const 1)) cleanE_poly)

theorem nb_poly : DigsBody.PolyB fun U => needE U + boundE U := DigsBody.PolyB.add needE_poly boundE_poly

/-- The evaluator's polynomial constant. -/
noncomputable def thrC : ℕ := Classical.choose nb_poly

/-- The evaluator's polynomial degree. -/
noncomputable def thrD : ℕ := Classical.choose (Classical.choose_spec nb_poly)

theorem nb_le (U : ℕ) : needE U + boundE U ≤ thrC * (U + 1) ^ thrD :=
  Classical.choose_spec (Classical.choose_spec nb_poly) U

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
