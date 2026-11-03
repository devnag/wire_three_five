import Proof.Wire_3_5.FinalPass.S5TChB

/-! # S5-THR, part 25: the THR path (P3:2150-2157, 2543-2558, 2596-2599, 3083-3086)

The THR half's THR branch on its layout, from the parse's exit: the first docks (`chainA_spec`: the fill count, T's
prep, W6), the next docks (`chainB_spec`: the front end, the data stage's inputs, the data stage), and the tail
(`tail_spec` on the named streams `tailSN` and registers `tailRg`): all eight THR slots written.

* `thrPathM`, `thrPathCost`, **`thrPath_spec`**.

Paper quantities of the main type: THR slots `8 … 15` (S2's call words and numbers `thrWords`, `thrNums`) at the
W6 numbers `v = thrNumVals` and the fixed hash's data `thrMP v.M v.A v.Bs v.den`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.HashSeed NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (dockS updS sTape_val)
open NearCubicWires.WireExponent3_5.PrimThrW.TopFront2 (tf2InPorts tf2OutPorts TF2Ok)
open NearCubicWires.WireExponent3_5.PrimThrW.Nums3 (nums3InPorts nums3OutPorts)
open NearCubicWires.SupplierPipeline

section Path
variable (D : ℕ) (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ) (cap : ℕ)

/-- The fixed hash's parameters from the W6 numbers. -/
abbrev mpOf (v : PrimThrW.Joins.ThrNumVals) : MajorantParams := PrimThrW.Joins.thrMP v.M v.A v.Bs v.den

theorem tail_hi (k : Fin 19) (hk : 10 ≤ k.val) :
    (14 + D ≤ tailA k + tailB k * D ∧ tailA k + tailB k * D ≤ 20 + D) ∨
      (7 ≤ tailA k + tailB k * D ∧ tailA k + tailB k * D ≤ 8) := by
  fin_cases k <;> simp [tailA, tailB] at hk ⊢ <;> omega

theorem tail_hi9 (k : Fin 19) (hk : 9 ≤ k.val) :
    (14 + D ≤ tailA k + tailB k * D ∧ tailA k + tailB k * D ≤ 739 + D) ∨
      (7 ≤ tailA k + tailB k * D ∧ tailA k + tailB k * D ≤ 8) := by
  fin_cases k <;> simp [tailA, tailB] at hk ⊢ <;> omega

end Path

end NearCubicWires.WireExponent3_5.FinalPass.S5T
