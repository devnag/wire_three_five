import Proof.Wire_3_5.FinalPass.SeamsWS

/-! # The final pass's assembly dock: every open producer as a typed argument

"The final pass costs `2^{n−k/4}n^{C_D}`" (P3:3046-3048, 3170-3181): `PlanFP.fpPlan E₅ CD₅ c₅ phases fits` gives
`∀ l, FinalPassLeaf l` from three phases per call family and the cost residual. This file composes the phases from
the producers that are NOT built yet, each taken as an argument at its type, so the top join typechecks now:

* **`Sw`** — the SYM evaluator's words (`SymWords`; the S3);
* **`X fam : SeedsWS`** — S4, at every call family;
* **`bridgeT fam : SeedsWS → SeedsProg2`** — BridgeT (S4's machine on the front's bank; its tapes are S4's layout);
* **`front fam : FrontPh (bridgeT fam (X fam))`** — the front phase ON S4'S LAYOUT: its `Phase` from `fpEntry`, its
  exit meeting `FrontOut` with S4's register lengths at its `W` (`ptCount·vmax < 2^W`), its cost within
  `s5Bound Cf Df`. It is the composition of the halves `S5ThrB2`, `S5CoreB2` at **`layOf Y E`** (`LayExt`: S4's
  `t, wd, tN, tD, reg, Kc, Dc` with the halves' scratch sets; the core's `FrontOut` is then `Y`'s by `rfl`);
* **`o fam`, `ho fam`, `O fam : OutMachine`** — the output machine docked on S4's layout (output tape `o ≠ 0`);
* **`E₅`, `CD₅`, `c₅`** — the StageU witnesses in `FinalPassLeaf`'s order of choice;
* **`fits`** — S6: `FitsRes` at the three phases' explicit bounds.

Built here: `seedsPh` (BridgeT's `SeedsProg2` as `FpPhases.seeds` from the front's exit), `numDen` (its exit meets
`NumDenOut`: `denW` from `FrontOut.numW`), `phasesOf` (the three phases; `out` is `OutMachine.phase`), `phasesOf_fits`
(`fits_dock`), and **`finalPass_of`** (`fpPlan`).

Paper quantity of the main type: the final pass's leaf `FinalPassLeaf l` (the primitive's printed value within
`c₅·finalClasses`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Assembly
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Family

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Assembly
