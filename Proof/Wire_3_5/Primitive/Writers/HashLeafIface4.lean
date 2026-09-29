import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4
import Proof.Wire_3_5.Primitive.Writers.BudgetIface
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.WritersJoin

/-! # The HASH writer's leaf over the v4 data stage — the deliverable type

`HashLeafOf` with the v4 data stage (`ThrData.ThrStage4U l`: v3 plus `x3` extra
scratch tapes for W6's numbers machine) in place of v3:

* **`HashLeafOf4 l`**: from `ThrStage4U l`, the walk bank, the FILTER setup, `FiltPipeLe2` and `ThrNumsPoly l`, the
  HASH writer's leaf `WritersJoin.HashLeafJ2 l`. The construction proves it (`ShellH2`'s shell on `STx + x3` tapes; the family
  budgets and the class link of HashFam/HashClass, which read the data stage's `cost3`, `need` only).

Paper quantity of the main type: the HASH tape `hashTape` within the preprocessing class `2^{O(Ψ)}q^{O(1)}`
(P3:3108, 3112-3114; the auxiliary filter rows of P3:2220-2226). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashLeaf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split

/-- **The HASH writer's leaf over the v4 data stage**. -/
abbrev HashLeafOf4 (l : Literals) : Type :=
  ThrData.ThrStage4U l → (W : PrimT.WalkBank.WalkBankProducer) → FiltSetup.FiltSetupSpec5 W →
    BudgetIface.FiltPipeLe2 → BudgetIface.ThrNumsPoly l → WritersJoin.HashLeafJ2 l

end NearCubicWires.WireExponent3_5.PrimAsm.HashLeaf
