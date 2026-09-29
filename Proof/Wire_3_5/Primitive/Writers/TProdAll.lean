import Proof.Wire_3_5.Primitive.Writers.TProdA
import Proof.Wire_3_5.Primitive.Writers.TProdB
import Proof.Wire_3_5.Primitive.Writers.KWT2
import Proof.Wire_3_5.Primitive.Writers.HashSetH1

/-! # T-a/b/c producers at the HASH setup's layout (c4's finish inputs)

The three stage contracts at every layout of the HASH setup `M0H` (the bank `3 + XH`, the regions `oD`, `oK`, `oQ`,
the tapes `g0, tNt, tLt, tDt`, `kInH`, `srcQ`), exactly `c4Leaf_of_obl3`'s `hDR`, `hKW`, `hQC`: **`tA`**
(`dataRerun_ok`), **`tB`** (`kwDock_ok`), **`tC`** (`qCopy2_ok`, T-c at `qCost2`).

Paper quantity of the main type: the setup's counts, kept words and `1^{Q'}` on the setup's tapes (P3:3011-3016). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.TProd
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm.HashSetH

/-- **T-a at every layout.** -/
theorem tA (Wk : PrimT.C4KW.KWW) : ∀ {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ}
    (L : PrimT.C4Set.Lay) (S4 : PrimAsm.ThrData.ThrDataStage4 alg Dexp capT) (T : PrimThrW.PortsE.TopFrontPort3 alg)
    (N : PrimThrW.Nums4.NumsPort4 alg Dexp) (fT : ℕ),
    PrimT.C4KW.DataRerun S4 (XH L S4 T N Wk fT) (oD L S4) (hDD L S4 T N Wk fT) (g0 L S4 T N Wk fT)
      (tNt L S4 T N Wk fT) (tLt L S4 T N Wk fT) (tDt L S4 T N Wk fT) :=
  fun L S4 T N fT => dataRerun_ok S4 _ _ _ _ _ _ _

/-- **T-b at every layout.** -/
theorem tB (Wk : PrimT.C4KW.KWW) : ∀ {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ}
    (L : PrimT.C4Set.Lay) (S4 : PrimAsm.ThrData.ThrDataStage4 alg Dexp capT) (T : PrimThrW.PortsE.TopFrontPort3 alg)
    (N : PrimThrW.Nums4.NumsPort4 alg Dexp) (fT : ℕ),
    PrimT.C4KW.KwDock Wk (XH L S4 T N Wk fT) (oK L S4 T N) (hKK L S4 T N Wk fT) (kInH L S4 T N Wk fT) :=
  fun L S4 T N fT => kwDock_ok Wk _ _ _ _

/-- **T-c at every layout** (at `qCost2`). -/
theorem tC (Wk : PrimT.C4KW.KWW) : ∀ {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ}
    (L : PrimT.C4Set.Lay) (S4 : PrimAsm.ThrData.ThrDataStage4 alg Dexp capT) (T : PrimThrW.PortsE.TopFrontPort3 alg)
    (N : PrimThrW.Nums4.NumsPort4 alg Dexp) (fT : ℕ),
    PrimT.C4KW.QCopy2 (XH L S4 T N Wk fT) (oQ L S4 T N Wk) (hQQ L S4 T N Wk fT) (srcQ L S4 T N Wk fT) :=
  fun L S4 T N fT => PrimT.C4KW.qCopy2_ok _ _ _ _

end NearCubicWires.WireExponent3_5.PrimAsm.TProd
