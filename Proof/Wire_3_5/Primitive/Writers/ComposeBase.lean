import Proof.Wire_3_5.Primitive.Writers.PlanBase

/-! # PA.compose: leaf P's per-call program from its two machines (plan module)

`prim:runtime` (P3:3105-3115): the primitive's per-call program is seed fixing followed by the final pass, "the running
time is the sum" of their classes. The residual `ComposeLeaf` asks, for the gate's free constants and
the two machines as hypotheses (`SeedFixAt`: `req.word ↦ seedWord` within `c₄·seedClasses E₄`; `FinalPassAt`:
`req.word ++ seedWord ↦ ratWord (greedyValue)` within `c₅·finalClasses E₅`), for ONE ordinary word function
`req.word ↦ ratWord (greedyValue)` within the gate's per-call budget `callBudget`.

This module is the enclosing term with its two ingredients as explicit residuals:
- `Glue`: the machine composition — run the first rewound word function, frame `w ++ s`, run the second — within
  `glueK·(|w| + b₄ + b₅ + 1)`;
- `EnvPack`: a coefficient rule `cg` and the budget inequality at every call, `glueK·(|req.word| + c₄·seedClasses E₄ +
  c₅·finalClasses E₅ + 1) ≤ callBudget` whenever `cg c₄ c₅ ≤ coef` (the classes of `E₄, E₅` are below those of `F.E`).

Paper quantities of the main types: `callBudget`, `seedClasses`, `finalClasses` (`EnvFor`); the composed word function
(`Glue`); `ComposeLeaf` (`composeLeaf`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Compose
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- The glue's constant: the composed run's overhead per input symbol and per step of the two machines. -/
def glueK : ℕ := 1000

/-- **The glue**: two rewound word functions `w ↦ s` (within `b₄`) and `w ++ s ↦ o` (within `b₅`) compose to one ordinary
word function `w ↦ o` within every budget `B ≥ glueK·(|w| + b₄ + b₅ + 1)`. -/
def Glue : Type 1 :=
  ∀ {Req : Type} (w s o : Req → List Bool) (b4 b5 B : Req → ℕ),
    RepairOrdinary.RewoundWordFunction Req w s b4 →
    RepairOrdinary.RewoundWordFunction Req (fun r => w r ++ s r) o b5 →
    (∀ r, glueK * ((w r).length + b4 r + b5 r + 1) ≤ B r) →
    RepairSource.OrdinaryWordFunction Req w o B

/-- The glue's own class floor: none (the glue's cost is charged to the classes of `F.E` through `cg`). -/
def zeroEnv : Envelope := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

end NearCubicWires.WireExponent3_5.PrimAsm.Compose
