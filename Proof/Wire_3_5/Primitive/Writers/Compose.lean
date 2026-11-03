import Lean
import Proof.Wire_3_5.Primitive.Writers.Plan
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.ComposeBase


noncomputable section
set_option maxRecDepth 4096


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

/-- **The budget at every call**, for a coefficient rule `cg`. -/
def EnvFor (cg : ℕ → ℕ → ℕ) : Prop :=
  ∀ (l : Literals) (F : GateFree l) (E₄ E₅ : Envelope) (c₄ c₅ : ℕ), ClassLE E₄ F.E → ClassLE E₅ F.E →
    ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), cg c₄ c₅ ≤ coef →
      ∀ r : {req : PrimRequest // (callInputs l F kclk coef A a ha).Call req},
        glueK * (r.1.word.length +
          c₄ * seedClasses E₄ r.1.n (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
            (((gate0 l F).budget kclk coef A a ha).psiOf r.1.n) +
          c₅ * finalClasses E₅ r.1.n (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
            (((gate0 l F).budget kclk coef A a ha).psiOf r.1.n) + 1) ≤
        ((gate0 l F).budget kclk coef A a ha).callBudget r.1.n

/-- A coefficient rule with its budget inequality. -/
def EnvPack : Type := Σ' cg : ℕ → ℕ → ℕ, EnvFor cg

/-- **PA.compose**: `ComposeLeaf` for every literal, from the glue and the budget. -/
noncomputable def composeLeaf (glue : Glue) (env : EnvPack) : ∀ l, ComposeLeaf l := fun l =>
  ⟨zeroEnv, env.1, fun F E₄ E₅ c₄ c₅ h4 h5 _ kclk coef A a ha hc s4 s5 =>
    glue (fun r : {req : PrimRequest // (callInputs l F kclk coef A a ha).Call req} => r.1.word) (fun r => seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1)
      (fun r => ratWord (SeedFix.greedyValue (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1))
      (fun r => c₄ * seedClasses E₄ r.1.n (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
        (((gate0 l F).budget kclk coef A a ha).psiOf r.1.n))
      (fun r => c₅ * finalClasses E₅ r.1.n (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
        (((gate0 l F).budget kclk coef A a ha).psiOf r.1.n))
      (fun r => ((gate0 l F).budget kclk coef A a ha).callBudget r.1.n) s4 s5
      (env.2 l F E₄ E₅ c₄ c₅ h4 h5 kclk coef A a ha hc)⟩

end NearCubicWires.WireExponent3_5.PrimAsm.Compose

end
