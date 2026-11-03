import Proof.Wire_3_5.FinalPass.MajMain
import Proof.Wire_3_5.Primitive.Writers.PlanBase

/-! # The final pass: the plan by phases (P3:3046-3048, 3170-3181)

"At each of `2^{n−k}` columns, evaluate the reported lookup at these `Q` pairs [...] The final pass costs
`2^{n−k/4}n^{C_D}`" (P3:3046-3048, 3170-3181). The final pass at one call family is ONE machine from `req.word ++ seedWord`
to `ratWord (greedyValue)`, all heads back at `0`, within `c₅·finalClasses E₅ (n, kOf n, psiOf n)`
(`FinalPassAt`). The join audit fixed its layout: TM-level phases in sequence, because the seed's filter table
(stage 6) and the walk bank are `Step`s, not word programs:

* `front`: the data stage (`Data.data_step` / `ThrData`), the numbers, the samples;
* `seeds`: the loop over the seeds (per seed: the walk bank, stage 6's table, the point loop over centers × samples);
* `out`: the reduced rational written as `ratWord`, every head back at `0`.

Each phase is one machine for every request of the family, stated as a `Step` FROM THE PREVIOUS PHASE'S EXIT BANK
(`Phase … H₀ A₀`): the seams are the typing. `FpPhases` bundles the three phases with the output and head facts; the plan takes
the EXPLICIT cost residual `fits` (the phases' costs against `c₅·finalClasses`); `FpPhases.blocks` composes them
(base `Step.seq`, one bridge step each) into `Top.FinalPassBlocks`, and **`fpPlan`** gives `(l : Literals) →
FinalPassLeaf l`.
Paper quantity of the main type: the primitive's printed value `ratWord (greedyValue I alg req)`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- **One phase**: one machine for every request, its per-request cost, and its `Step` from the entry bank
`(H₀ r, A₀ r)` to its exit bank `(H r, A r)`. -/
structure Phase (Req : Type) (t : ℕ) (H₀ : Req → Fin t → ℕ) (A₀ : Req → Fin t → List Bool) where
  s : ℕ
  M : Machine t s
  cost : Req → ℕ
  H : Req → Fin t → ℕ
  A : Req → Fin t → List Bool
  run : ∀ r, Step M (cost r) (H₀ r) (A₀ r) (H r) (A r)

/-- Two phases in sequence: base's `Step.seq` (one paid bridge step). -/
def Phase.seq {Req : Type} {t : ℕ} {H₀ : Req → Fin t → ℕ} {A₀ : Req → Fin t → List Bool}
    (p : Phase Req t H₀ A₀) (q : Phase Req t p.H p.A) : Phase Req t H₀ A₀ :=
  ⟨p.s + q.s, Composition.machine p.M q.M, fun r => p.cost r + 1 + q.cost r, q.H, q.A,
    fun r => Step.seq (p.run r) (q.run r)⟩

section Family

end Family

end NearCubicWires.WireExponent3_5.FinalPass.PlanFP
