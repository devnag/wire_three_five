import Proof.Wire_3_5.Primitive.Writers.C3WSizes

/-! # C3 request writer, part 20: the call's steps in one size `S`

`Gm a Dv S`: the writer's steps at a call whose base sizes (the request word, `n`, the four numbers, the writers'
budgets, the fill polynomial) are at most `S` (**`call_cost_le`**), polynomially bounded in `S` (`pb_Gm`).

Paper quantity: the request writer's steps within the preprocessing class (P3:3108). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch NearCubicWires.LocalBitMultitape
open NearCubicWires.PolynomialSchedule NearCubicWires.SourceInterfaces NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.DecBound
open NearCubicWires.WireExponent3_5.PrimAsm.C3Asm NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
open NearCubicWires.WireExponent3_5.PrimAsm.C3Field
open NearCubicWires.RepairOrdinary (frame frame_length)
open NearCubicWires.RepairRepresentation (natWord)

/-- C3a′'s steps as a polynomial in the size `S`. -/
def PnA (a : RepairRepresentation.DecompositionAlgorithm) (S : ℕ) : ℕ :=
  10246 * ((20 * S + 12) * (20 * S + 12) * ((SourceEnvelope.coefficient a + 1) * (S + 2) ^ (2 * degD a + 2) + 1)) ^ 4 +
    Kd a * (S + 2) ^ (2 * degD a + 3)

/-- **The call's steps as a polynomial in the size `S`.** -/
noncomputable def Gm (a : RepairRepresentation.DecompositionAlgorithm) (Dv S : ℕ) : ℕ :=
  2 * (cR Dv * (S + PnA a S + 1) ^ dR Dv) + 2

theorem pb_Gm (a : RepairRepresentation.DecompositionAlgorithm) (Dv : ℕ) : PolynomiallyBounded (fun S => Gm a Dv S) := by
  simp only [Gm, PnA]
  iterate 60 (all_goals (try (first
    | with_reducible exact polynomiallyBounded_id
    | with_reducible exact polynomiallyBounded_constant _
    | with_reducible apply polynomiallyBounded_add
    | with_reducible apply polynomiallyBounded_mul
    | with_reducible apply polynomiallyBounded_pow)))

noncomputable def cGm (a : RepairRepresentation.DecompositionAlgorithm) (Dv : ℕ) : ℕ :=
  Classical.choose (pb_Gm a Dv)
noncomputable def dGm (a : RepairRepresentation.DecompositionAlgorithm) (Dv : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (pb_Gm a Dv))

theorem Gm_le (a : RepairRepresentation.DecompositionAlgorithm) (Dv S : ℕ) : Gm a Dv S ≤ cGm a Dv * (S + 1) ^ dGm a Dv :=
  (Classical.choose_spec (Classical.choose_spec (pb_Gm a Dv))).2 S

section Call
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
