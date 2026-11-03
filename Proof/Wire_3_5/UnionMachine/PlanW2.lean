import Lean
import Proof.Wire_3_5.UnionMachine.PlanW
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Assembly.Free
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.UnionEventual
import Proof.Wire_3_5.UnionMachine.Plan
import Proof.Wire_3_5.UnionMachine.PlanW2Base


noncomputable section
set_option maxRecDepth 4096


/-! # C6: leaf U's enclosing application with the union's own exponents

The plan of `WireExponent3_5UnionMachinePlanW` with the union's clock and source-work exponents: the numeral
clock `kclk` (paper v2, order of the constants, item (1): `C_clk = kclk + 2 > d_0 + 2`), `a = kclk + 1`, and a margin
`e` kept as an index of the front residual. The union's own preprocessing includes v8's cold decoders, whose
polynomial degree is an absolute constant (base `CloseoutWitness.Oracle.budget_polynomial`: `(N+2)^25`; the atom
decoders' capacity `(ℓ+2)^26`), below the clock.

Main statement: **`union_planW2 c1 dec fronts count acc facts : ∀ l, UnionLeafF l`** with
`fronts : ∀ l, Σ e, ∀ F, GateFreeOK l F → FrontsFWE e l F` (the margin per literal set: a stage whose degree depends
on `l`'s source or PCPP constants beyond `gateDver` picks a larger `e` at that `l`) and the setup residuals at every
margin. Paper quantity: `UnionLeafF l`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.PlanW2
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.ExtDecompositionBatch NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.Bindings.CLW20Theorem113
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW Filter
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)

/-! ## The union's exponents -/

section Consts
variable (l : Literals)

/-- The clock exponent at margin `e`: `T(N) = N^{kclk+2}`, the numeral `kclk` fixed first (paper v2, order of the
constants, item (1)); the margin `e` is kept as an index of the front residual and does not move the clock. -/
abbrev kE (_l : Literals) (_e : ℕ) : ℕ := kclk

/-- The source-work exponent at margin `e`: `a = kclk + 1`. -/
abbrev aE (l : Literals) (e : ℕ) : ℕ := kE l e + 1

theorem haE (e : ℕ) : aE l e ≤ kE l e + 1 := le_rfl

end Consts

/-! ## Layer A at margin `e` -/

section Leaf
variable (l : Literals)

/-- The inputs of the union at the gate: clock `kE l e`, source work `A·(N+1)^{aE l e}`, coefficient `coef`. -/
noncomputable abbrev IUE (F : GateFree l) (e coef A : ℕ) := (gate0 l F).inputs (kE l e) coef A (aE l e) (haE l e)

/-- The pinned setup at a language of the clock. -/
noncomputable abbrev SUE (F : GateFree l) (e coef A : ℕ) (L : Language) (hL : InNTIME (fun n => n ^ (kE l e + 2)) L) :
    UnionSetup (IUE l F e coef A) :=
  setupF l F (kE l e) coef A (aE l e) (haE l e) L hL

/-- **Residual (setup facts)** at every free choice, coefficient, source work and language. -/
def SetupFactsFE (e : ℕ) : Prop :=
  ∀ (F : GateFree l) (coef A : ℕ) (L : Language) (hL : InNTIME (fun n => n ^ (kE l e + 2)) L),
    SetupFacts (SUE l F e coef A L hL) L

/-- **Residual (an accepting guess calls)** at every free choice, coefficient, source work, language and primitive. -/
def AcceptsCallFE (e : ℕ) : Prop :=
  ∀ (F : GateFree l) (coef A : ℕ) (L : Language) (hL : InNTIME (fun n => n ^ (kE l e + 2)) L)
    (P : FusedPrimitive (IUE l F e coef A)), AcceptsCall (SUE l F e coef A L hL) P

/-- The coefficient-`0` branch: the machine rejects everything; completeness is vacuous (`Free.coef_pos`). -/
noncomputable def leafAtZeroE (e : ℕ) (F : GateFree l) (coef A : ℕ) (hA : 3 ≤ A) (hc : ¬ 1 ≤ coef)
    (acc : AcceptsCallFE l e) :
    UnionLeafAt (IUE l F e coef A) (fun L hL => SUE l F e coef A L hL) where
  build := fun _ _ => rejectAll
  soundness := fun _ _ _ => ⟨0, fun n _ x h => absurd h (rejectAll_rejects n x)⟩
  time := fun _ _ N _ => by
    rw [rejectAll_runtime]
    have h1 : 1 ≤ (N + 1) ^ aE l e := Nat.one_le_pow _ _ (Nat.succ_pos N)
    have : 3 ≤ A * (N + 1) ^ aE l e := le_trans hA (Nat.le_mul_of_pos_right _ h1)
    exact le_trans this (Nat.le_add_right _ _)
  complete := fun P L hL => ⟨0, fun N _ z g hg => by
    obtain ⟨req, hreq⟩ := acc F coef A L hL P N z g hg
    exact absurd (Free.coef_pos l F P req hreq) hc⟩

end Leaf

/-! ## Layer B at margin `e` -/

section Front
end Front

section LeafB
variable (l : Literals)

/-- The eventual facts the worker's time reads, at one coefficient, source work and language: the count,
`GateFreeOK`'s absorption at the per-call factor `Kf·(3+Kd)`, and C1's one call. -/
theorem eventual_timeE (e : ℕ) (F : GateFree l) (hF : GateFreeOK l F) (coef A : ℕ) (hc : 1 ≤ coef) (L : Language)
    (hL : InNTIME (fun n => n ^ (kE l e + 2)) L) {d₁ : ℕ} (c1 : C1At d₁) (Kf Kd : ℕ) (count : CallCountF l) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      (∀ (z : BitInput N) (g : UnionGuess (SUE l F e coef A L hL) z),
        UnionGuards (SUE l F e coef A L hL) z g →
          ∀ tr : List ℕ, (g.checkData tr).schedule.length ≤
            ((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e)).q N ^ unionCallDeg l) ∧
      Kf * (3 + Kd) * (((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e)).q N + 1) ^
        (unionCallDeg l + (callDegMargin - 1)) ≤ ((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e)).q N ^ F.E.callDeg ∧
      c1.budgetAt ((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e))
        (((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e)).q N) ≤
          ((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e)).callBudget
            (((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e)).q N) := by
  have hq := tendsto_q ((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e))
  have e1 := count coef A (aE l e) (haE l e) F L hL
  have e2 := hq.eventually (calls_absorb l F hF (Kf * (3 + Kd)))
  have e3 := hq.eventually (Free.selection_le_callBudget l F (kE l e) coef A (aE l e) (haE l e) hc c1.E₁ c1.c₁)
  exact eventually_atTop.1 (e1.and (e2.and e3))

end LeafB

end NearCubicWires.WireExponent3_5.UnionMachine.PlanW2

end
