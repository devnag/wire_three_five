import Proof.Wire_3_5.Selection.Order
import Proof.Wire_3_5.Selection.Objective
import Proof.Wire_3_5.Selection.Pool
import Proof.Wire_3_5.Selection.Joins

/-! # C1.1: the selection machine's math, assembled (P3:1337-1362)

Paper: `star:selection`, "it remains to compute each candidate's objective. Enumerate its `2^k` error rows. [...]
For each of the sixteen corner patterns, count pairs satisfying its four weak inequalities [...] Sum its exact count
with the rational population weights, over gates and rows. There are `2^k` candidate cosets [...] Select a minimum
objective" (P3:1339-1360).

The two consumer-facing theorems of the C1.1 plan (`Proof.Wire_3_5.Selection.MathPlan`), with every residual
discharged (R1 `Order.r1Fold`, R2 `Objective.r2Objective`, R3 `Pool.r3Pool`/`Pool.r3Bound`, R4–R6 and the key
transfer `Joins.r4JForm`/`r5OneDim`/`r6Levels`/`rKey`):
* **`selArgmin_eq_fold`**: the selected coset (paper quantity) is the coset counter's strict-`<` running minimum of
  the exact key `objKey` under the cross-multiplied compare `ratLt`;
* **`gateRows_eq_gateJoin`**: a gate's row counts (paper quantity) are `gateJoin`, the sorted `<`-joins of the
  written points' offset-binary keys, for any enumeration of the halves and any key width meeting `KeyBound`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine

/-- **The selected coset is the counter's running minimum of the exact key.** -/
theorem selArgmin_eq_fold (R : SelectionReq) (h : ParamsOk R) (hp : ∀ X ∈ R.pops, 0 ≤ X.2) :
    selArgmin R = codesOfIdx R.s R.r (argminIdx ratLt (fun N => objKey R h (codesOfIdx R.s R.r N)) (2 ^ R.k)) :=
  selArgmin_eq_fold_of Order.r1Fold Objective.r2Objective R h hp

/-- **A gate's row counts are the joins of its written points.** -/
theorem gateRows_eq_gateJoin (P : StarParams) (σ : P.Translation) (g : NormalizedThresholdGate P.n)
    (Ls : List (P.Errors × (P.SideL → Bool))) (Rs : List (P.Errors × (P.SideR → Bool)))
    (hLs : Enumerates Ls (fun _ => True)) (hRs : Enumerates Rs (fun _ => True)) (V : ℕ) (hV : KeyBound g V) :
    gateRows P σ g = gateJoin V g.threshold (Ls.map (ptLz P σ g)) (Rs.map (ptRz P σ g)) :=
  gateRows_eq_gateJoin_of Pool.r3Pool Pool.r3Bound Joins.r4JForm Joins.r5OneDim Joins.r6Levels Joins.rKey P σ g Ls Rs
    hLs hRs V hV

end NearCubicWires.WireExponent3_5.SelectionMachine.Math
