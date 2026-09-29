import Proof.Wire_3_5.Primitive.ThresholdWriter.TopFront
import Proof.Wire_3_5.Primitive.ThresholdWriter.EqRef

/-! # THR, reader lemmas for the front end's words and the selection (the three conditions on)

P3:2543-2551 (row:threshold-rows): selection `g` picks one child of each circuit's retained top; `L_g` stacks the
picked children's equations with base `1 + Σ_i ‖child_i‖`. The construction reads the front end's payloads (`TopFront.payOf`) and
builds the mod-`p` rows from them; these lemmas state the words' fields and the selection's digits exactly:

1. **Reader**: `payOf_eq` (a payload is `frame (natWord |supp| ++ natWord |children| ++ children.flatMap exactWord)`),
   `exactWord_eq` (a child's word is its weights' `intWord`s in local order, then its target's `intWord`), `intW_eq`
   (`EqW.intW = intWord`): the order `EqRef.eqRef` uses (`w_{i,k}` for `k < |supp_i|`, then `t_i`).
2. **Base**: `baseOf_eq`: `base = 1 + Σ_i childMagnitude (child_i)` over the SELECTED children only (one per circuit),
   `childMagnitude_eq`: `‖child‖ = Σ_k |w_k| + |t|`.
3. **Selection**: `sel_digit`: circuit `i`'s child index is `(g / Π_{j<i} |children_j|) mod |children_i|` (digit `0` least
   significant, `Enum.thrEqEquiv = finPiFinEquiv`), `sel_index` the converse sum; `children_count`: `|children_i|` is the
   `natWord` at the head of the payload's `exactListWord`.

Paper quantities: the selected children and the stack base of `L_g`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.EqRead
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.ThresholdAlignedEnvelope NearCubicWires.PacketsMeta.CutoffMath

/-! ## 1. The words -/

theorem exactWord_eq {k : ℕ} (g : ExactThresholdGate k) :
    exactWord g = (List.ofFn g.weight).flatMap intWord ++ intWord g.target := rfl

/-- **A payload's fields**: the retained top's support size, the children's count, the children's words in order. -/
theorem payOf_eq (alg : DecompositionAlgorithm) {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) :
    TopFront.payOf alg c = frame (natWord c.top.support.card ++
      (natWord (ThresholdRows.children alg c).length ++ (ThresholdRows.children alg c).flatMap exactWord)) := rfl

/-! ## 2. The base -/

theorem childMagnitude_eq {k : ℕ} (g : ExactThresholdGate k) :
    childMagnitude g = (∑ i, (g.weight i).natAbs) + g.target.natAbs := rfl

/-- **The base runs over the SELECTED children** (one per circuit). -/
theorem baseOf_eq (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : ThresholdRows.Selection a r) :
    EqRef.baseOf a r sel =
      (∑ i : Fin r.circuits.length, childMagnitude ((ThresholdRows.children a (r.circuits.get i)).get (sel i))) + 1 :=
  rfl

/-! ## 3. The selection's digits -/

section Sel
variable (P : NearCubicWires.WireExponent3_5.Shared.StarParams) {a' : ℕ}
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (alg : DecompositionAlgorithm)

/-- **Circuit `i`'s child index** in selection `g` (digit `0` least significant). -/
theorem sel_digit (g : ℕ) (hg : g < ∏ i : Fin (List.ofFn Cs).length,
      (ThresholdRows.children alg ((List.ofFn Cs).get i)).length) (i : Fin (List.ofFn Cs).length) :
    ((NearCubicWires.WireExponent3_5.PrimAsm.Enum.thrEqEquiv P Cs alg).symm ⟨g, hg⟩ i : ℕ) =
      (g / ∏ j : Fin i, (ThresholdRows.children alg ((List.ofFn Cs).get (Fin.castLE i.is_lt.le j))).length) %
        (ThresholdRows.children alg ((List.ofFn Cs).get i)).length := rfl

end Sel

end NearCubicWires.WireExponent3_5.PrimThrW.EqRead
