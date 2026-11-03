import Gadget.CheckedSize

set_option autoImplicit false

namespace NearCubicGates.Close.Gadget

open NearCubicWires NearCubicGates.PublishedSources.PCPP NearCubicWires.SourceInterfaces NearCubicWires.RepairSource
open NearCubicWires.RepairOrdinary NearCubicWires.Bindings.CLW20Lemma311

variable {n : ℕ}

/-! ## One-node builders -/

@[simp] theorem addInput_out (b0 : BooleanDAGBuilder n) (i : Fin n) : (addInput b0 i).out = b0.nodes.length := rfl
@[simp] theorem addConst_out (b0 : BooleanDAGBuilder n) (v : Bool) : (addConst b0 v).out = b0.nodes.length := rfl
@[simp] theorem addNot_out (b0 : BooleanDAGBuilder n) {r : ℕ} {f : BitInput n → Bool} (hr : Computes b0 r f)
    (hlt : r < b0.nodes.length) : (addNot b0 hr hlt).out = b0.nodes.length := rfl
@[simp] theorem addAnd_out (b0 : BooleanDAGBuilder n) {r s : ℕ} {f g : BitInput n → Bool} (hr : Computes b0 r f)
    (hs : Computes b0 s g) (hlt : r < b0.nodes.length ∧ s < b0.nodes.length) :
    (addAnd b0 hr hs hlt).out = b0.nodes.length := rfl
@[simp] theorem addOr_out (b0 : BooleanDAGBuilder n) {r s : ℕ} {f g : BitInput n → Bool} (hr : Computes b0 r f)
    (hs : Computes b0 s g) (hlt : r < b0.nodes.length ∧ s < b0.nodes.length) :
    (addOr b0 hr hs hlt).out = b0.nodes.length := rfl

/-! ## Parity chains -/

/-! ## Checks -/

section Checks

end Checks

end NearCubicGates.Close.Gadget
