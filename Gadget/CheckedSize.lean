import Gadget.Checked

/-!
# The size of the checked circuit — the near-cubic-gates paper ("a polynomial-size list of three-literal clauses")

Exact node counts of the circuit-kit builders, and `(checkedCircuit E D).m ≤ D.m + L(8 + 5q) + q + L` with
`q = D.n`, `L = E.length q`: the checks add one parity chain (at most `q` XORs of five nodes) and five more nodes per
code bit, and the padding adds at most the arity.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Gadget

open NearCubicWires NearCubicGates.PublishedSources.PCPP NearCubicWires.SourceInterfaces NearCubicWires.RepairSource
open NearCubicWires.RepairOrdinary NearCubicWires.Bindings.CLW20Lemma311

variable {n : ℕ}

@[simp] theorem Ext.trans_length {b0 : BooleanDAGBuilder n} (e : Ext b0) (e' : Ext e.b) :
    (e.trans e').b.nodes.length = e'.b.nodes.length := rfl

section

end

end NearCubicGates.Close.Gadget
