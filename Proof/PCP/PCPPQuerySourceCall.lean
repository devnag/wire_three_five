import Proof.PCP.PCPPQueryPrepare

/-! One call to the same ordinary PCPP source constructor, on its isolated
literal input and a fresh source workspace. The paid source reset produces
the explicit object at head zero and retains the two physical query drivers. -/
namespace NearCubicWires.RepairOrdinary.PCPPQuerySourceCall
open LocalBitMultitape RepairRepresentation ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : PointwisePCPPAlgorithm)

def sourceBudget (r : PCPPRequest a.minimumArity) := a.coefficient*(r.circuit.size+r.arity+1)^a.degree
def budget (r : PCPPRequest a.minimumArity) (index : ℕ) :=
  PCPPQueryPrepare.budget r.arity index (encodeBooleanCircuit r.circuit).bits+2*sourceBudget a r+3

end NearCubicWires.RepairOrdinary.PCPPQuerySourceCall
