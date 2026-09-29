import Proof.PCP.PCPPRequestInput

/-! One call to the faithful PCPP constructor on the physically emitted
request, with an isolated blank source workspace. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestSource
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : PointwisePCPPAlgorithm)
def program := Rewind.program a.constructor.program
def tapes := PCPPRequestInput.tapes+(program a).tapeCount
def slots (j : Fin (program a).tapeCount) : Fin (tapes a) :=
  if j.val=0 then PCPPRequestInput.outputSlot.castAdd (program a).tapeCount
  else j.natAdd PCPPRequestInput.tapes
def outputSlot := slots a (program a).outputTape
noncomputable def first := TapeEmbedding.machine (program a).tapeCount PCPPRequestInput.machine
noncomputable def second := RecoveryFocus.machine (slots a) (program a).machine
noncomputable def machine := Composition.machine (first a) (second a)
def sourceBudget (request : PCPPRequest a.minimumArity) :=
  a.coefficient*(request.circuit.size+request.arity+1)^a.degree
def budget (request : PCPPRequest a.minimumArity) :=
  PCPPRequestInput.budget request.circuit+2*sourceBudget a request+3

end NearCubicWires.RepairOrdinary.PCPPRequestSource
