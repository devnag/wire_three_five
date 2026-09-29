import Proof.PCP.PCPPQueryCapacity

/-! Allocated index buffers for arbitrary repeated SAME-cache queries.
Only the existing index tape is padded. All operations use the same machines. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryIndexPadding
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true



def clauseData (source : List Bool) (arity index C : ℕ) (result : List Bool) (j : Fin 19) :=
  if j=14 then ZeroPadding.pad C (UnaryTemplate.tape index) else PCPPQueryClauseReuse.data source arity index C result j


end NearCubicWires.RepairOrdinary.PCPPQueryIndexPadding
