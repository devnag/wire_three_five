import Proof.PCP.PCPPQueryClauseLookup

/-! Complete clause reader on one explicit source object and the two
physically produced arity/index drivers. Metadata, matrix rows, list header,
index scan and result serialization are all executed by this fixed machine. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClause
open LocalBitMultitape RepairRepresentation PCPPQueryField RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5→Fin 16 := ![0,11,15,14,12]
noncomputable def lookup := RecoveryFocus.machine slots PCPPQueryClauseLookup.machine
noncomputable def machine := Composition.machine PCPPQueryClauseMatrix.machine lookup
noncomputable def entry (source : List Bool) (arity index : ℕ) :=
  Composition.leftConfig ((4+(PCPPQueryClauseLookup.prefixBits.length+1))+(Fintype.card (RepeatMachine.Control 8)+8))
    (Composition.leftConfig (Fintype.card (RepeatMachine.Control 5)) (PCPPQueryClauseHeader.entry source arity index))
def budget (a b c arity count : ℕ) (rows : List (ℕ×ℕ)) (left right : ℕ) :=
  PCPPQueryClauseMatrix.budget a b c arity+1+PCPPQueryClauseLookup.budget count rows left right

end NearCubicWires.RepairOrdinary.PCPPQueryClause
