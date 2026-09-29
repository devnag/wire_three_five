import Proof.PCP.PCPPQueryClauseMatrix

/-! Final explicit clause lookup: parse the actual list-count field, write
the constant two-literal result header, skip index preceding pairs and copy
the selected pair. Every entry cursor comes from the preceding matrix scan. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClauseLookup
open LocalBitMultitape RepairRepresentation PCPPQueryField RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerSlots : Fin 3→Fin 5 := ![0,1,4]
def printSlots : Fin 1→Fin 5 := fun _ => 2
def pairSlots (i : Fin 4) : Fin 5 := i.castAdd 1
def prefixBits := natWord 2
noncomputable def header := RecoveryFocus.machine headerSlots (PCPPQueryField.machine false)
noncomputable def print := RecoveryFocus.machine printSlots (HierarchyFixedWord.raw prefixBits)
noncomputable def prefixMachine := Composition.machine header print
noncomputable def pairs := RecoveryFocus.machine pairSlots PCPPQueryClauseRows.machine
noncomputable def machine := Composition.machine prefixMachine pairs
noncomputable def entry (source : List Bool) (pos : ℕ) (backing : List Bool) (index : ℕ) :=
  (⟨machine.start,![pos,0,0,1,0],![source,backing,[],UnaryTemplate.tape index,[]]⟩ :
    Configuration 5 ((4+(prefixBits.length+1))+(Fintype.card (RepeatMachine.Control 8)+8)))
def budget (count : ℕ) (rows : List (ℕ×ℕ)) (a b : ℕ) :=
  fieldCost count+prefixBits.length+PCPPQueryClauseRows.budget rows a b+2
def capacity (index : ℕ) : Fin 4→ℕ := fun i => if i=3 then index+2 else 0

end NearCubicWires.RepairOrdinary.PCPPQueryClauseLookup
