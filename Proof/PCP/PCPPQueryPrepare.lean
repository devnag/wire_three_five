import Proof.PCP.PCPPQueryPrepareCopy

/-! The literal query input produces both unary value drivers before the
source call. Their values are read from the retained query-index cursor and
the separately copied arity field of the same PCPP request. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryPrepare
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word (arity : ℕ) (code : List Bool) := natWord arity++code
def budget (arity index : ℕ) (code : List Bool) :=
  PCPPQueryPrepareCopy.budget (word arity code) (natWord index)+
    PCPPQueryNatural.budget index+PCPPQueryNatural.budget arity+2

end NearCubicWires.RepairOrdinary.PCPPQueryPrepare
