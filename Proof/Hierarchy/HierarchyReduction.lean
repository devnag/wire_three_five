import Proof.Hierarchy.HierarchyReductionPadding

/-! Complete ordinary padding producer from the retained framed source x.
All arithmetic, unary allocation, slice rounding, constant printing, header
copying, zero padding, physical returns, and head restoration are paid. -/
namespace NearCubicWires.RepairOrdinary.HierarchyReduction
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (k C Cpad : ℕ) (code : List Bool) := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (boundProgram k C)
    (allocationProgram k C Cpad code)) (sliceProgram k)) (codeProgram k code)) (headerProgram k)
def budget (k C Cpad : ℕ) (code x : List Bool) := HierarchyFromInput.budget (k+2) C x+1+
  HierarchyAllocation.budget (coefficient Cpad) (constant C Cpad code) x+1+
  (2*length k C Cpad code x+4)+1+codeCost code+1+(2*length k C Cpad code x+4)

end NearCubicWires.RepairOrdinary.HierarchyReduction
