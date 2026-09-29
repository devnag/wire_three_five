import Proof.PCP.PCPPNativeCounters

/-! Literal original hierarchy fields dock directly into the paid metadata
and mass scans. All counter workspace is physically fresh. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchyCounters
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def base (k : ℕ) := PCPPNativeHierarchy.tapes source k
def sourcePorts (k : ℕ) : Fin 6 → Fin (base source k) :=
  ![PCPPNativeHierarchy.loadSlots source k 2,
    PCPPNativeHierarchy.hierarchySlots source k (HierarchyStreams.old source k (HierarchyStreams.bitsQ source k)),
    PCPPNativeHierarchy.hierarchySlots source k (HierarchyStreams.slots source k 46),
    PCPPNativeHierarchy.hierarchySlots source k (HierarchyStreams.slots source k 29),
    PCPPNativeHierarchy.hierarchySlots source k (HierarchyStreams.slots source k 25),
    PCPPNativeHierarchy.hierarchySlots source k (HierarchyStreams.slots source k 38)]
def sourceValues (k : ℕ) : Fin 6 → ℕ :=
  ![2,4+(HierarchyStreams.bitsQ source k).val,4+HierarchyStreams.base source k+46,
    4+HierarchyStreams.base source k+29,4+HierarchyStreams.base source k+25,4+HierarchyStreams.base source k+38]
theorem source_values (k : ℕ) (i : Fin 6) : (sourcePorts source k i).val=sourceValues source k i := by
  have hp : 0<(HierarchyStreams.bitsQ source k).val := HierarchyStreams.slot_positive source k _
  fin_cases i <;>
    simp [sourcePorts,sourceValues,PCPPNativeHierarchy.hierarchySlots,PCPPNativeHierarchy.loadSlots,
      HierarchyStreams.old,HierarchyStreams.slots,Nat.ne_of_gt hp,Nat.add_assoc]



end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchyCounters
