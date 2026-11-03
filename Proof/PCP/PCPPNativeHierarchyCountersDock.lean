import Proof.PCP.PCPPNativeHierarchyCountersLayout

/-! The original hierarchy's retained physical fields satisfy the exact
entry of the metadata and measured-counter program. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchyCounters
open LocalBitMultitape SourceInterfaces RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem counter_input (oracle : List Bool) (p : RawProjectionPCP) (R Q : ℕ) (i : Fin 75) :
    PCPPNativeColdCounters.input oracle p R Q i=
      if i=0 then oracle else if i=40 then frame Q.bits
      else if i=47 then VerifierDecoding.CompareMachine.word (Codec.clauses p).length
      else if i=52 then PCPPNativeMetadataMass.queryBytes p R Q
      else if i=54 then VerifierDecoding.CompareMachine.word (R*Q)
      else if i=57 then DedupBytes.fields p else [] := by
  fin_cases i <;> rfl
theorem counter_heads (i : Fin 75) :
    PCPPNativeColdCounters.heads i=if i=47 then 1 else if i=54 then 1 else 0 := by
  fin_cases i <;> rfl


end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchyCounters
