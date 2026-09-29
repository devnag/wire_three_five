import Proof.Amplification.RecoveryPCPFormulaResumeState

/-! Literal source fields retained by the checked hierarchy stream are
connected to the fixed cold original-formula constructor. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeHierarchy
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def port (k : Nat) (i : Fin 5) : Fin (HierarchyStreams.tapes source k) :=
  if i.val=0 then HierarchyStreams.old source k (HierarchyStreams.bitsR source k) else
  if i.val=1 then HierarchyStreams.old source k (HierarchyStreams.bitsQ source k) else
  if i.val=2 then HierarchyStreams.slots source k 29 else
  if i.val=3 then HierarchyStreams.slots source k 38 else HierarchyStreams.slots source k 46

theorem port_value (k : Nat) (i : Fin 5) : (port source k i).val=
    if i.val=0 then (HierarchyStreams.bitsR source k).val else
    if i.val=1 then (HierarchyStreams.bitsQ source k).val else
    if i.val=2 then HierarchyStreams.base source k+29 else
    if i.val=3 then HierarchyStreams.base source k+38 else HierarchyStreams.base source k+46 := by
  fin_cases i <;> rfl

theorem port_injective (k : Nat) : Function.Injective (port source k) := by
  have hr : (HierarchyStreams.bitsR source k).val<HierarchyStreams.base source k :=
    (HierarchyStreams.bitsR source k).isLt
  have hq : (HierarchyStreams.bitsQ source k).val<HierarchyStreams.base source k :=
    (HierarchyStreams.bitsQ source k).isLt
  have hn : (HierarchyStreams.bitsR source k).val≠(HierarchyStreams.bitsQ source k).val := by
    intro he
    have hd:=HierarchyStreams.dimension_injective source k (Fin.ext he)
    have hv:=congrArg Fin.val hd
    have hbits:=HierarchyStreams.bit_values source.degrees.proofLog source.degrees.queries
    rw [hbits.1,hbits.2] at hv
    omega
  intro i j he
  have hv:=congrArg Fin.val he
  have hi:=i.isLt
  have hj:=j.isLt
  apply Fin.ext
  rw [port_value,port_value] at hv
  split_ifs at hv <;> omega


end
end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeHierarchy
