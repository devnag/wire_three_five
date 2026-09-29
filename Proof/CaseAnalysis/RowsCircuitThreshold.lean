import Proof.CaseAnalysis.RowsCircuitPorts

/-! Cold original circuit input reaches the existing complete threshold
top consumer. The actual serialized-bottom template is positioned once;
no arity word, initialized bank or top field is an additional input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdThreshold
open LocalBitMultitape RecoveryRootRound RadixSemantics CanonicalWitnessCodec
open CloseoutRowsCircuit CloseoutRowsGatePairHeads
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool):=Function.update (CloseoutRowsCircuitColdEntry.heads out) 624 1
noncomputable def positioned:=Composition.machine (CloseoutRowsCircuitColdEntry.machine true)
  (CompetitorCountTable.moveMachine (624 : Fin 1703))
noncomputable def machine:=Composition.machine positioned CloseoutRowsCircuitThresholdTop.machine
def budget (cap : ℕ) (bits : List Bool):=CloseoutRowsCircuitColdEntry.budget cap bits+3+
  CloseoutRowsCircuitThresholdTop.budget cap (CloseoutRowsCircuitHeader.codeWord bits 3)

theorem gate_heads (out : List Bool) (i : Fin 1049) :
    heads out (gateSlots i)=CloseoutRowsGateMeasured.heads i:=by
  rw [CloseoutRowsGateBank.heads_eq]
  by_cases hi:i.val=1035
  · rw [if_pos hi]
    have he:gateSlots i=624:=by apply Fin.ext;rw [gate_val,if_pos hi];rfl
    rw [he];exact Function.update_self _ _ _
  · rw [if_neg hi]
    have he:gateSlots i≠624:=by
      intro h;have hv:=congrArg (fun k : Fin 1703=>k.val) h
      rw [gate_val,if_neg hi] at hv
      change 639+i.val=624 at hv;omega
    rw [heads,Function.update_of_ne he]
    unfold CloseoutRowsCircuitColdEntry.heads CloseoutRowsCircuit.heads
    have hv:(gateSlots i).val=639+i.val:=by rw [gate_val,if_neg hi]
    split_ifs <;> first | rfl | (rename_i h;have h':=congrArg (fun k : Fin 1703=>k.val) h;rw [hv] at h';change 639+i.val=1688 at h';omega) | omega

theorem external_heads (out : List Bool) (i : Fin 7) :
    heads out (CloseoutRowsCircuitThresholdTop.external i)=0:=by
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdThreshold
