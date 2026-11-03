import Proof.Rows.CircuitFlagBody

/-! The physical flag callback consumes exactly Production's native circuit
codec. All count and individual-gate width bounds follow from its byte cap. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 250000
namespace PCJ45bee56da9f34d5a_NativeCircuitCodec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.CompilerSemantics
open PCJ45bee56da9f34d5a_NativeCircuitFlags (payload flags)
open PCJ45bee56da9f34d5a_NativeGateLoop (word stream)
open PCJ45bee56da9f34d5a_FramedGateBank (strict)
noncomputable section

def thrGates {q : Nat} (c : NormalizedThresholdThresholdCircuit q) :=
 List.ofFn (fun i=> (c.bottom (retainedTopIndex c i)).gate)
def thrTop {q : Nat} (c : NormalizedThresholdThresholdCircuit q) :=thresholdWord (nonStrictAsStrict (retainedTopGate c))

theorem native_gate {q : Nat} (g : SupportedNormalizedGate q) :
 frame (PCJd4d1d9d7d1fa4313_Production.bottomWord g)=word g.gate :=by
 simp only [PCJd4d1d9d7d1fa4313_Production.bottomWord,thresholdWord,nonStrictAsStrict,word,
  PoolEntryLoad.word,strict,exactWord,List.append_assoc]

theorem thrWord_eq {q : Nat} (c : NormalizedThresholdThresholdCircuit q) :
 PCJd4d1d9d7d1fa4313_Production.thrWord c=payload (thrGates c) (thrTop c) :=by
 simp only [PCJd4d1d9d7d1fa4313_Production.thrWord,payload,thrGates,thrTop,List.length_ofFn,stream]
 have hm : (List.ofFn (fun i=>c.bottom (retainedTopIndex c i))).map (fun g=>g.gate)=
   List.ofFn (fun i=>(c.bottom (retainedTopIndex c i)).gate):=by rw [List.map_ofFn];rfl
 rw [←hm,List.flatMap_map]
 congr 1
 apply List.flatMap_congr
 intro g _
 exact native_gate g

end
end PCJ45bee56da9f34d5a_NativeCircuitCodec
