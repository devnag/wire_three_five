import Proof.SourceAssembly.SourceThresholdBounds

/- Paid rewind of the three completed logical streams, using the retained
quadratic C driver. Metadata and counted-loop driver remain outside the reset. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceThresholdReady
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def streams (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) : Fin 3→List Bool:=
  ![PCJ6e421fabe2aa4155_SourceThresholdLoop.outputs r.arity (PCJ6e421fabe2aa4155_SourceThresholdCache.bits a r ci hk)
      (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci) 0,
    PCJ6e421fabe2aa4155_SourceThresholdLoop.outputs r.arity (PCJ6e421fabe2aa4155_SourceThresholdCache.bits a r ci hk)
      (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci) 1,
    frame (PCJ6e421fabe2aa4155_SourceThresholdTop.payload (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci))]
def slots : Fin 5→Fin 210:=![199,200,204,101,206]
def first:=TapeEmbedding.machine 4 PCJ6e421fabe2aa4155_SourceThresholdTopQuery.machine
def last:=RecoveryFocus.machine slots (PCJ6e421fabe2aa4155_SourceClear.rewind 3)
def machine:=Composition.machine first last
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) : Fin 210→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (PCJ6e421fabe2aa4155_SourceThresholdTopQuery.input a r ci C) (fun _ : Fin 4=>[])
def beforeHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) : Fin 210→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (PCJ6e421fabe2aa4155_SourceThresholdTopQuery.finalHeads a r ci hk) (fun _ : Fin 4=>0)
def finalHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits):=
  dockH slots (beforeHeads a r ci hk) (fun _=>0)
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat):=
  PCJ6e421fabe2aa4155_SourceThresholdTopQuery.budget a r ci C+1+2*Capacity.value r.arity+2

theorem before_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) (i : Fin 5) :
    beforeHeads a r ci hk (slots i)=PCJ6e421fabe2aa4155_SourceClear.join
      (fun j=>(streams a r ci hk j).length) 0 0 i := by
  fin_cases i
  · change PCJ6e421fabe2aa4155_SourceThresholdTopQuery.finalHeads a r ci hk 199=_
    rw [PCJ6e421fabe2aa4155_SourceThresholdTopQuery.finalHeads,dockH_other _ _ _ 199 (by decide)]
    change PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads a r ci hk (PCJ6e421fabe2aa4155_SourceThresholdQuery.slots 29)=_
    rw [PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads,dockH_slot _ PCJ6e421fabe2aa4155_SourceThresholdQuery.slots_inj _ _ 29]
    rfl
  · change PCJ6e421fabe2aa4155_SourceThresholdTopQuery.finalHeads a r ci hk 200=_
    rw [PCJ6e421fabe2aa4155_SourceThresholdTopQuery.finalHeads,dockH_other _ _ _ 200 (by decide)]
    change PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads a r ci hk (PCJ6e421fabe2aa4155_SourceThresholdQuery.slots 30)=_
    rw [PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads,dockH_slot _ PCJ6e421fabe2aa4155_SourceThresholdQuery.slots_inj _ _ 30]
    rfl
  · change PCJ6e421fabe2aa4155_SourceThresholdTopQuery.finalHeads a r ci hk (PCJ6e421fabe2aa4155_SourceThresholdTopQuery.slots 2)=_
    rw [PCJ6e421fabe2aa4155_SourceThresholdTopQuery.finalHeads,dockH_slot PCJ6e421fabe2aa4155_SourceThresholdTopQuery.slots (by decide) _ _ 2]
    change (PCJ6e421fabe2aa4155_SourceThresholdTop.finalOut _ 0).length=_
    rw [PCJ6e421fabe2aa4155_SourceThresholdTop.final_exact]
    rfl
  · change PCJ6e421fabe2aa4155_SourceThresholdTopQuery.finalHeads a r ci hk 101=0
    rw [PCJ6e421fabe2aa4155_SourceThresholdTopQuery.finalHeads,dockH_other _ _ _ 101 (by decide)]
    change PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads a r ci hk (PCJ6e421fabe2aa4155_SourceThresholdQuery.slots 22)=0
    rw [PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads,dockH_slot _ PCJ6e421fabe2aa4155_SourceThresholdQuery.slots_inj _ _ 22]
    rfl
  · rfl

end
end PCJ6e421fabe2aa4155_SourceThresholdReady
