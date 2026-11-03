import Proof.SourceAssembly.SourceThresholdQuery

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceThresholdTopQuery
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots : Fin 6→Fin 206:=![164,203,204,205,140,201]
def first:=TapeEmbedding.machine 3 PCJ6e421fabe2aa4155_SourceThresholdQuery.machine
def last:=RecoveryFocus.machine slots PCJ6e421fabe2aa4155_SourceThresholdTop.machine
def machine:=Composition.machine first last
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) : Fin 206→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (PCJ6e421fabe2aa4155_SourceThresholdQuery.input a r ci C) (fun _ : Fin 3=>[])
def beforeHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) : Fin 206→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads a r ci hk) (fun _ : Fin 3=>0)
def finalHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits):=
  dockH slots (beforeHeads a r ci hk) (PCJ6e421fabe2aa4155_SourceThresholdTop.H
    (PCJ6e421fabe2aa4155_SourceThresholdTop.finalOut (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci)))
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat):=
  PCJ6e421fabe2aa4155_SourceThresholdQuery.budget a r ci C+1+
    PCJ6e421fabe2aa4155_SourceThresholdTop.budget (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci)

theorem selected_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) (i : Fin 6) :
    beforeHeads a r ci hk (slots i)=PCJ6e421fabe2aa4155_SourceThresholdTop.inputHeads i := by
  fin_cases i
  · change PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads a r ci hk 164=0
    rw [PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads,dockH_other _ _ _ 164 (by decide)]
    change PCJ6e421fabe2aa4155_SourceThresholdCache.finalHeads a r ci 164=0
    rw [PCJ6e421fabe2aa4155_SourceThresholdCache.finalHeads,dockH_other _ _ _ 164 (by decide)]
    change PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.finalHeads a r ci 164=0
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.slots_inj _ _ 24
  · rfl
  · rfl
  · rfl
  · change PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads a r ci hk (PCJ6e421fabe2aa4155_SourceThresholdQuery.slots 32)=1
    rw [PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads,dockH_slot _ PCJ6e421fabe2aa4155_SourceThresholdQuery.slots_inj _ _ 32]
    rfl
  · change PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads a r ci hk (PCJ6e421fabe2aa4155_SourceThresholdQuery.slots 31)=0
    rw [PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads,dockH_slot _ PCJ6e421fabe2aa4155_SourceThresholdQuery.slots_inj _ _ 31]
    rfl

end
end PCJ6e421fabe2aa4155_SourceThresholdTopQuery
