import Proof.SourceAssembly.SourceThresholdReady

/- Full fixed physical THR parity-circuit producer from the actual queried
bank. Every source field and rewind driver comes from the paid prefix. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceThresholdPhysical
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def gates (q n : Nat) (bits : List Bool) : List CloseoutRowsTupleSeek.GatePair:=
  (List.range n).map (fun j=>(natWord q++weights bits++false::natWord j,bits))
theorem gates_length (q n : Nat) (bits : List Bool) : (gates q n bits).length=n:=by simp [gates]
theorem gates_native (q n : Nat) (bits : List Bool) : CloseoutRowsTupleSeek.nativeWord (gates q n bits)=
    PCJ6e421fabe2aa4155_SourceThresholdLoop.outputs q bits n 0 := by
  simp only [CloseoutRowsTupleSeek.nativeWord,gates,List.flatMap_map];rfl
theorem gates_support (q n : Nat) (bits : List Bool) : CloseoutRowsTupleSeek.supportWord (gates q n bits)=
    PCJ6e421fabe2aa4155_SourceThresholdLoop.outputs q bits n 1 := by
  simp only [CloseoutRowsTupleSeek.supportWord,gates,List.flatMap_map];rfl

def native (q n : Nat) (bits : List Bool):=PCJ6e421fabe2aa4155_SourceSymmetricAssemble.circuitWord
  (PCJ6e421fabe2aa4155_SourceThresholdTop.payload n) (gates q n bits)
def slots : Fin 8→Fin 210:=![161,204,199,200,140,207,208,209]
theorem slots_inj : Function.Injective slots:=by decide
def writer:=RecoveryFocus.machine slots PCJ6e421fabe2aa4155_SourceSymmetricAssemble.machine
def machine:=Composition.machine PCJ6e421fabe2aa4155_SourceThresholdReady.machine writer
def finalHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits):=
  dockH slots (PCJ6e421fabe2aa4155_SourceThresholdReady.finalHeads a r ci hk)
    (PCJ6e421fabe2aa4155_SourceSymmetricAssemble.H
      (PCJ6e421fabe2aa4155_SourceThresholdTop.payload (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci))
      (gates r.arity (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci)
        (PCJ6e421fabe2aa4155_SourceThresholdCache.bits a r ci hk)) 3)
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits):=
  PCJ6e421fabe2aa4155_SourceThresholdReady.budget a r ci C+1+
    PCJ6e421fabe2aa4155_SourceSymmetricAssemble.budget
      (PCJ6e421fabe2aa4155_SourceThresholdTop.payload (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci))
      (gates r.arity (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci)
        (PCJ6e421fabe2aa4155_SourceThresholdCache.bits a r ci hk))

theorem selected_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) (i : Fin 8) :
    PCJ6e421fabe2aa4155_SourceThresholdReady.finalHeads a r ci hk (slots i)=
      PCJ6e421fabe2aa4155_SourceSymmetricAssemble.H
        (PCJ6e421fabe2aa4155_SourceThresholdTop.payload (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci))
        (gates r.arity (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci)
          (PCJ6e421fabe2aa4155_SourceThresholdCache.bits a r ci hk)) 0 i := by
  fin_cases i
  · change PCJ6e421fabe2aa4155_SourceThresholdReady.finalHeads a r ci hk 161=0
    rw [PCJ6e421fabe2aa4155_SourceThresholdReady.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change PCJ6e421fabe2aa4155_SourceThresholdTopQuery.finalHeads a r ci hk 161=0
    rw [PCJ6e421fabe2aa4155_SourceThresholdTopQuery.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads a r ci hk 161=0
    rw [PCJ6e421fabe2aa4155_SourceThresholdQuery.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change PCJ6e421fabe2aa4155_SourceThresholdCache.finalHeads a r ci 161=0
    rw [PCJ6e421fabe2aa4155_SourceThresholdCache.finalHeads,dockH_other _ _ _ 161 (by decide)]
    change PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.finalHeads a r ci 161=0
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.slots_inj _ _ 21
  · exact dockH_slot _ (by decide) _ _ 2
  · exact dockH_slot _ (by decide) _ _ 0
  · exact dockH_slot _ (by decide) _ _ 1
  · change PCJ6e421fabe2aa4155_SourceThresholdReady.finalHeads a r ci hk 140=1
    rw [PCJ6e421fabe2aa4155_SourceThresholdReady.finalHeads,dockH_other _ _ _ 140 (by decide)]
    change PCJ6e421fabe2aa4155_SourceThresholdTopQuery.finalHeads a r ci hk 140=1
    exact dockH_slot _ (by decide) _ _ 4
  · exact dockH_other _ _ _ 207 (by decide)
  · exact dockH_other _ _ _ 208 (by decide)
  · exact dockH_other _ _ _ 209 (by decide)

end
end PCJ6e421fabe2aa4155_SourceThresholdPhysical
