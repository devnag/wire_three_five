import Proof.SourceAssembly.SourceThresholdCache

/- Actual queried support/cache/count → reusable THR staircase loop. The33
callee inputs are docked from five retained tapes and freshly allocated work. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceThresholdQuery
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots (i : Fin 33) : Fin 203:=if i=22 then 101 else if i=26 then 131 else if i=27 then 166 else
  if i=28 then 167 else if i=32 then 140 else i.natAdd 170
theorem slots_inj : Function.Injective slots:=by decide
def oldSlots : Fin 5→Fin 170:=![101,131,166,167,140]
def first:=TapeEmbedding.machine 33 PCJ6e421fabe2aa4155_SourceThresholdCache.machine
def last:=RecoveryFocus.machine slots PCJ6e421fabe2aa4155_SourceThresholdCold.machine
def machine:=Composition.machine first last
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) : Fin 203→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (PCJ6e421fabe2aa4155_SourceThresholdCache.input a r ci C) (fun _ : Fin 33=>[])
def beforeHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) : Fin 203→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (PCJ6e421fabe2aa4155_SourceThresholdCache.finalHeads a r ci) (fun _ : Fin 33=>0)
def finalHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits):=
  dockH slots (beforeHeads a r ci) (PCJ6e421fabe2aa4155_SourceThresholdCold.heads r.arity
    (PCJ6e421fabe2aa4155_SourceThresholdCache.bits a r ci hk) (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci))
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat):=
  PCJ6e421fabe2aa4155_SourceThresholdCache.budget a r ci C+1+
    PCJ6e421fabe2aa4155_SourceThresholdCold.budget r.arity (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci)

theorem count_le (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) : PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci≤r.arity := by
  exact (List.length_filter_le _ _).trans List.length_range.le

theorem old_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (i : Fin 5) :
    PCJ6e421fabe2aa4155_SourceThresholdCache.finalHeads a r ci (oldSlots i)=0 := by
  fin_cases i
  · exact dockH_slot _ (by decide) _ _ 2
  · change PCJ6e421fabe2aa4155_SourceThresholdCache.finalHeads a r ci 131=0
    rw [PCJ6e421fabe2aa4155_SourceThresholdCache.finalHeads,dockH_other _ _ _ 131 (by decide)]
    change PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.finalHeads a r ci 131=0
    rw [PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 131 (by decide)]
    change PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.beforeHeads a r ci ((131 : Fin 141).castAdd 25)=0
    rw [PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricQuery.slots_inj _ _ 2
  · exact dockH_slot _ (by decide) _ _ 3
  · exact dockH_slot _ (by decide) _ _ 4
  · change PCJ6e421fabe2aa4155_SourceThresholdCache.finalHeads a r ci 140=0
    rw [PCJ6e421fabe2aa4155_SourceThresholdCache.finalHeads,dockH_other _ _ _ 140 (by decide)]
    change PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.finalHeads a r ci 140=0
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.slots_inj _ _ 3

theorem selected_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (i : Fin 33) : beforeHeads a r ci (slots i)=0 := by
  by_cases h22:i=22
  · subst i;exact old_heads a r ci 0
  by_cases h26:i=26
  · subst i;exact old_heads a r ci 1
  by_cases h27:i=27
  · subst i;exact old_heads a r ci 2
  by_cases h28:i=28
  · subst i;exact old_heads a r ci 3
  by_cases h32:i=32
  · subst i;exact old_heads a r ci 4
  simp only [slots,h22,h26,h27,h28,h32,if_false,beforeHeads,Fin.addCases_right]

end
end PCJ6e421fabe2aa4155_SourceThresholdQuery
