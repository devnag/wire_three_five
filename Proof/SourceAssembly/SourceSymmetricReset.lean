import Proof.SourceAssembly.SourceSymmetricBound
import Proof.SourceAssembly.SourceClear

/- The actual local C driver rewinds only the two produced bottom streams.
The potentially much longer retained query bitmap is outside this bank. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceSymmetricReset
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots : Fin 4→Fin 170:=![138,139,101,166]
def first:=TapeEmbedding.machine 4 PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.machine
def last:=RecoveryFocus.machine slots (PCJ6e421fabe2aa4155_SourceClear.rewind 2)
def machine:=Composition.machine first last
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) : Fin 170→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.input a r ci C) (fun _ : Fin 4=>[])
def beforeHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) : Fin 170→Nat:=
  Fin.addCases (motive:=fun _=>Nat) (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.finalHeads a r ci) (fun _ : Fin 4=>0)
def finalHeads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)):=dockH slots (beforeHeads a r ci) (fun _=>0)
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat):=
  PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.budget a r ci C+1+2*Capacity.value r.arity+2

theorem before_heads (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (i : Fin 4) :
    beforeHeads a r ci (slots i)=PCJ6e421fabe2aa4155_SourceClear.join
      (fun j=> (PCJ6e421fabe2aa4155_SourceSymmetricScan.outputs r.arity
        (PCJ6e421fabe2aa4155_SourceSymmetricQuery.bitmap a r ci) r.arity j).length) 0 0 i := by
  fin_cases i
  · change PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.finalHeads a r ci 138=_
    rw [PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 138 (by decide)]
    change PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.beforeHeads a r ci ((138 : Fin 141).castAdd 25)=_
    rw [PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricQuery.slots_inj _ _ 3
  · change PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.finalHeads a r ci 139=_
    rw [PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 139 (by decide)]
    change PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.beforeHeads a r ci ((139 : Fin 141).castAdd 25)=_
    rw [PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_slot _ PCJ6e421fabe2aa4155_SourceSymmetricQuery.slots_inj _ _ 4
  · change PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.finalHeads a r ci 101=0
    rw [PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.finalHeads,dockH_other _ _ _ 101 (by decide)]
    change PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.beforeHeads a r ci ((101 : Fin 141).castAdd 25)=0
    rw [PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.beforeHeads,Fin.addCases_left]
    exact dockH_other _ _ _ 101 (by decide)
  · rfl

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C) :
    ∃ A,Step machine (budget a r ci C) (fun _=>0) (input a r ci C) (finalHeads a r ci) A ∧
      A 138=PCJ6e421fabe2aa4155_SourceSymmetricScan.outputs r.arity (PCJ6e421fabe2aa4155_SourceSymmetricQuery.bitmap a r ci) r.arity 0 ∧
      A 139=PCJ6e421fabe2aa4155_SourceSymmetricScan.outputs r.arity (PCJ6e421fabe2aa4155_SourceSymmetricQuery.bitmap a r ci) r.arity 1 ∧
      A 140=CompareMachine.word (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci) ∧
      A 142=frame (PCJ6e421fabe2aa4155_SourceSymmetricTop.table (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci)) ∧
      A 161=natWord (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.count a r ci) ∧
      A 167=[] ∧A 168=[] ∧A 169=[] := by
  obtain ⟨A,ha,h138,h139,h140,h142,h161,h101⟩:=PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.run a r ci C hc
  let bank : Fin 170→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 4=>[])
  let out:=PCJ6e421fabe2aa4155_SourceSymmetricScan.outputs r.arity
    (PCJ6e421fabe2aa4155_SourceSymmetricQuery.bitmap a r ci) r.arity
  have firstStep : Step first (PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery.budget a r ci C)
      (fun _=>0) (input a r ci C) (beforeHeads a r ci) bank :=
    (ha.embed (fun _ : Fin 4=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have raw:=PCJ6e421fabe2aa4155_SourceClear.raw_rewind out (fun i=>(out i).length)
    (Capacity.value r.arity) (fun i=>PCJ6e421fabe2aa4155_SourceSymmetricBound.output_bound r.arity _ i)
  have selected : ∀ i,bank (slots i)=PCJ6e421fabe2aa4155_SourceClear.join out
      (List.replicate (Capacity.value r.arity) true) [] i := by
    intro i;fin_cases i
    · exact h138
    · exact h139
    · exact h101
    · rfl
  have lastStep:=raw.dock slots (by decide) (beforeHeads a r ci) bank (before_heads a r ci) selected
  refine ⟨_,(firstStep.seq lastStep).enlarge (by unfold budget;omega),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact install_slot slots (by decide) bank _ 0
  · exact install_slot slots (by decide) bank _ 1
  · exact (install_other slots bank _ 140 (by decide)).trans h140
  · exact (install_other slots bank _ 142 (by decide)).trans h142
  · exact (install_other slots bank _ 161 (by decide)).trans h161
  · exact install_other slots bank _ 167 (by decide)
  · exact install_other slots bank _ 168 (by decide)
  · exact install_other slots bank _ 169 (by decide)

end
end PCJ6e421fabe2aa4155_SourceSymmetricReset
