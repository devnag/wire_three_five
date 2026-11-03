import Proof.SourceAssembly.SourceLog
import Proof.MachineModel.ClockUnaryProduct
import Proof.PCP.ProjectionDimensionTemplate
import Proof.Hierarchy.HierarchyFixedWord

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceLiveCount
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open PCJ6e421fabe2aa4155_SourceLog SupplierPipeline SupplierEstimator
noncomputable section

theorem product_step (L e : Nat) : Step ClockUnaryProduct.machine (2*(L*(2*e+3)+2)+2)
    (fun _=>0) ![List.replicate L true,CompareMachine.word e,[],[]] (fun _=>0)
    ![List.replicate L true,CompareMachine.word e,List.replicate (L*e) true,List.replicate (L*(2*e+3)+2) false] := by
  obtain ⟨r,hr,h0,h1,h2,h3,hh,hs⟩:=ClockUnaryProduct.product_run L e
  have hi : (Fin.addCases (motive:=fun _ : Fin 4=>List Bool)
      ![List.replicate L true,false::List.replicate e true,[]] (fun _ : Fin 1=>[]))=
      ![List.replicate L true,CompareMachine.word e,[],[]] := by
    funext i;fin_cases i <;>rfl
  rw [hi] at hr
  refine ⟨r,hr,funext hh,?_,hs.le⟩
  funext i;fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem unary_pad (n : Nat) : UnaryTemplate.tape n=ZeroPadding.pad (n+2) (CompareMachine.word n) := by
  simp [UnaryTemplate.tape,ZeroPadding.pad,CompareMachine.word]

def fixedSlots : Fin 2→Fin 27:=![16,17]
def productSlots : Fin 4→Fin 27:=![16,14,18,19]
def templateSlots : Fin 3→Fin 27:=![18,20,21]
def splitSlots : Fin 5→Fin 27:=![0,20,22,23,24]
def finalSlots : Fin 3→Fin 27:=![22,25,26]
def first:=TapeEmbedding.machine 11 PCJ6e421fabe2aa4155_SourceLog.machine
def fixed (L : Nat):=RecoveryFocus.machine fixedSlots (HierarchyFixedWord.machine (List.replicate L true))
def product:=RecoveryFocus.machine productSlots ClockUnaryProduct.machine
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def split:=RecoveryFocus.machine splitSlots PCJ6e421fabe2aa4155_SourceLiveMin.split
def last:=RecoveryFocus.machine finalSlots (DimensionTemplate.machine false)
def machine (L : Nat):=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine first (fixed L)) product) template) split) last

def budget (q L : Nat):=
  ((((PCJ6e421fabe2aa4155_SourceLog.budget q+1+(2*L+2))+1+(2*(L*(2*logScale q+3)+2)+2))+1+
    (2*(L*logScale q)+8))+1+(2*q+6))+1+(2*normalizedLiveCount q L+8)

end
end PCJ6e421fabe2aa4155_SourceLiveCount
