import Proof.Assembly.SourceProduction

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJc4297ab269d8423a_Source
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairRepresentation SourceInterfaces SupplierPipeline SupplierEstimator
open RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-- Original occurrence supports, with multiplicity, and the actual live count. -/
structure MaskData where
  q : Nat
  m : Nat
  K : Nat
  support : Fin m → Finset (Fin q)
  bound : K ≤ q

def MaskData.supportWord (d : MaskData) : List Bool :=
  (List.ofFn (fun i : Fin d.m => RepairOrdinary.frame
    (List.ofFn (fun x : Fin d.q => decide (x ∈ d.support i))))).flatten

def MaskData.word (d : MaskData) : List Bool :=
  List.ofFn (fun x : Fin d.q => decide (x ∈ CyclicChoice.selectedLive d.support d.K))

/-- Only existing support frames and unary domain/count drivers enter.
In particular the q-bit output is not assumed resident. -/
def MaskData.input (work : Nat) (d : MaskData) : Fin (5+work) → List Bool := fun i =>
  if i.val=0 then d.supportWord else
  if i.val=1 then CompareMachine.word d.q else
  if i.val=2 then CompareMachine.word d.K else
  if i.val=3 then CompareMachine.word d.m else []

def maskBudget (coefficient degree : Nat) (d : MaskData) : Nat :=
  coefficient * (d.q+d.K+d.m+d.supportWord.length+1)^degree

/-- One ordinary program, chosen before every runtime input and every source
hierarchy parameter. Final private words are deliberately left unconstrained. -/
structure MaskProducer where
  work : Nat
  states : Nat
  machine : Machine (5+work) states
  coefficient : Nat
  degree : Nat
  positive : 0 < coefficient
  correct : ∀ d : MaskData, ∃ B : Fin (5+work) → List Bool,
    Step machine (maskBudget coefficient degree d) (fun _ => 0) (d.input work)
      (fun _ => 0) B ∧ B ⟨4,by omega⟩=d.word

end
end PCJc4297ab269d8423a_Source
