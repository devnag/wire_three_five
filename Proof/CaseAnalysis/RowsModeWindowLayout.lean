import Proof.CaseAnalysis.RowsModeWindowGuard
import Proof.CaseAnalysis.RowsModeWindowSelect

/-! The elementary and scalar banks share one paid log. Subset digit width
v remains separate from coefficient width u, and original M is retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowLayout
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey ExtDecompositionBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scalarCaps (C : Nat) (i : Fin 8):=if i=5 then 0 else C
def scalars (u offset b scratch degree target C : Nat) (nonzero guard : Bool) : Fin 8→List Bool:=
  fun i=>ZeroPadding.pad (scalarCaps C i)
    (CloseoutRowsModeWindowGuard.data u offset b scratch degree target (C+1) nonzero guard i)
def extra (u M offset b scratch degree target C : Nat) (nonzero guard : Bool) : Fin 8→List Bool:=
  let A:=scalars u offset b scratch degree target C nonzero guard
  ![A 0,A 1,A 2,A 3,A 4,A 6,A 7,List.replicate M true]
def heads (out : List Bool) : Fin 60→Nat:=Fin.addCases (m:=52) (n:=8) (motive:=fun _=>Nat)
  (CloseoutRowsModeElementaryLayout.heads out) (fun _=>0)
noncomputable def data (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) : Fin 60→List Bool:=
  Fin.addCases (m:=52) (n:=8) (motive:=fun _=>List Bool)
    (CloseoutRowsModeElementaryReusable.paddedBlank v a M C out)
    (extra u M offset b scratch degree target C nonzero guard)
def guardSlots : Fin 8→Fin 60:=![52,53,54,55,56,51,57,58]

noncomputable def elementary:=TapeEmbedding.machine 8 CloseoutRowsModeElementaryReusable.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowLayout
