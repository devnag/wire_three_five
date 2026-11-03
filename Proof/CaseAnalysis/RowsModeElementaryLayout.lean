import Proof.CaseAnalysis.RowsModeElementaryReload
import Proof.CaseAnalysis.RowsModeElementaryClear

/-! The reusable elementary bank has four original numeric master tapes,
an original coarse C driver, and one shared erase/copy log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryLayout
open LocalBitMultitape RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def metadata (w k M : Nat) : Fin 4→List Bool:=
  ![CompareMachine.word w,frame (binary w (M-1)),CompareMachine.word k,List.replicate w true]
def extra (w k M C : Nat) : Fin 6→List Bool:=
  Fin.addCases (m:=4) (n:=2) (motive:=fun _=>List Bool) (metadata w k M)
    ![List.replicate C true,List.replicate (C+1) false]
noncomputable def raw (w k M : Nat) (out : List Bool):=
  (⟨CloseoutRowsModeElementary.machine.start,CloseoutRowsModeElementary.heads out,
    CloseoutRowsModeElementary.input w k M out⟩ : Configuration 45 _)
noncomputable def loaded (w k M C : Nat) (out : List Bool):=
  TapeEmbedding.config (fun _ : Fin 6=>0) (extra w k M C)
    (CloseoutRowsModeElementaryReset.input (raw w k M out) C)
def heads (out : List Bool) (i : Fin 52):=if i=44 then out.length else 0
noncomputable def blank (w k M C : Nat) (out : List Bool):=
  CloseoutRowsModeElementaryReload.data (loaded w k M C out).tapes C (metadata w k M) 0

end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryLayout
