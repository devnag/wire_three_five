import Proof.CaseAnalysis.RowsReusableCuts
import Proof.CaseAnalysis.RowsMetadataReload
import Proof.CaseAnalysis.RowsDegreeNext

/-! One exact boundary for the degree loop: native row context, 57 work
tapes, the retained C driver/logs, and six short templates. The worker
receipt describes every physical head and tape needed by its next call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsLoopLayout
open LocalBitMultitape RecoveryExecution CloseoutRowsDegreeReset
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def templates (p w M j : ℕ) : Fin 6→List Bool :=
  ![CompareMachine.word w,frame (SignedSortKey.binary w (M-1)),CompareMachine.word (j+1),
    List.replicate w true,List.replicate j true,List.replicate p true]
def extra (p w M j C : ℕ) : Fin 9→List Bool :=
  Fin.addCases (m:=3) (n:=6) (motive:=fun _=>List Bool)
    ![List.replicate C false,List.replicate C true,List.replicate (C+1) false] (templates p w M j)
noncomputable def rawInput {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  CloseoutRowsComputedCuts.input (0 : Fin 1) gs p F w j rows out
noncomputable def inputHeads {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) : Fin 112→ℕ :=
  Fin.addCases (m:=103) (n:=9) (motive:=fun _=>ℕ) (rawInput gs p F w j rows out).heads (fun _=>0)
noncomputable def inputTapes {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) : Fin 112→List Bool :=
  Fin.addCases (m:=103) (n:=9) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (caps C i) ((rawInput gs p F w j rows out).tapes i))
    (extra p w rows.length j C)
noncomputable def worker := TapeEmbedding.machine 6 CloseoutRowsReusableCuts.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsLoopLayout
