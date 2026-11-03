import Proof.MachineModel.NativeState
import Proof.CaseAnalysis.RowsFamilyLoop

/-! The original raw polynomial family executes with one retained native
bank and one literal outer driver, including empty polynomials/families. -/
namespace NearCubicWires.ExtIncidence.NativeFamily
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawWord {B : ℕ} (ms : List (List (Fin B))):=stream (rawIndices ms)
def emit {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) (Q w : ℕ)
    (ms : List (List (Fin gs.length))):=
  (CloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap
    (MatrixScoreBatch.cutWord (NativeWidth.width gs Q))
def cost {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) :
    List (List (List (Fin gs.length)))→ℕ
  | []=>0
  | ms::ps=>max (NativeRound.budget gs Q w (rawIndices ms)) (cost gs Q w ps)

noncomputable def machine:=CloseoutRowsDegreeLoop.machine NativeRound.machine
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ)
    (ps : List (List (List (Fin gs.length)))):=ps.length*(cost gs Q w ps+3)+3
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ)
    (ps : List (List (List (Fin gs.length)))) (pre tail : List Bool)
    (H : Fin 277→ℕ) (A : Fin 277→List Bool) (j : ℕ) (out : List Bool):=
    (⟨NativeRound.machine.start,
      NativeState.heads H (pre.length+((ps.take j).flatMap rawWord).length) out,
      NativeState.tapes A (NativeMaster.words gs Q w) (NativeMeasured.capacity gs Q w)
        (pre++ps.flatMap rawWord++tail) out⟩ : Configuration 277 _)

end NearCubicWires.ExtIncidence.NativeFamily
