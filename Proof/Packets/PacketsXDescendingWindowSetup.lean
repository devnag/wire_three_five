import Proof.Packets.DescendingWindowPrepare
import Proof.CaseAnalysis.RowsDegreeAdvance
import Proof.CaseAnalysis.RowsModeWindowScalar

/-! Paid descending-antidiagonal setup docked into the actual retained
sixty-tape elementary/scalar bank, plus its one physical count tape. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowSetup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeWindowLayout

def slots : Fin 5→Fin 61 := ![48,53,60,50,51]
def H (out : List Bool) : Fin 61→Nat := Fin.addCases (m:=60) (n:=1) (motive:=fun _=>Nat) (heads out) (fun _ : Fin 1=>0)
noncomputable def A (v u M a offset b scratch d target C count : Nat)
    (nonzero guard : Bool) (out : List Bool) : Fin 61→List Bool :=
  Fin.addCases (m:=60) (n:=1) (motive:=fun _=>List Bool) (data v u M a offset b scratch d target C nonzero guard out)
    (fun _ : Fin 1=>ZeroPadding.pad C (CompareMachine.word count))
noncomputable def machine := RecoveryFocus.machine slots DescendingWindowPrepare.machine

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowSetup
