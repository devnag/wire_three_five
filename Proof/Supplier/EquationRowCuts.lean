import Proof.Supplier.EquationCutAmbientLayout

/-! Execute the accepted two-cut emitter once per original equation, using
one physical G driver. No cut buffer, scalar workspace or cursor is free. -/
namespace NearCubicWires.RepairOrdinary.EquationRowCuts
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def stream (p : Nat) (cuts : List Cut) := cuts.flatMap (cutWord p)
def machine := RepeatMachine.machine EquationCut.Ambient.machine (fun _ _=>true)

@[simp] theorem stream_nil (p : Nat) : stream p []=[] := rfl
@[simp] theorem stream_cons (p : Nat) (c : Cut) (cuts : List Cut) :
    stream p (c::cuts)=cutWord p c++stream p cuts := rfl

end
end NearCubicWires.RepairOrdinary.EquationRowCuts
