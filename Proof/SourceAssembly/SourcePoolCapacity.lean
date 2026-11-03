import Proof.SourceAssembly.SourcePoolAdmissions
import Proof.SourceAssembly.SourceCacheBudget
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePoolCapacity
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding
noncomputable section

def value (B q : Nat):=16777216*(B+q+1)^3

theorem small_bounds (B q : Nat) : q+2≤value B q ∧
    PoolEntry.reserve B q (B+q+1)+1≤value B q ∧8*(B+q+1)+12≤value B q := by
  have hw:1≤B+q+1:=by omega
  have h2:B+q+1≤(B+q+1)^2:=by nlinarith
  have h3:(B+q+1)^2≤(B+q+1)^3:=by
    have h:=Nat.mul_le_mul_right ((B+q+1)^2) hw
    simpa only [one_mul,pow_succ,Nat.mul_comm] using h
  unfold value PoolEntry.reserve
  constructor
  · nlinarith
  constructor <;>nlinarith

end
end PCJ6e421fabe2aa4155_SourcePoolCapacity
