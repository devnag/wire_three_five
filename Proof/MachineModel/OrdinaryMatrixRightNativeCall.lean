import Proof.MachineModel.OrdinaryMatrixBatchRightReturn

/-! The right-bucket controller at the original Request's native width.
All rank, endpoint and scratch bounds are derived locally; its finite
sentinel and padded bank match the reusable ordinary caller. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightNativeCall
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ranks_fit (r : Request) (g : Fin r.Gates) :
    ∀ entry∈MatrixScoreRawRanks.entries r g,entry.2.2<2^(H r)-1 := by
  have hs : ∀ entry∈MatrixScoreRawRanks.entries r g,entry.2.2<2^r.M := by
    apply KeyLoop.indexed_fits
    have hl := MatrixBucketCallBounds.entries_length r g
    simp only [MatrixScoreRawRanks.entries,KeyLoop.indexed_length] at hl
    rw [MatrixBucketCallBounds.native_power]
    have hu : 1≤r.U := Nat.one_le_two_pow
    omega
  intro entry he
  have h := hs entry he
  have hp := MatrixBucketCallBounds.header_power r
  have hu : 1≤r.U := Nat.one_le_two_pow
  rw [MatrixBucketCallBounds.native_power] at h
  omega

theorem boundary_fit (r : Request) :
    (r.bucketSize+1)+r.Buckets*(r.bucketSize+1)<2^(H r) := by
  have hb := MatrixBucketCallBounds.boundary_le r
  have hB : r.bucketSize+1≤2*r.U+1 := MatrixBucketDimensions.width_le r.U r.Gates
  have hp := MatrixBucketCallBounds.header_power r
  have hu : 1≤r.U := Nat.one_le_two_pow
  omega

noncomputable def params (r : Request) (g : Fin r.Gates) : MatrixRightBucket.Params where
  S := r.S
  K := r.M
  I := r.M
  B := r.bucketSize+1
  keyCap := MatrixScoreReusableRanks.D r
  resetCap := MatrixScoreReusableRanks.D r
  records := MatrixScoreRawRanks.entries r g
  rankFit := ranks_fit r g
  keyI := by have h := (MatrixBatchBucketBankFields.capacity_fit r).2; omega
  keyK := by have h := (MatrixBatchBucketBankFields.capacity_fit r).2; omega
  resetFit := by
    rw [MatrixBucketCallBounds.entries_length]
    have h := MatrixBucketCallBounds.reset_fit r
    unfold MatrixBucketCallBounds.resetBudget H at h
    convert h using 1
    ring

def driverCaps (r : Request) (i : Fin 26) := if i=25 then r.Buckets+2 else 0
def caps (r : Request) (i : Fin 26) := if i=22 then 0 else MatrixScoreReusableRanks.D r
noncomputable def cfg (r : Request) (g : Fin r.Gates) (phase : Fin 5) (v : MatrixRightAdvance.Store) :=
  ZeroPadding.config (caps r) (ZeroPadding.config (driverCaps r)
    (RepeatMachine.cfg phase (MatrixRightBucket.cfg MatrixRightBucket.machine.start (params r g) v) r.Buckets 1))
def budget (r : Request) := r.Buckets*(2*MatrixBucketCallBounds.resetBudget r+24*H r+4*r.M+36)+3
noncomputable def output (r : Request) (g : Fin r.Gates) :=
  MatrixRightLoop.output (params r g) (r.bucketSize+1) (g.val*r.Buckets) r.Buckets

end NearCubicWires.RepairOrdinary.MatrixRightNativeCall
