import Proof.Wire_3_5.Recovery.HybridProgOneBranch

/-! # The hybrid `E^NP` program: Source (P3:3758-3759; D1.6 C)

Realizes, for the hybrid slice, "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on
the source length `N_{a(n)}`" (P3:3758-3759): base's `CloseoutCommonProgram` step `CommonProgramSource`, restated over
the hybrid program's `Parameters` (the scan prefix and hybrid Case-2 machine). Base's description: The common worker's native request and dimensions are the original selected outer PCP's request and dimensions.

Paper quantity: the hybrid slice's one ordinary `E^NP` program. -/

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces ProjectionNormalization
open SelectedRecoveryIntegration RecoveryScheduleEnvelope PolynomialClock
set_option autoImplicit false
noncomputable section

def globalPCP (p : Parameters):=(outer p.sources p.k p.clock).result.pcp
def hierarchyWord (p : Parameters) (r : InputRequest):=HierarchySourceInput.hierarchyInput (hierarchy p) r
def sourcePCP (p : Parameters) (r : InputRequest):=(source p).output (HierarchyEncode.encode (hierarchy p) (pad p) r)
def R (p : Parameters) (r : InputRequest):=(globalPCP p).nativeWidth r.1
def Q (p : Parameters) (r : InputRequest):=HierarchyProjection.queries (source p) (hierarchy p) (pad p) r.1
def B (p : Parameters) (r : InputRequest):=oracleSizeBound p.degree (R p r)

theorem pad_large (p : Parameters) : p.k+3 ≤ pad p:=Nat.le_max_right _ _

theorem native_source (p : Parameters) (r : InputRequest) :
    PCPPNativeHierarchyNodes.pcp (source p) p.k (hierarchy p).coefficient (pad p) (code p) r.2=sourcePCP p r:=by
  exact congrArg (source p).output
    (HierarchyStreams.hierarchy_dimensions (source p) (hierarchy p) (pad p) (pad_large p) r).1

theorem native_width (p : Parameters) (r : InputRequest) :
    PCPPNativeHierarchyNodes.width (source p) p.k (hierarchy p).coefficient (pad p) (code p) r.2=R p r:=
  (HierarchyStreams.hierarchy_dimensions (source p) (hierarchy p) (pad p) (pad_large p) r).2.1

theorem native_queries (p : Parameters) (r : InputRequest) :
    PCPPNativeHierarchyNodes.queries (source p) p.k (hierarchy p).coefficient (pad p) (code p) r.2=Q p r:=
  (HierarchyStreams.hierarchy_dimensions (source p) (hierarchy p) (pad p) (pad_large p) r).2.2

theorem bound_positive (p : Parameters) (r : InputRequest) : 0 < B p r:=by
  have hR : 0 < R p r:=by
    change 0 < natBitLength _
    unfold natBitLength
    omega
  exact hR.trans_le (value_le_pairIter (oracleDepth p.degree) (R p r))

structure Fits (p : Parameters) (r : InputRequest) (W : ℕ) : Prop where
  length : r.1 ≤ W
  workspace : CloseoutRecoveryWorkspace.originalWorkspace (R p r) (B p r) (Q p r)
    (Codec.clauses (sourcePCP p r)).length ≤ W
  bytes : (DedupBytes.fields (sourcePCP p r)).length ≤ W
  two : 2^(R p r) ≤ W

end
end NearCubicWires.RepairSource.HybridProgram
