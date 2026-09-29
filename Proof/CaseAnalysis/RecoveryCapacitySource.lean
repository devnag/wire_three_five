import Proof.CaseAnalysis.CaseOneLive
import Proof.CaseAnalysis.RecoveryCapacityActual

/-! Export the source-length domination already present in the SAME recovery
majorant. This pays the original hierarchy-stream call as well as its graph. -/
namespace NearCubicWires.RepairSource.CloseoutRecoveryCapacity
open RepairOrdinary ProjectionNormalization SourceInterfaces RecoveryScheduleEnvelope
open CloseoutLanguage CloseoutRecoveryWorkspace SelectedRecoveryIntegration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem actual_capacity_with_source
    (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) {k : ℕ}
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad degree : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) :
    ∃ A B0 : ℕ, ∀ (n : ℕ) (r : InputRequest), r.1 ≤ 2^n →
      HierarchyProjection.width source H Cpad r.1 ≤ n →
      let p:=source.output (HierarchyEncode.encode H Cpad r)
      let R:=HierarchyProjection.width source H Cpad r.1
      let Q:=HierarchyProjection.queries source H Cpad r.1
      let B:=oracleSizeBound degree R
      let W:=CloseoutCapacity.capacity A B0 n
      r.1 ≤ W ∧ originalWorkspace R B Q (Codec.clauses p).length ≤ W ∧
        R ≤ W ∧ Q ≤ W ∧ B ≤ W ∧ (DedupBytes.fields p).length ≤ W ∧ 2^R ≤ W:=by
  obtain ⟨A,B0,hW⟩:=exists_capacity source H Cpad degree
  refine ⟨A,B0,?_⟩
  intro n r hn hr
  have hx:2^n ≤ majorant source H Cpad degree (2^n):=by
    unfold majorant
    exact (Nat.le_add_left _ _).trans (Nat.le_succ _)
  obtain ⟨hg,hR,hQ,hB,hbytes,htwo⟩:=actual_bounds source H Cpad degree hcoeff hpad r n hn hr
  exact ⟨hn.trans (hx.trans (hW n)),hg.trans (hW n),hR.trans (hW n),hQ.trans (hW n),
    hB.trans (hW n),hbytes.trans (hW n),htwo.trans (hW n)⟩

end
end NearCubicWires.RepairSource.CloseoutRecoveryCapacity
