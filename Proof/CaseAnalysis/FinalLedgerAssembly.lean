import Proof.CaseAnalysis.FinalCompletion
import Proof.CaseAnalysis.FinalStageSeamBridge
import Proof.CaseAnalysis.FinalSupplierCall

namespace NearCubicWires.RepairSource.CloseoutFinal.C10LedgerAssembly

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open RepairOrdinary.CloseoutFinalC10StageSeam (dockedFuel)
open RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  The width-growth link, in the direction the ledger needs -/

/-- **The native width dominates every fixed threshold, eventually.**  The
selected source's native width at length `N` is `Nat.log 2` of the projection
envelope of `N`, and the envelope dominates `N + 1`
(`input_le_envelope`, `Proof/CaseAnalysis/NativeWidthStep.lean`); so once
`2 ^ T <= N`, the width is at least `T`.  This is
`input_cutoff_native` (`Proof/CaseAnalysis/WitnessInputCutoff.lean`) with its
fixed `minimumArity` replaced by a free `T` -- the same proof, nothing new. -/
theorem nativeWidth_ge (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (T N : ℕ) (hN : 2 ^ T ≤ N) :
    T ≤ (outer sources k clock).result.pcp.nativeWidth N := by
  let H := (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy
  have hp : 2 ^ T ≤ ProjectionNormalization.Dimensions.envelope (fixedProjection sources)
      (HierarchyEncode.length H (padding sources k clock) N) :=
    hN.trans ((Nat.le_succ N).trans
      (CloseoutNativeWidth.input_le_envelope (fixedProjection sources) H
        (padding sources k clock) N))
  exact (Nat.le_log_of_pow_le (by decide : 1 < 2) hp).trans (Nat.le_succ _)

/-! ## Section 2  The ledger -/

end
end NearCubicWires.RepairSource.CloseoutFinal.C10LedgerAssembly
