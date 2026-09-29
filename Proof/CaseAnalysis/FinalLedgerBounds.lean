import Proof.CaseAnalysis.FinalLedgerAssembly

namespace NearCubicWires.RepairSource.CloseoutFinal.C10LedgerBounds

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open RepairOrdinary.CloseoutFinalC10StageSeam (dockedFuel)
open RepairOrdinary.CloseoutFinalC10WorkerDock (joinScalarWidth dockBudget)
open RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  `hrows` -- the clause-address count against a power of the width -/

/-! ## Section 2  `hrow` -- one external row against one residual table factor -/

/-! ## Section 3  `hdriver` -- the words stage against a power of the width -/

/-! ## Section 4  `hrest` -- the docked body and the tail against `A * (N+1)` -/

/-! ## Section 5  `hrest` at `a := 1`, from a polylogarithmic width schedule -/

/-! ## Section 6  The native width really is logarithmic in `N` -/

/-- **The native width is at most a constant times the bit length of the
hierarchy clock.**  `HierarchySourceCost.width_bound`
(`Proof/Hierarchy/HierarchySourceOutputBounds.lean`) at the route's own padding
`max H.coefficient (k+3)` (`Proof/Assembly/SelectedRecoveryIntegration.lean`), whose two
side conditions are the two `max` inequalities `outer` itself already supplies
(`Proof/Assembly/SelectedRecoveryIntegration.lean`). -/
theorem nativeWidth_le_time_bits (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (N : ℕ) :
    (outer sources k clock).result.pcp.nativeWidth N
      ≤ ProjectionNormalization.HierarchySourceCost.widthCoefficient
            (fixedProjection sources)
            (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy
            (padding sources k clock)
          * (natBitLength
              ((sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.time N) + 1) :=
  ProjectionNormalization.HierarchySourceCost.width_bound (fixedProjection sources)
    (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy (padding sources k clock)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) N

/-- **`nativeWidth N = O(log N)`, with explicit constants.**  The hierarchy clock
is `H.time N = H.coefficient * (N ^ (k+2) + 1)` (`Proof/Foundations/SourceCore.lean`), so its
bit length is `natBitLength H.coefficient + (k+2) * natBitLength N + 1`.  Together
with `nativeWidth_ge` (`Proof/CaseAnalysis/FinalLedgerAssembly.lean`), which gives
the matching lower bound `T <= nativeWidth N` whenever `2 ^ T <= N`, this pins
`nativeWidth N = Theta (log N)` -- so a schedule polynomial in the native width IS
polylogarithmic in `N`, which is exactly what
`hrest_of_logarithmic_schedule` consumes. -/
theorem nativeWidth_le_log (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (N : ℕ) :
    (outer sources k clock).result.pcp.nativeWidth N
      ≤ ProjectionNormalization.HierarchySourceCost.widthCoefficient
            (fixedProjection sources)
            (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy
            (padding sources k clock)
          * (natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
              + (k + 2) * natBitLength N + 2) := by
  refine (nativeWidth_le_time_bits sources k clock N).trans (Nat.mul_le_mul_left _ ?_)
  have hb : natBitLength ((sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.time N)
      ≤ natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
        + natBitLength (N ^ (k + 2) + 1) :=
    CloseoutNativeWidth.bits_mul_bound _ _ _ (le_of_eq rfl)
  have hp : natBitLength (N ^ (k + 2) + 1) ≤ (k + 2) * natBitLength N + 1 := by
    have h1 : N < 2 ^ natBitLength N := Nat.lt_pow_succ_log_self (by decide) N
    have h2 : N ^ (k + 2) < 2 ^ ((k + 2) * natBitLength N) := by
      calc N ^ (k + 2) < (2 ^ natBitLength N) ^ (k + 2) :=
            Nat.pow_lt_pow_left h1 (by omega)
        _ = 2 ^ (natBitLength N * (k + 2)) := by rw [← pow_mul]
        _ = 2 ^ ((k + 2) * natBitLength N) := by rw [Nat.mul_comm]
    have hpos : 1 ≤ 2 ^ ((k + 2) * natBitLength N) := Nat.one_le_pow _ _ (by norm_num)
    have hdouble : 2 ^ ((k + 2) * natBitLength N) + 2 ^ ((k + 2) * natBitLength N)
        = 2 ^ ((k + 2) * natBitLength N + 1) := by rw [pow_succ]; ring
    have h3 : N ^ (k + 2) + 1 < 2 ^ ((k + 2) * natBitLength N + 1) := by omega
    have h4 : Nat.log 2 (N ^ (k + 2) + 1) < (k + 2) * natBitLength N + 1 :=
      Nat.log_lt_of_lt_pow (by omega) h3
    change Nat.log 2 (N ^ (k + 2) + 1) + 1 ≤ (k + 2) * natBitLength N + 1
    omega
  omega

/-- `natBitLength n = Nat.log 2 n + 1` is below `logScale n = Nat.clog 2 (n + 2)`
(`Proof/Foundations/Semantics.lean`). -/
theorem natBitLength_le_logScale (N : ℕ) : natBitLength N ≤ logScale N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    unfold natBitLength logScale
    norm_num
  · have hle : N + 2 ≤ 2 ^ Nat.clog 2 (N + 2) := Nat.le_pow_clog (by norm_num) _
    have hlt : N < 2 ^ Nat.clog 2 (N + 2) := by omega
    have h := Nat.log_lt_of_lt_pow (by omega : N ≠ 0) hlt
    change Nat.log 2 N + 1 ≤ Nat.clog 2 (N + 2)
    omega

/-- **The bridge from Section 6 to Section 5**: `nativeWidth N + 1` is at most a
CONSTANT times `logScale N`.  A schedule polynomial in `nativeWidth N + 1` is
therefore polynomial in `logScale N`, which is exactly the hypothesis
`hrest_of_logarithmic_schedule` consumes -- so `hrest` at `a := 1` is reachable
from a width-indexed schedule and needs no re-parameterisation of
`ledger_of_parts`. -/
theorem nativeWidth_succ_le_logScale (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (N : ℕ) :
    (outer sources k clock).result.pcp.nativeWidth N + 1
      ≤ (ProjectionNormalization.HierarchySourceCost.widthCoefficient
            (fixedProjection sources)
            (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy
            (padding sources k clock)
          * (natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
              + k + 4) + 1) * logScale N := by
  have hL : 1 ≤ logScale N := by
    unfold logScale
    exact Nat.clog_pos (by norm_num) (by omega)
  have hb := natBitLength_le_logScale N
  have h := nativeWidth_le_log sources k clock N
  have hstep :
      natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
          + (k + 2) * natBitLength N + 2
        ≤ (natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
            + k + 4) * logScale N := by
    have e1 : (natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
          + k + 4) * logScale N
        = natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
            * logScale N + (k + 2) * logScale N + 2 * logScale N := by ring
    have e2 : natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
        * 1 ≤ natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
          * logScale N := Nat.mul_le_mul_left _ hL
    have e3 : (k + 2) * natBitLength N ≤ (k + 2) * logScale N := Nat.mul_le_mul_left _ hb
    omega
  calc (outer sources k clock).result.pcp.nativeWidth N + 1
      ≤ ProjectionNormalization.HierarchySourceCost.widthCoefficient (fixedProjection sources)
            (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy (padding sources k clock)
          * (natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
              + (k + 2) * natBitLength N + 2) + 1 := by omega
    _ ≤ ProjectionNormalization.HierarchySourceCost.widthCoefficient (fixedProjection sources)
            (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy (padding sources k clock)
          * ((natBitLength
                (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
              + k + 4) * logScale N) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hstep) 1
    _ ≤ ProjectionNormalization.HierarchySourceCost.widthCoefficient (fixedProjection sources)
            (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy (padding sources k clock)
          * ((natBitLength
                (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
              + k + 4) * logScale N) + logScale N := by omega
    _ = (ProjectionNormalization.HierarchySourceCost.widthCoefficient (fixedProjection sources)
            (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy (padding sources k clock)
          * (natBitLength
                (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
              + k + 4) + 1) * logScale N := by ring

end
end NearCubicWires.RepairSource.CloseoutFinal.C10LedgerBounds
