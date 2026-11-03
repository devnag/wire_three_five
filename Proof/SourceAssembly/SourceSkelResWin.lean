import Proof.SourceAssembly.SourceSkelParamsV4
import Proof.CaseAnalysis.FinalFuelEnvelope

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton.ResWin
noncomputable section

/-- `clog₂(q+2) ≤ 2(log₂ q + 1)`. -/
theorem clog_two_le (q : ℕ) : Nat.clog 2 (q + 2) ≤ 2 * (Nat.log 2 q + 1) := by
  have h1 : q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have hX2 : 2 ≤ 2 ^ (Nat.log 2 q + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (Nat.log 2 q + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : 2 ^ (2 * (Nat.log 2 q + 1)) = 2 ^ (Nat.log 2 q + 1) * 2 ^ (Nat.log 2 q + 1) := by
    rw [two_mul, pow_add]
  have h2 : q + 2 ≤ 2 ^ (2 * (Nat.log 2 q + 1)) := by
    rw [e]
    nlinarith
  exact Nat.clog_le_of_le_pow h2

/-- The ledger exponent dominates its `r`. -/
theorem ledger_ge (sources : EightSources) (r degree : ℕ) : r ≤ C10PartsSchedule.ledgerExponent sources r degree := by
  unfold C10PartsSchedule.ledgerExponent C10SupplierFuel.stageExponent
  have h := le_max_left (560001 + 4 * (r + 1)) (max (2 * degree + 1 + r + 22) 2)
  omega

/-- **The residue window.** Past an onset, the admission's residue bound `envelope + 1` is below `2^(q − K)`. -/
theorem residue_window (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r L : ℕ)
    (hk : WorkspaceSelectedEntryRuntime.entryDegree sources p ≤ k + 1) :
    ∃ o, ∀ n, o ≤ n →
      WorkspaceSelectedEntryBudget.envelope sources p k r n + 1 ≤
        2 ^ (C10PartsSchedule.widthAt sources k n -
          normalizedLiveCount (C10PartsSchedule.widthAt sources k n) L) := by
  obtain ⟨coef, o0, h0⟩ := WorkspaceSelectedEntryRuntime.entry_bound sources p k r
  refine ⟨max o0 (C10FuelRepin.repinOnset sources k (2*L) 0 (coef+1)), fun n hn => ?_⟩
  have ht := C10FuelEnvelope.polyFuel_le_table sources k (2*L) 0 (coef+1)
    (WorkspaceSelectedEntryRuntime.entryDegree sources p) n (by omega) (le_trans (le_max_right _ _) hn)
  have he := h0 n (le_trans (le_max_left _ _) hn)
  have hK : normalizedLiveCount (C10PartsSchedule.widthAt sources k n) L ≤
      C10PartsSchedule.ledgerExponent sources (2*L) 0 * (Nat.log 2 (C10PartsSchedule.widthAt sources k n) + 1) := by
    have h1 : normalizedLiveCount (C10PartsSchedule.widthAt sources k n) L ≤
        L * logScale (C10PartsSchedule.widthAt sources k n) := min_le_right _ _
    have h2 : logScale (C10PartsSchedule.widthAt sources k n) ≤
        2 * (Nat.log 2 (C10PartsSchedule.widthAt sources k n) + 1) := clog_two_le _
    have h3 := ledger_ge sources (2*L) 0
    calc normalizedLiveCount (C10PartsSchedule.widthAt sources k n) L
        ≤ L * logScale (C10PartsSchedule.widthAt sources k n) := h1
      _ ≤ L * (2 * (Nat.log 2 (C10PartsSchedule.widthAt sources k n) + 1)) := Nat.mul_le_mul_left _ h2
      _ = (2*L) * (Nat.log 2 (C10PartsSchedule.widthAt sources k n) + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ h3
  have hpow : 2 ^ (C10PartsSchedule.widthAt sources k n -
        C10PartsSchedule.ledgerExponent sources (2*L) 0 * (Nat.log 2 (C10PartsSchedule.widthAt sources k n) + 1)) ≤
      2 ^ (C10PartsSchedule.widthAt sources k n - normalizedLiveCount (C10PartsSchedule.widthAt sources k n) L) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpf : WorkspaceSelectedEntryBudget.envelope sources p k r n + 1 ≤
      C10FuelRepin.polyFuel (coef+1) (WorkspaceSelectedEntryRuntime.entryDegree sources p) n := by
    unfold C10FuelRepin.polyFuel
    have h1 : 1 ≤ (n+1) ^ (WorkspaceSelectedEntryRuntime.entryDegree sources p) := Nat.one_le_pow _ _ (by omega)
    nlinarith
  exact hpf.trans (ht.trans hpow)

variable (selector : CyclicChoice.Laws) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)

/-- The site's hierarchy index is past the entry degree. -/
theorem entryDegree_le_kW (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) :
    WorkspaceSelectedEntryRuntime.entryDegree sources p ≤ ParamsV4.kW selector mask packets rows sources gamma hg hh p + 1 := by
  unfold ParamsV4.kW SourceBudget.kSelR SourceParent.kOf ControllerCappedRuntime.hierarchyIndex WorkspaceSelectedEntryRuntime.degree
  exact Nat.le_succ_of_le (le_trans (le_max_left _ _) (le_max_right _ _))

/-- **The reduce term's free onset, instantiated**: the residue window at the site's `kW`, `rBsel`, `LW`. -/
def xtraW : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat :=
  fun mask packets rows s g hg hh p =>
    Classical.choose (residue_window s p (ParamsV4.kW selector mask packets rows s g hg hh p) (SourceSteps.rBsel s p)
      (ParamsV4.LW selector mask packets rows s g hg hh p) (entryDegree_le_kW selector mask packets rows s g hg hh p))

end
end NearCubicWires.SourceSkeleton.ResWin
end

