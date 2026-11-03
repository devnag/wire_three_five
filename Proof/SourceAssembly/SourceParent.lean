import Proof.SourceAssembly.SourceParentPhase
import Proof.SourceAssembly.SourceBundle

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceParent
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-! ## `SelectedWitness`: what one `MaskedSelected` still owes -/

/-! ## `SourceContract`: the `Choices` and a witness at every admitted instance -/

/-- The site machine that a fixed `SourceCode` determines: `SourceTrace._hcode`'s left side. -/
def siteOfCode {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma} {k r scratch : Nat}
    {ph : Phase} (code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) :
    Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states :=
  ⟨_, RecoveryFocus.machine code.whole
    (Composition.machine (PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code code.firstCode.base.cached))
      (CloseoutRowsDegreeLoop.machine
        (Composition.machine
          (Composition.machine (RecoveryFocus.machine code.slots (f_machine code.a))
            (Composition.machine (RecoveryFocus.machine code.enc e_machine)
              (RecoveryFocus.machine code.app CloseoutFinalC10SingleAppend.machine)))
          (PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code code.refillCode.base.cached)))))⟩

/-- The hierarchy index the `Choices` fix. -/
abbrev kOf (capIndex remainingDegree : (sources : EightSources) → (gamma : Real) → 0 < gamma →
      gamma < 1/2 → Parameters sources gamma → Nat)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) : Nat :=
  ControllerCappedRuntime.hierarchyIndex sources p (capIndex sources gamma hg hh p+1)
    (remainingDegree sources gamma hg hh p)

/-- The numeric and schedule `Choices` (everything but the site machine). -/
structure SourceChoices where
  capIndex : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  remainingDegree : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  r : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  base : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  scratch : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  remainingFuel : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat → Nat
  widths : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    (p : Parameters sources gamma) → (n : Nat) → BitInput n → List Bool → Phase → Nat
  remainingCoefficient : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  remainingOnset : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  tableCoefficient : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  tableDegree : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat

/-- ONE shared per-clause code per `(mode, phase)`, fixed before `n x bits`
(`paper.tex:4280-4290`); the site machine is DEFINED from it (`siteOfCode`). -/
abbrev CodeFamily (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (ch : SourceChoices) :=
  (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) →
    (p : Parameters sources gamma) → Bool → (ph : Phase) →
    RCFive.Source.SourceCode mask selector packets rows sources p
      (kOf ch.capIndex ch.remainingDegree sources gamma hg hh p) (ch.r sources gamma hg hh p)
      (ch.scratch sources gamma hg hh p) ph

/-- The site family a code family determines. -/
abbrev CodeFamily.site {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {ch : SourceChoices}
    (code : CodeFamily mask selector packets rows ch)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) (mode : Bool) (ph : Phase) :
    Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p
      (kOf ch.capIndex ch.remainingDegree sources gamma hg hh p) (ch.r sources gamma hg hh p)
      (ch.scratch sources gamma hg hh p)) states :=
  siteOfCode (code sources gamma hg hh p mode ph)

end
end NearCubicWires.SourceParent
end
