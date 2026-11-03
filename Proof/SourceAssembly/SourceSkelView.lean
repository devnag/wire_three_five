import Proof.SourceAssembly.SourceSkelGood

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section view
variable {mask : MaskProducer} {selector : CyclicChoice.Laws}
  {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
  {rows : PCJc4297ab269d8423a_Source.RowLibrary selector}
  {sources : EightSources} {gamma : Real} {p : Parameters sources gamma} {k r scratch : Nat} {ph : Phase}
  (code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (b : Nat) {Atom : Type}
  (vd : RCFive.Source.CallValues Atom code.sourceTapes)

/-- `_hfields`' entry-emitter words at call `j` (`old j` is the clause's choice). -/
abbrev encInOf (j : Nat) :=
  e_bank b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩ (vd.D j) (vd.cap j) (vd.old j)

/-- `_hfields`' appender words at call `j`. -/
abbrev appInOf (j : Nat) :=
  CloseoutFinalC10AppendPositioning.tapes b (vd.D j) (vd.logSize j) (vd.resetSize j)
    ⟨vd.coefficient j, vd.total j, vd.denominator j⟩ (vd.phasePrefix ++ vd.entries.take j)

/-- **The chain's call-`j` view of a machine bank `Am`**: exact family input on the slots, exact emitter words on `enc`, exact appender
words on `app`, `Am` elsewhere. -/
def viewOf (j : Nat) (Am : Fin code.sourceTapes → List Bool) : Fin code.sourceTapes → List Bool :=
  install code.slots (install code.enc (install code.app Am (appInOf code b vd j)) (encInOf code b vd j)) (inTOf code b vd j)

/-- **The chain's bank at call `j` for a clause of `M` calls**: the exact view `viewOf` while a call follows (`j < M`); at the loop end
(`M ≤ j`: no `_hfields` there, and the last refill's empty request writes no coefficient words on `enc 0..2`) only the slots are unpadded. -/
def chainView (M j : Nat) (Am : Fin code.sourceTapes → List Bool) : Fin code.sourceTapes → List Bool :=
  if j < M then viewOf code b vd j Am else install code.slots Am (inTOf code b vd j)

end view

end
end NearCubicWires.SourceSkeleton
end
