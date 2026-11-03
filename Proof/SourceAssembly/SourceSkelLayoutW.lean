import Proof.SourceAssembly.SourceSkelLayout

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceSkeleton
noncomputable section

section bounded
variable {a : DecompositionAlgorithm} {q L : Nat} {F : Packets.Family q L} {g : Packets.Geometry F}

/-- **The layout with prescribed data at any width `w` above some layout's width, under the load at `w`.** -/
def boundedLayout (w C : Nat) (h : ∃ lay : Packets.Layout a F g, lay.w ≤ w)
    (hload : 200*(normalizedLiveCount q L + w*(normalizedLiveCount q L+2)) ≤ Packets.residual F) : Packets.Layout a F g where
  w := w
  degree := Admission.uniformDeg q L
  C := C
  residualLarge := h.elim fun lay _ => lay.residualLarge
  positiveWidth := h.elim fun lay hw => le_trans lay.positiveWidth hw
  degreeBound := h.elim fun lay _ => fun row hrow =>
    ((Admission.row_degree_lt_w lay row hrow).trans_le (Admission.w_le_uniformDeg lay)).le
  widthFromTouch := h.elim fun lay hw => fun ht row hrow =>
    (lay.widthFromTouch ht row hrow).trans_le (Nat.pow_le_pow_right (by decide) hw)
  load := hload

end bounded

section family
variable (sources : EightSources) (selector : CyclicChoice.Laws)
  {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
  (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
    ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
  (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (L target : Nat) (mode : Bool)

/-- **The layout family at ONE width `wB` for every call** (data `(wB, uniformDeg q L, C)`, all `rfl`). -/
def layOfW (C wB : Nat) (hadm : LayAdm sources selector coordinate ph ci L target mode)
    (hle : ∀ j, Admission.admittedWidth sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j) ≤ wB)
    (hload : 200*(normalizedLiveCount q L + wB*(normalizedLiveCount q L+2)) ≤ q - normalizedLiveCount q L) :
    SourceConstruction.TraceData.LayoutFamily coordinate ph ci sources L target mode selector :=
  fun j => boundedLayout wB C ((hadm j).elim fun lay hw => ⟨lay, hw ▸ hle j⟩) hload


end family

end
end NearCubicWires.SourceSkeleton
end
