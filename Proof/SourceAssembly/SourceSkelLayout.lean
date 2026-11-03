import Proof.SourceAssembly.SourceSkelBridge
import Proof.SourceAssembly.AdmissionLayout
import Proof.SourceAssembly.AdmissionDegree
import Proof.SourceAssembly.AdmissionSource

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

section explicit


end explicit

section family
variable (sources : EightSources) (selector : CyclicChoice.Laws)
  {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
  (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
    ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
  (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (L target : Nat) (mode : Bool)

/-- Some layout of call `j`'s family has the admitted width (what `layout_admission` supplies). -/
abbrev LayAdm : Prop :=
  ∀ j : Nat, ∃ lay : Packets.Layout (decompositionOf sources) (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j))
    (Packets.geometry selector (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j))),
    lay.w = Admission.admittedWidth sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)


/-- `factorsAt` IS the `getD` of the monomials' factor lists, at EVERY index (past the end both are `[]`). -/
theorem factorsAt_getD (j : Nat) :
    ((SourceRequest.FactorLoop.monomials coordinate ph ci).map (fun m => m.factors)).getD j [] =
      SourceRequest.FactorLoop.factorsAt coordinate ph ci j := by
  unfold SourceRequest.FactorLoop.factorsAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (SourceRequest.FactorLoop.monomials coordinate ph ci)[j]? <;> rfl

end family

/-- AD's frozen carried-coefficient threshold of `layout_admission` (a maximum fixed before any input, `paper.tex:4288`). -/
def layDen0 (sources : EightSources) (degree target L : Nat) : Nat :=
  Classical.choose (Admission.layout_admission sources degree target L)

/-- AD's frozen arity onset of `layout_admission`. -/
def layOnset (sources : EightSources) (degree target L : Nat) : Nat :=
  Classical.choose (Classical.choose_spec (Admission.layout_admission sources degree target L))

/-- **`hadm` from AD's admission**: past the `(layDen0, layOnset)`, every admitted call has a layout of the admitted width. -/
theorem hadm_of_admission (sources : EightSources) (selector : CyclicChoice.Laws)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (L target : Nat) (mode : Bool)
    (degree den : Nat) (hden : layDen0 sources degree target L ≤ den) (hq : layOnset sources degree target L ≤ q)
    (hA : ∀ j, Admission.Admitted den degree (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)) :
    LayAdm sources selector coordinate ph ci L target mode := by
  intro j
  obtain ⟨lay, _, hw⟩ := Classical.choose_spec (Classical.choose_spec (Admission.layout_admission sources degree target L))
    den hden mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j) hq (hA j)
    (Packets.geometry selector (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j))) 0
  exact ⟨lay, hw⟩

/-- **Every call of the site is admitted** (AD's `trace_atoms_admitted` at `order := monomials`), at every index. -/
theorem admitted_at (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))
    {gamma : Real} (p : Parameters sources gamma) (den : Nat) {n : Nat} (x : BitInput n)
    (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)) (bits : List Bool)
    (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n) (ph : CloseoutRowsOriginalSchedule.Phase)
    (ci : Fin (2^(pcppAt sources k clock x oracle).clauseBits)) (j : Nat) :
    Admission.Admitted den p.clauseDegree
      (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits) ph ci j) := by
  have h := Admission.trace_atoms_admitted sources k clock p den x oracle bits hN ph ci _ (List.Perm.refl _) j
  rw [factorsAt_getD] at h
  exact h

end
end NearCubicWires.SourceSkeleton
end
