import Proof.SourceAssembly.SourceSkelLoop
import Proof.SourceAssembly.SourceTraceData
import Proof.SourceAssembly.SourceClauseBridge

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
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-- The phase's fixed entry list at live scale `L` (clause-ordered, `SourceTraceData.entriesOf`). -/
abbrev phaseE (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den k : Nat) {n : Nat}
    (x : BitInput n) (bits : List Bool) (mode : Bool) (ph : Phase) (L : Nat) :
    Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) →
      List Stream.Entry :=
  fun c => TraceData.entriesOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph c sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) mode

/-- **The clause's per-call values**, every data field chosen; inputs: the live scale, the admission's layouts and
effective degrees, the resident bound `V`, `dflt`, the uniform record capacities, `old`, the per-call banks, `Rc`, costs. -/
def clauseVals (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (ph : Phase) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat)
    (lay : TraceData.LayoutFamily (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) selector) (deg : Nat → Nat) (V : Nat)
    (dflt : P1TopDownPaidReusable.Datum) (Dw capw logw resetw : Nat) (old : Nat → List Bool)
    (H : Nat → Fin (code ph).sourceTapes → Nat) (A : Nat → Fin (code ph).sourceTapes → List Bool)
    (Rc familyCost refillCost firstCost counterReserve : Nat) :
    RCFive.Source.CallValues (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (code ph).sourceTapes where
  order := TraceData.order (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci
  L := L
  target := (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p))
  dflt := dflt
  ds := TraceData.dsOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) selector compiler lay
  xs := fun j => (TraceData.dsOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) selector compiler lay j).map
    PCJ9eff70d512234a4c_Fixed.datumValue
  S := fun _ => P1TopDownPaidReusableReserves.workspace (code ph).a V
  R := fun _ => P1TopDownPaidReusableReserves.rewind (code ph).a V
  B := fun _ => P1TopDownPaidReusableReserves.buffer V
  rowWidth := TraceData.rowWidthOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) deg
  total := fun j => (TraceData.fractionOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) j).1
  denominator := fun j => (TraceData.fractionOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) j).2
  D := fun _ => Dw
  cap := fun _ => capw
  logSize := fun _ => logw
  resetSize := fun _ => resetw
  coefficient := TraceData.coefficientOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci
  old := old
  phasePrefix := prefixEntries (phaseE sources p den k x bits (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph L) ci.val
  entries := TraceData.entriesOf (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)
  H := H
  A := A
  reserveSize := Rc
  familyCost := familyCost
  refillCost := refillCost
  firstCost := firstCost
  counterReserve := counterReserve

/-- **The site's exit bank** that `SourceTrace._hfinalA` forces, from the clause-start bank and the values. -/
def finalA (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (ph : Phase) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (globalA : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (values : RCFive.Source.CallValues (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (code ph).sourceTapes) : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool :=
    let a := (code ph).a
    let sourceTapes := (code ph).sourceTapes
    let slots := (code ph).slots
    let enc := (code ph).enc
    let app := (code ph).app
    let refillCode := (code ph).refillCode
    let whole := (code ph).whole
    let entries := values.entries
    let H := values.H
    let A := values.A
    let reserveSize := values.reserveSize
    let counterReserve := values.counterReserve
    let refillCycle := refillCode.base.cached
    let refill := PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code refillCycle)
    let reserve := fun (i : Fin sourceTapes) => if ((PCJda54a286946142d3_BranchPhases.offset sources p k r) + 1155) ≤ i.val then reserveSize else 0
    let queried := install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)) globalA
       (PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) ((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))) (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity ci.val
         (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size+(req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity))
         (natListWord [literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))).clauses ci).left,
           literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))).clauses ci).right]))
    let counterCaps : Fin (sourceTapes+1) → Nat := fun i=>if i.val=sourceTapes then counterReserve else 0
    let family := Composition.machine (RecoveryFocus.machine slots (f_machine a))
      (Composition.machine (RecoveryFocus.machine enc e_machine)
        (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
    let padded := fun j i=>ZeroPadding.pad (reserve i) (A j i)
    let body := Composition.machine family refill
    let state := fun j (_out : List Bool)=>(⟨body.start,H j,padded j⟩ : Configuration sourceTapes _)
    install whole queried (fun i=>ZeroPadding.pad (counterCaps i)
        ((RepeatMachine.cfg 3 (state entries.length []) entries.length 1).tapes i))

/-- **The site's exit heads** that `SourceTrace._hfinalH` forces. -/
def finalH (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (ph : Phase) (globalH : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (values : RCFive.Source.CallValues (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (code ph).sourceTapes) : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat :=
    let a := (code ph).a
    let sourceTapes := (code ph).sourceTapes
    let slots := (code ph).slots
    let enc := (code ph).enc
    let app := (code ph).app
    let refillCode := (code ph).refillCode
    let whole := (code ph).whole
    let entries := values.entries
    let H := values.H
    let A := values.A
    let reserveSize := values.reserveSize
    let refillCycle := refillCode.base.cached
    let refill := PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code refillCycle)
    let reserve := fun (i : Fin sourceTapes) => if ((PCJda54a286946142d3_BranchPhases.offset sources p k r) + 1155) ≤ i.val then reserveSize else 0
    let family := Composition.machine (RecoveryFocus.machine slots (f_machine a))
      (Composition.machine (RecoveryFocus.machine enc e_machine)
        (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
    let padded := fun j i=>ZeroPadding.pad (reserve i) (A j i)
    let body := Composition.machine family refill
    let state := fun j (_out : List Bool)=>(⟨body.start,H j,padded j⟩ : Configuration sourceTapes _)
    dockH whole globalH (RepeatMachine.cfg 3 (state entries.length []) entries.length 1).heads

/-! ## The per-clause hole and its assembly -/

section assemble

end assemble

section steps

end steps

end
end NearCubicWires.SourceSkeleton
end
