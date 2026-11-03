import Proof.SourceAssembly.MaskSource

section
/- Source body: PCJ38fbfed565f64139_Source.lean; adapted only for the paid mask load. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
namespace RCFive.Source
open PCJc4297ab269d8423a_Source
attribute [local irreducible] P1TopDownPaidPayload.tapes

abbrev PacketLibrary (selector : CyclicChoice.Laws) :=
  (a : DecompositionAlgorithm) → PacketWriter selector a
abbrev RowLibrary (selector : CyclicChoice.Laws) :=
  (a : DecompositionAlgorithm) → (printer : WilliamsAlgorithm) → RowProducer selector a printer


/- Fixed layout and code, with no source length, clause index, request, or receipt parameter. -/
structure SourceCode (mask : MaskProducer) (selector : CyclicChoice.Laws)
 (packets : PacketLibrary selector) (rows : RowLibrary selector)
 (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k r scratch : Nat) (ph : CloseoutRowsOriginalSchedule.Phase) where
  a :
    WilliamsAlgorithm
  prepT :
    Nat
  _hsize :
    scratch = r_tapes a+14+prepT
  sourceTapes :
    Nat
  slots :
    Fin (r_tapes a) → Fin sourceTapes
  _hs :
    ∀ i,(slots i).val=(PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155+i.val
  enc :
    Fin 11 → Fin sourceTapes
  _he :
    ∀ i,(enc i).val=if i.val=5 then (PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155+r_tapes a-5
       else (PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155+r_tapes a+(if i.val<5 then i.val else i.val-1)
  app :
    Fin 6 → Fin sourceTapes
  _ha :
    ∀ i,(app i).val=(![(PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155+r_tapes a+5,(CloseoutFinalC10RetainedPhaseFold.wordSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) ph 81).val,
       (PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155+r_tapes a+10,(CloseoutFinalC10RetainedPhaseFold.wordSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) ph 90).val,(PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155+r_tapes a+11,(PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155+r_tapes a+12] : Fin 6 → Nat) i
  refillCode :
    let packet := packets (decompositionOf sources)
    let row := rows (decompositionOf sources) a
    MaskFamilyCode mask packet row sourceTapes
  firstCode :
    let packet := packets (decompositionOf sources)
    let row := rows (decompositionOf sources) a
    MaskFamilyCode mask packet row (sourceTapes+1)
  _refillSource :
    let refillCycle := refillCode.base.cached
    refillCycle.rewindSlots 0=slots (PCJc4297ab269d8423a_Source.sourcePort a)
  _firstSource :
    let firstCycle := firstCode.base.cached
    firstCycle.rewindSlots 0=(slots (PCJc4297ab269d8423a_Source.sourcePort a)).castAdd 1
  whole :
    Fin (sourceTapes+1) → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)
  _hwhole :
    ∀ i,(whole i).val=i.val


end RCFive.Source
end
