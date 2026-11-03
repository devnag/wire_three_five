import Proof.Assembly.NativeNativeSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

namespace PCJ1fef9807c6954e94_Native

noncomputable def sourceProjection (nativeValues : ValuesContract) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
 (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (ci : Fin (2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits))
 (globalH globalHnext : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→Nat)
 (globalA globalAfter : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→List Bool)
 (b siteFuel : Nat) (supplied : NativeSourceSpec sources p k den r scratch clock n x oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel) :
 SourceSpec sources p k r scratch site mode ph (CloseoutLanguage.selectedPCPP sources) (req sources k clock x oracle) ci globalH globalHnext globalA globalAfter b siteFuel := by
 rcases supplied with ⟨order,horder,L,target,a,prepT,hsize,dflt,ds,xs,S,R,B,rowWidth,total,denominator,D,cap,logSize,resetSize,coefficient,old,phasePrefix,entries,hlen,hxs,hcoeff,hnative,U,slots,hs,enc,he,app,ha,H,A,reserveSize,hw,hfit,hH,hA,hc,hold,hl,hr,heH,haH,hfields,familyCost,refillCost,firstCost,refillStates,firstStates,refill,first,whole,hwhole,counterReserve,hcost,hrefill,hfirst,hfinalH,hfinalA,hcode,hbound⟩
 have facts := fun j (hj:j<entries.length) => nativeValues sources L target mode
  ((order.map (fun m=>m.factors)).getD j []) a (S j) (R j) (B j) (rowWidth j) (ds j) (total j) (denominator j) (hnative j hj)
 have hv : ∀ j<entries.length,∀ k (hk:k<(ds j).length),Valid a (B j) (R j) (S j) (ds j)[k] := by
  intro j hj;exact (facts j hj).1
 have hwords : ∀ j<entries.length,(ds j).map Datum.emit=(xs j).map (SignedSortKey.binary (rowWidth j)) := by
  intro j hj;rw [hxs];exact (facts j hj).2.1
 have hx : ∀ j<entries.length,∀ x∈xs j,x<2^(rowWidth j) := by
  intro j hj;rw [hxs];exact (facts j hj).2.2.1
 have hsum : ∀ j<entries.length,(xs j).sum=total j := by
  intro j hj;rw [hxs];exact (facts j hj).2.2.2
 exact ⟨a,prepT,hsize,dflt,ds,xs,S,R,B,rowWidth,total,denominator,D,cap,logSize,resetSize,coefficient,old,phasePrefix,entries,U,slots,hs,enc,he,app,ha,H,A,reserveSize,hv,hwords,hw,hx,hsum,hfit,hH,hA,hc,hold,hl,hr,heH,haH,hfields,familyCost,refillCost,firstCost,refillStates,firstStates,refill,first,whole,hwhole,counterReserve,hcost,hrefill,hfirst,hfinalH,hfinalA,hcode,hbound⟩

end PCJ1fef9807c6954e94_Native
