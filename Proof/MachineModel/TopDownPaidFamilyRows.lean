import Proof.MachineModel.TopDownPaidReusableBinary
import Proof.MachineModel.TopDownPaidReusableParents
import Proof.MachineModel.TopDownPaidReusableCost

/-! Actual SYM/THR row descriptors and literal schedule-to-payload identities.
These are semantic lists, not claimed physical input stream producers. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusable
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open SupplierPipeline SupplierEstimator SupplierPrime SourceInterfaces CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal CloseoutRawRows
open C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow
open C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord
attribute [local irreducible] BinaryPool.pool CompactBounds.radix

section Sym
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (L : Nat) (target : Nat→Nat) (s w degree : Nat)
  (harity : (s+1)/2+s/2=(normalizedLiveSet (symmetricFourfoldOccurrences r) L)ᶜ.card)
  (hs : 67 ≤ s) (hpos : 1 ≤ w)
  (hload : 200*((normalizedLiveSet (symmetricFourfoldOccurrences r) L).card+
    w*((normalizedLiveSet (symmetricFourfoldOccurrences r) L).card+2)) ≤ s)
  (sample : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences r) L (familyDenominator target r))
  (offset : Fin r.circuits.length→Nat)
  (hmon : (CloseoutRowsUniversal.lower a (normalizedLiveSet (symmetricFourfoldOccurrences r) L)
    (symmetricFourfoldOccurrences r) (familyPolynomial L target r sample offset)).length < 2^w)
  (hdegree : RawMonomialDegreeAtMost degree (familyPolynomial L target r sample offset))
  (C : Nat)

noncomputable def symDatum : Datum :=
  binaryDatum a (normalizedLiveSet (symmetricFourfoldOccurrences r) L)
    (symmetricFourfoldOccurrences r) s harity w degree hs hpos hload
    ⟨familyPolynomial L target r sample offset,hmon,hdegree,printerSelect r L s harity offset⟩ C

end Sym

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (L listDen s w degree : Nat)
  (harity : (s+1)/2+s/2=(normalizedLiveSet (thresholdFourfoldOccurrences r) L)ᶜ.card)
  (hs : 67 ≤ s) (hpos : 1 ≤ w)
  (hload : 200*((normalizedLiveSet (thresholdFourfoldOccurrences r) L).card+
    w*((normalizedLiveSet (thresholdFourfoldOccurrences r) L).card+2)) ≤ s)
  {cutoff : Nat} (sel : ThresholdRows.Selection a r) (prime : PrimeIndex cutoff)
  (sample : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) L listDen)
  (offset : Fin prime.val)
  (hmon : (CloseoutRowsUniversal.lower a (normalizedLiveSet (thresholdFourfoldOccurrences r) L)
    (thresholdFourfoldOccurrences r) (thresholdRow a r sel L listDen prime.val offset.val sample)).length < 2^w)
  (hdegree : RawMonomialDegreeAtMost degree (thresholdRow a r sel L listDen prime.val offset.val sample))
  (C : Nat)

noncomputable def thrDatum : Datum :=
  binaryDatum a (normalizedLiveSet (thresholdFourfoldOccurrences r) L)
    (thresholdFourfoldOccurrences r) s harity w degree hs hpos hload
    ⟨thresholdRow a r sel L listDen prime.val offset.val sample,hmon,hdegree,
      fun i j=>decide (thrOffset a r L
        (printerPoint (normalizedLiveSet (thresholdFourfoldOccurrences r) L) s harity i.val j.val)
        sel prime.val=offset.val)⟩ C

end Thr

end NearCubicWires.P1TopDownPaidReusable
