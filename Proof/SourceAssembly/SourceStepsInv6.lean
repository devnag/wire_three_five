import Proof.SourceAssembly.SourceStepsParts1

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
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest NearCubicWires.SourceConstruction.Bridge
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section inv6
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)
  (ph : Phase)
  (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)))
  (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources))) {gW : Nat}
  (e : (dimsOf mask packets rows sources res p k r).RestExt3 se.extra sp.extra gW)
  (g7F : Phase → Σ s, Machine (UOf mask packets rows sources res p k r) s)
  (preFF : Phase → Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
  (compiler : Packets.CompilerLaws) (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
  (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) states)
  (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
  (L Rc Rk b : Nat)
  (lay : TraceData.LayoutFamily (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp) selector)
  (K : Fin (UOf mask packets rows sources res p k r) → Prop)
  (K0 : Fin (UOf mask packets rows sources res p k r) → List Bool)
  (KH0 : Fin (UOf mask packets rows sources res p k r) → Nat)
  (V : Nat) (dflt : P1TopDownPaidReusable.Datum) (Dw capw logw resetw : Nat)
  (Hd : Nat → Fin (UOf mask packets rows sources res p k r) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources res p k r) → List Bool)
  (old : Nat → List Bool) (familyCost firstCost counterReserve refillCost : Nat) (cW cQ cB cS : Nat) (N : Nat)
  (H' : Fin (UOf mask packets rows sources res p k r + 1) → Nat) (A' : Fin (UOf mask packets rows sources res p k r + 1) → List Bool)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒽" => UOf_le mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒞" => skelCodeR mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)
set_option hygiene false in
local notation "codeF" => fun ph' => skelCodeR mask packets rows sources res hres p k r ph' (refill3 mask packets rows sources res p k r se sp e (g7F ph').2) (preFF ph')
set_option hygiene false in
local notation "oracleC" => C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x oracleC bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp
set_option hygiene false in
local notation "vQ" => (req sources k (PolynomialClock.ordinaryClock k) x oracleC).arity
set_option hygiene false in
local notation "layA" => layoutAtOf sources selector coordC ph ci L tgtC modeC lay
set_option hygiene false in
local notation "factsA" => factsAtOf sources selector compiler coordC ph ci L tgtC modeC
set_option hygiene false in
local notation "vWS" => P1TopDownPaidReusableReserves.workspace (printerOf sources) V
set_option hygiene false in
local notation "vRW" => P1TopDownPaidReusableReserves.rewind (printerOf sources) V
set_option hygiene false in
local notation "vBF" => P1TopDownPaidReusableReserves.buffer V
set_option hygiene false in
local notation "vMB" => InitRun.Mb L vQ
set_option hygiene false in
local notation "vMS" => InitPost.Ms L vQ
set_option hygiene false in
local notation "vU0" => InitRun.U0 L vQ
set_option hygiene false in
local notation "vdC" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw (oldAt coordC ph ci sources L tgtC modeC b Dw) Hd Ad Rc familyCost refillCost firstCost counterReserve

set_option hygiene false in
local notation "vdX" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve

set_option hygiene false in
local notation "H0cS" => (fun y : Fin (UOf mask packets rows sources res p k r) => H' y.castSucc)
set_option hygiene false in
local notation "A0cS" => chainView 𝒞 b vdX N 0 (fun y : Fin (UOf mask packets rows sources res p k r) => A' y.castSucc)

/-- **The clause chain's invariant, v6** (`seam6_clause`'s, named): `Inv5`'s six conjuncts and (7) the `encT 0..2, 4` lengths at the chain's end. -/
def Inv6 : Nat → (Fin (UOf mask packets rows sources res p k r) → Nat) → (Fin (UOf mask packets rows sources res p k r) → List Bool) → Prop :=
  fun j H A => Rest.InvR e 𝒽 Rc Rk K K0 KH0 j b vQ vMB vMS cW cQ cB cS vWS vRW vBF b vU0 (fuelOf 𝒞 b vdX j) H A ∧
        (∀ z : Fin (UOf mask packets rows sources res p k r), z.val < (𝔇).F →
          Cycle.Free ((𝔇).slot 𝒽) ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).poolSlots 𝒽) ((𝔇).familySlots 𝒽)
            (Dims.rewind2Slots e.ext2.ext1.ext 𝒽) z →
          (∀ i, (𝒞).app i ≠ z) → A z = A0cS z ∧ H z = H0cS z) ∧
        (∀ i, ((𝒞).app i).val < (𝔇).F → H ((𝒞).app i) = H0cS ((𝒞).app i) ∧
          (0 < j → A ((𝒞).app i) = appTOf b vdX (j-1) i)) ∧
        (∀ kk : Fin 13, H (Dims.encT (d := 𝔇) 𝒽 kk) = H0cS (Dims.encT (d := 𝔇) 𝒽 kk)) ∧
        (j < N → (∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).enc i) → A ((𝒞).enc i) = encInOf 𝒞 b vdX j i) ∧
          (∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).app i) → (∀ i', (𝒞).enc i' ≠ (𝒞).app i) → A ((𝒞).app i) = appInOf 𝒞 b vdX j i)) ∧
        (N ≤ j → 0 < j → ∀ kk : Fin 13, (kk.val = 3 ∨ 5 ≤ kk.val) →
          A (Dims.encT (d := 𝔇) 𝒽 kk) = ZeroPadding.pad Rc
            (install (𝒞).app (install (𝒞).enc (fun _ => []) (encWOf b vdX (j-1))) (appTOf b vdX (j-1)) (Dims.encT (d := 𝔇) 𝒽 kk))) ∧
        (N ≤ j → 0 < j → ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → (A (Dims.encT (d := 𝔇) 𝒽 kk)).length ≤ Rc)

set_option hygiene false in
local notation "Inv5S" => Inv5 mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk b lay K K0 KH0 V dflt Dw capw logw resetw Hd Ad old familyCost firstCost counterReserve refillCost cW cQ cB cS N H' A'
set_option hygiene false in
local notation "Inv6S" => Inv6 mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk b lay K K0 KH0 V dflt Dw capw logw resetw Hd Ad old familyCost firstCost counterReserve refillCost cW cQ cB cS N H' A'

end inv6

end
end NearCubicWires.SourceSteps
end

