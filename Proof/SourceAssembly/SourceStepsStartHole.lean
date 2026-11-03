import Proof.SourceAssembly.SourceStepsSeam4
import Proof.SourceAssembly.SourceStepsEntryInv3

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

section start
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

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
local notation "vdS" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt (InitRun.D0 b) (InitRun.cap0 b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) (fun j => if j = 0 then w0 else oldAt coordC ph ci sources L tgtC modeC b (InitRun.D0 b) j) Hd Ad Rc familyCost refillCost firstCost counterReserve

def ChainStartP (ph : Phase)
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)))
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources))) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources res p k r) s)
    (preFF : Phase → Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
    (compiler : Packets.CompilerLaws) (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) states)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat) (Rc Rk b : Nat)
    (lay : TraceData.LayoutFamily coordC ph ci sources L tgtC modeC selector)
    (K : Fin (UOf mask packets rows sources res p k r) → Prop)
    (K0 : Fin (UOf mask packets rows sources res p k r) → List Bool)
    (KH0 : Fin (UOf mask packets rows sources res p k r) → Nat)
    (V : Nat) (dflt : P1TopDownPaidReusable.Datum)
    (Hd : Nat → Fin (UOf mask packets rows sources res p k r) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources res p k r) → List Bool)
    (familyCost firstCost counterReserve refillCost : Nat) (cW cQ cB cS : Nat) (w0 : List Bool)
    (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) → Nat)
    (H' : Fin ((𝒞).sourceTapes + 1) → Nat) (A' : Fin ((𝒞).sourceTapes + 1) → List Bool) : Prop :=
  -- (1) the first cycle (E16)
  MaskFamilyCode.Prepared (𝒞).firstCode ((vdS).ds 0) firstCost (fun i => H ((𝒞).whole i)) H'
    (fun i => queriedAt sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ci.val A ((𝒞).whole i)) A' ∧
  -- (2) `first_startV`'s conclusions (E2, E4)
  (∀ i, (fun y => H' y.castSucc) ((𝒞).slots i) = r_inputH (𝒞).a ((vdS).ds 0) ((vdS).S 0) ((vdS).R 0) ((vdS).B 0) ((vdS).xs 0).length i) ∧
  (∀ i, chainView 𝒞 b vdS (vdS).entries.length 0 (fun y => A' y.castSucc) ((𝒞).slots i) =
    r_inputT (𝒞).a ((vdS).ds 0) ((vdS).S 0) ((vdS).R 0) ((vdS).B 0) ((vdS).rowWidth 0) b ((vdS).xs 0).length i) ∧
  Rest.InvR e 𝒽 Rc Rk K K0 KH0 0 b vQ vMB vMS cW cQ cB cS vWS vRW vBF b vU0 (fuelOf 𝒞 b vdS 0) (fun y => H' y.castSucc)
    (chainView 𝒞 b vdS (vdS).entries.length 0 (fun y => A' y.castSucc)) ∧
  (Fin.addCases (fun y : Fin (𝒞).sourceTapes => H' y.castSucc) (fun _ : Fin 1 => (1 : Nat)) : Fin ((𝒞).sourceTapes + 1) → Nat) = H' ∧
  (fun i : Fin ((𝒞).sourceTapes + 1) => ZeroPadding.pad (if i.val = (𝒞).sourceTapes then (vdS).counterReserve else 0)
    ((Fin.addCases (fun y : Fin (𝒞).sourceTapes =>
        ZeroPadding.pad (if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ y.val then (vdS).reserveSize else 0)
          (chainView 𝒞 b vdS (vdS).entries.length 0 (fun z => A' z.castSucc) y))
      (fun _ : Fin 1 => CompareMachine.word (vdS).entries.length) : Fin ((𝒞).sourceTapes + 1) → List Bool) i)) = A' ∧
  -- (3) the seam invariant's words at call `0` (E2)
  (0 < (vdS).entries.length →
    (∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).enc i) →
      chainView 𝒞 b vdS (vdS).entries.length 0 (fun y => A' y.castSucc) ((𝒞).enc i) = encInOf 𝒞 b vdS 0 i) ∧
    (∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).app i) → (∀ i', (𝒞).enc i' ≠ (𝒞).app i) →
      chainView 𝒞 b vdS (vdS).entries.length 0 (fun y => A' y.castSucc) ((𝒞).app i) = appInOf 𝒞 b vdS 0 i)) ∧
  -- (4) the composite frame (D2, D3)
  (∀ y : Fin (𝒞).sourceTapes, y.val < (𝔇).F →
    Cycle.Free ((𝔇).slot 𝒽) ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).poolSlots 𝒽) ((𝔇).familySlots 𝒽)
      (Dims.rewind2Slots e.ext2.ext1.ext 𝒽) y →
    (∀ i, y.val ≠ (PCJda54a286946142d3_BranchPhases.cache sources p k r (scratchOf mask packets rows sources res) modeC i).val) →
    (y.val < 278 ∨ 284 < y.val) →
    A' y.castSucc = queriedAt sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ci.val A ((𝒞).whole y.castSucc) ∧
    H' y.castSucc = H ((𝒞).whole y.castSucc)) ∧
  -- (5) the emitter/appender words and heads on `encT` at the first cycle's exit (the clause's exit when it has no call)
  EncWords (UOf_le_succ mask packets rows sources res p k r) Rc b H' A'

end start

section pen

end pen

end
end NearCubicWires.SourceSteps
end

