import Proof.SourceAssembly.SourceSkelFinalClose
import Proof.SourceAssembly.SourceStepsSite2
import Proof.SourceAssembly.SourceStepsInv6
import Proof.Packets.SrcLayRows
import Proof.Packets.SrcK0W2

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceSkeleton
open NearCubicWires.SourceSkeleton.FirstW NearCubicWires.SourceStart.EntryW
namespace NearCubicWires.SourceSkeleton.Final
open NearCubicWires.SourceSteps
open NearCubicWires.SourceSkeleton.FirstW NearCubicWires.SourceStart.EntryW
noncomputable section

section close2
variable (selector : CyclicChoice.Laws)

set_option hygiene false in
local notation "CODE" => skelFamilyR mask packets rows (FillV5.resPV5 selector mask packets rows)
  (resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows))
  (ParamsV4.fPW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows)
  (refillFam3 mask packets rows (ParamsR.gWR selector mask packets rows) (FillV5.xRV5 selector mask packets rows) (FillV5.hxRV5 selector mask packets rows) _
    (FirstW.g7OfW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows)) (FirstW.firstW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows)
set_option hygiene false in
local notation "𝔉" => forcedChoices mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows)
set_option hygiene false in
local notation "denI" => (𝔉).capIndex sources gamma hg hh p + 1
set_option hygiene false in
local notation "kI" => kSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "rI" => rSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "resI" => resSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "modeI" => PCJ374c44bb8b7f47d9_.S.mode sources p (denI) (Nat.succ_pos _) kI rI (scrSite selector mask packets rows sources gamma hg hh p) n x bits hp
set_option hygiene false in
local notation "oracleI" => C10TotalDecode.oracleOf sources kI (PolynomialClock.ordinaryClock kI) p.degree n bits
set_option hygiene false in
local notation "coordI" => PCJd04de0277f804fcc_.coordinate sources kI (PolynomialClock.ordinaryClock kI) p (denI) x oracleI bits
set_option hygiene false in
local notation "tgtI" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "LI" => ParamsV4.LW selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "UI" => UOf mask packets rows sources resI p kI rI
set_option hygiene false in
local notation "NCI" => NC sources kI (PolynomialClock.ordinaryClock kI) x oracleI
set_option hygiene false in
local notation "RcI" => Once.Rc (ClassV4.hRx4 selector mask packets rows sources gamma hg hh p) LI 1 (C10PartsSchedule.widthAt sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "VI" => SourceBudget.Params.cVcN selector sources gamma hg hh p *
  RuntimeShape.tableClass LI (SourceBudget.Params.hVN selector sources gamma hg hh p) (C10PartsSchedule.widthAt sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "bI" => C10PartsSchedule.entryWidthSchedule sources kI rI n
set_option hygiene false in
local notation "seI" => (DSite selector mask packets rows sources gamma hg hh p).se
set_option hygiene false in
local notation "spI" => (DSite selector mask packets rows sources gamma hg hh p).sp
set_option hygiene false in
local notation "eI" => eSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "hresI" => resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows) sources gamma hg hh p
set_option hygiene false in
local notation "g7FI" => fun ph' => FirstW.g7OfW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows sources gamma hg hh p modeI ph'
set_option hygiene false in
local notation "preFFI" => fun ph' => FirstW.firstW selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows sources gamma hg hh p modeI ph'
set_option hygiene false in
local notation "siteI" => (CODE).site sources gamma hg hh p
set_option hygiene false in
local notation "EtI" => EWFam selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows (CODE) sources gamma hg hh p n x bits hp
set_option hygiene false in
local notation "EFI" => EFSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) (NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)) mask packets rows sources gamma hg hh p n x bits hp
set_option hygiene false in
local notation "SFI" => ParamsV4.sfPW selector mask packets rows sources gamma hg hh p n x bits ph
set_option hygiene false in
local notation "KI" => KeptW.KSite selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector) mask packets rows sources gamma hg hh p UI (UOf_le mask packets rows sources resI p kI rI) modeI
set_option hygiene false in
local notation "KH0I" => (fun (_ : Fin UI) => (0 : Nat))
set_option hygiene false in
local notation "𝒞I" => skelCodeR mask packets rows sources resI hresI p kI rI ph (refill3 mask packets rows sources resI p kI rI seI spI eI (g7FI ph).2) (preFFI ph)

set_option hygiene false in
local notation "𝔛" => NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector
set_option hygiene false in
local notation "vQI" => (req sources kI (PolynomialClock.ordinaryClock kI) x oracleI).arity
set_option hygiene false in
local notation "capCI" => capC sources kI (PolynomialClock.ordinaryClock kI) x oracleI
set_option hygiene false in
local notation "BTSI" => ControllerSelectedContinuation.bodyTapes sources p kI rI (scratchOf mask packets rows sources resI)

/-- The trivial equation row (the default datum's row). -/
def dfltRow : RepairOrdinary.EquationRow.Input :=
  ⟨0, 0, false, [], by simp, by simp, by simp, by simp⟩

/-- **The default datum** (`TraceNums`/`C2` are generic in it). -/
def dfltD : P1TopDownPaidReusable.Datum := ⟨dfltRow, 0, 0, fun _ _ => 0, fun _ _ => false⟩

/-- `dflt` at the site. -/
def dfltFS (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) (ph : Phase) : P1TopDownPaidReusable.Datum := dfltD

def costFS (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) (ph : Phase) : Nat :=
  NearCubicWires.SourceFactorSel.ClauseCost.Bsplit selector mask packets rows sources gamma hg hh p kI n

/-- The steps guard gives `extraW xtraFin ≤ n`. -/
theorem hextFS (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) : ParamsV4.extraW selector 𝔛 mask packets rows sources gamma hg hh p ≤ n :=
  NearCubicWires.SourceSkeleton.OnsetW.extraW_le_of_onset selector 𝔛 mask packets rows (FillV5.resPV5 selector mask packets rows)
    sources gamma hg hh p ((CODE).site sources gamma hg hh p) n hn

theorem hcutFS (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) : CloseoutWitnessPolicy.inputCutoff sources ≤ n :=
  (NearCubicWires.SourceStart.LayRP.layF_adm selector mask packets rows sources gamma hg hh p 𝔛 n (hextFS selector mask packets rows sources gamma hg hh p n x bits hn hp)).1

theorem hden0FS (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) : SourceSkeleton.layDen0 sources p.clauseDegree tgtI LI ≤ denI :=
  (NearCubicWires.SourceStart.LayRP.layF_adm selector mask packets rows sources gamma hg hh p 𝔛 n (hextFS selector mask packets rows sources gamma hg hh p n x bits hn hp)).2.1

theorem hq0FS (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) : SourceSkeleton.layOnset sources p.clauseDegree tgtI LI ≤ vQI := by
  rw [Admission.req_arity sources kI (PolynomialClock.ordinaryClock kI) x oracleI (hcutFS selector mask packets rows sources gamma hg hh p n x bits hn hp)]
  exact (NearCubicWires.SourceStart.LayRP.layF_adm selector mask packets rows sources gamma hg hh p 𝔛 n (hextFS selector mask packets rows sources gamma hg hh p n x bits hn hp)).2.2

theorem h201FS (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) : 201 * normalizedLiveCount vQI LI ≤ vQI := by
  rw [Admission.req_arity sources kI (PolynomialClock.ordinaryClock kI) x oracleI (hcutFS selector mask packets rows sources gamma hg hh p n x bits hn hp)]
  exact (NearCubicWires.SourceStart.LayRP.layOnW_spec selector mask packets rows sources gamma hg hh p n
    (NearCubicWires.SourceFactorSel.OnsetFin.pastE_layOnW selector mask packets rows sources gamma hg hh p n (hextFS selector mask packets rows sources gamma hg hh p n x bits hn hp))).1

theorem hAFS (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) (ph : Phase) (ci : Fin NCI) (j : Nat) :
    Admission.Admitted (denI) p.clauseDegree (SourceRequest.FactorLoop.factorsAt coordI ph ci j) :=
  SourceSkeleton.admitted_at sources kI (PolynomialClock.ordinaryClock kI) p (denI) x oracleI bits (hcutFS selector mask packets rows sources gamma hg hh p n x bits hn hp) ph ci j

def layFS (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) (ph : Phase) (ci : Fin NCI) : TraceData.LayoutFamily coordI ph ci sources LI tgtI modeI selector :=
  NearCubicWires.SourceStart.LayRP.layF selector sources coordI ph ci LI tgtI modeI
    (SourceBudget.Params.COf selector sources p (C10PartsSchedule.widthAt sources kI n)) p.clauseDegree (denI)
    (hden0FS selector mask packets rows sources gamma hg hh p n x bits hn hp) (hq0FS selector mask packets rows sources gamma hg hh p n x bits hn hp) (hAFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph ci) (h201FS selector mask packets rows sources gamma hg hh p n x bits hn hp)

def K0FS (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hn : (ControllerCappedSelected.workerData sources p ((𝔉).capIndex sources gamma hg hh p+1) (Nat.succ_pos ((𝔉).capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData ((𝔉).capIndex sources gamma hg hh p+1) (ControllerCappedRuntime.continuation sources p ((𝔉).capIndex sources gamma hg hh p+1) ((𝔉).remainingDegree sources gamma hg hh p) ((𝔉).r sources gamma hg hh p) ((𝔉).base sources gamma hg hh p) ((𝔉).scratch sources gamma hg hh p) ((CODE).site sources gamma hg hh p) ((𝔉).remainingFuel sources gamma hg hh p)))).onset ≤ n)
    (hp : P1Independent.CappedLegalAdmission.passed sources p (ControllerCappedSelected.reference (denI) (Nat.succ_pos _) kI (PolynomialClock.ordinaryClock kI))
        (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) (ph : Phase) (ci : Fin NCI) : Fin UI → List Bool :=
  KeptW.K0Site selector 𝔛 mask packets rows sources gamma hg hh p UI (UOf_le mask packets rows sources resI p kI rI) modeI
    (RepairOrdinary.frame bits) (ZeroPadding.pad capCI (SourceSteps.qwordAt sources p kI n x bits ci.val))
    (Function.update (SourceSteps.cdAt sources p kI n x bits ci.val) 15 (List.replicate capCI false))
    (StartGuard.resWSite selector mask packets rows sources gamma hg hh p modeI n bI) VI NCI

set_option hygiene false in
local notation "SPI" => (fun (ci : Fin NCI) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p kI rI (scratchOf mask packets rows sources resI)) → List Bool)
  (H : Fin (ControllerSelectedContinuation.bodyTapes sources p kI rI (scratchOf mask packets rows sources resI)) → Nat) (H1 : Fin (UI + 1) → Nat) (A1 : Fin (UI + 1) → List Bool) =>
  ChainStartP5 mask packets rows sources resI hresI p kI rI ph seI spI eI g7FI preFFI compiler (denI) (Nat.succ_pos _) n x bits hp siteI ci LI RcI
    (InitS.Rk RcI) bI (layFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph ci) KI (K0FS selector mask packets rows sources gamma hg hh p n x bits hn hp ph ci) KH0I VI
    (dfltFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph)
    (fun (_ : Nat) (_ : Fin UI) => (0 : Nat)) (fun (_ : Nat) (_ : Fin UI) => ([] : List Bool))
    (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) RcI
    (costFS selector mask packets rows sources gamma hg hh p n x bits hn hp ph) RcI RcI RcI RcI
    ((A ((𝒞I).whole (Dims.encT (d := dimsOf mask packets rows sources resI p kI rI) (UOf_le mask packets rows sources resI p kI rI) 5).castSucc)).take (InitRun.D0 bI))
    A H H1 A1)

end close2

end
end NearCubicWires.SourceSkeleton.Final
end

