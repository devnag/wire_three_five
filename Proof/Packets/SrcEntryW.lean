import Proof.SourceAssembly.SourceSkelStartGuard
import Proof.Packets.SrcPen0

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
namespace NearCubicWires.SourceStart.EntryW
open NearCubicWires.SourceSkeleton.KeptW
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsV4
open NearCubicWires.SourceSkeleton.Fill (XtraW)
open NearCubicWires.SourceSkeleton.FillV5 NearCubicWires.SourceSkeleton.FirstW
noncomputable section

section site
variable (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔨" => kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯" => rSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔰" => scrSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔘" => USite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔡" => dSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔇𝔰" => DSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔬" => PCJda54a286946142d3_BranchPhases.offset sources p
  (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p)
set_option hygiene false in
local notation "𝔮" => C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n
set_option hygiene false in
local notation "𝔏" => LW selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "ℜ" => Once.Rc (hRx4 selector mask packets rows sources gamma hg hh p) (LW selector mask packets rows sources gamma hg hh p) 1 (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "𝔙" => SourceBudget.Params.cVcN selector sources gamma hg hh p *
  RuntimeShape.tableClass (LW selector mask packets rows sources gamma hg hh p) (SourceBudget.Params.hVN selector sources gamma hg hh p) (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "𝔒" => C10TotalDecode.oracleOf sources (kSite selector xtra mask packets rows sources gamma hg hh p)
  (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) p.degree n bits
set_option hygiene false in
local notation "ℭ" => PCJda54a286946142d3_BranchPhases.cache sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p)
set_option hygiene false in
local notation "𝔅𝔗" => ControllerSelectedContinuation.bodyTapes sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p)
set_option hygiene false in
local notation "ℭ𝔖" => cacheSite selector xtra mask packets rows sources gamma hg hh p (USite selector xtra mask packets rows sources gamma hg hh p + 1) (Nat.le_succ _)

/-- The site universe `U + 1` IS the body's tape count. -/
theorem U_succ_eq : 𝔘 + 1 = 𝔅𝔗 :=
  dims_U mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p) p 𝔨 𝔯

/-- **`whole`**: the site tape `i` as the body tape `i`. -/
def wholeW : Fin (𝔘 + 1) → Fin 𝔅𝔗 := fun i =>
  ⟨i.val, lt_of_lt_of_eq i.isLt (U_succ_eq selector xtra mask packets rows sources gamma hg hh p)⟩

def KcW (mode : Bool) (y : Fin (𝔘 + 1)) : Prop :=
  KSite selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode y ∧ y ≠ ℭ𝔖 mode 15 ∧
    y ≠ q284Site selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _)

/-- **The K0Site wrapper**: the kept words at clause `ci` (cache = `cdAt ci`, query copy = `pad capC (qwordAt ci)`, tape `1` = `frame bits`,
terminal = `1^NC`, the init's strip words, `Vv = VvOf`; StartGuard's `K0S` at any onset). -/
def K0W (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) : Phase → ℕ → Fin (𝔘 + 1) → List Bool := fun _ ci =>
  K0Site selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode (RepairOrdinary.frame bits)
    (ZeroPadding.pad (capC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒) (SourceSteps.qwordAt sources p 𝔨 n x bits ci))
    (SourceSteps.cdAt sources p 𝔨 n x bits ci)
    (StartGuard.resWSite selector mask packets rows sources gamma hg hh p mode n (C10PartsSchedule.entryWidthSchedule sources 𝔨 𝔯 n)) 𝔙
    (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒)

def EW (mode : Bool) (n : ℕ) (x : BitInput n) (bits : List Bool) : SourceSteps.EntrySite 𝔅𝔗 where
  d := 𝔡
  eX := (𝔇𝔰).se.extra
  pX := (𝔇𝔰).sp.extra
  gW := (𝔇𝔰).gW
  eR := hRx4 selector mask packets rows sources gamma hg hh p
  eV := SourceBudget.Params.hVN selector sources gamma hg hh p
  X := initX (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) sources gamma hg hh p
  T := 𝔘 + 1
  whole := wholeW selector xtra mask packets rows sources gamma hg hh p
  pl := fun ph => plSite selector xtra mask packets rows sources gamma hg hh p mode ph
  e := eSite selector xtra mask packets rows sources gamma hg hh p
  Rc := ℜ
  Rk := InitS.Rk ℜ
  Ce := WorkspaceSelectedEntryBudget.envelope sources p 𝔨 𝔯 n + 1
  Kc := KcW selector xtra mask packets rows sources gamma hg hh p mode
  K0 := K0W selector xtra mask packets rows sources gamma hg hh p mode n x bits
  KH0 := fun _ => 0
  cnt := Fin.last _
  c15 := ℭ𝔖 mode 15
  q284 := q284Site selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _)
  c17 := ℭ𝔖 mode 17
  c18 := ℭ𝔖 mode 18
  b := C10PartsSchedule.entryWidthSchedule sources 𝔨 𝔯 n
  q := (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x 𝔒).arity
  Mb := NearCubicWires.SourceConstruction.InitRun.Mb 𝔏 𝔮
  Ms := NearCubicWires.SourceConstruction.InitPost.Ms 𝔏 𝔮
  S := sC sources gamma hg hh p * (𝔙 + 1)
  Rw := rC sources gamma hg hh p * (𝔙 + 1)
  B := 𝔙 + 1
  U0 := NearCubicWires.SourceConstruction.InitRun.U0 𝔏 𝔮

/-! ## The bridge's ten layout facts -/

set_option hygiene false in
local notation "𝔪" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) n x bits hp
set_option hygiene false in
local notation "ℕℭ" => NC sources (kSite selector xtra mask packets rows sources gamma hg hh p)
  (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) x
  (C10TotalDecode.oracleOf sources (kSite selector xtra mask packets rows sources gamma hg hh p)
    (PolynomialClock.ordinaryClock (kSite selector xtra mask packets rows sources gamma hg hh p)) p.degree n bits)

/-! ## `pen0` at `EW` -/

end site

end
end NearCubicWires.SourceStart.EntryW
end

