import Proof.SourceAssembly.SourceSkelFirstW
import Proof.SourceAssembly.SourceStepsCode
import Proof.SourceAssembly.SourceSkelCodeFacts
import Proof.SourceAssembly.SourcePhaseChain
import Proof.SourceAssembly.SourceRestIn4

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
namespace NearCubicWires.SourceSkeleton.KeptW
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsR (gWR)
open NearCubicWires.SourceSkeleton.ParamsV4 (LW fPW sfPW)
open NearCubicWires.SourceSkeleton.Fill (XtraW)
open NearCubicWires.SourceSkeleton.FillV5 NearCubicWires.SourceSkeleton.FirstW
noncomputable section

section kept
variable (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔡" => dSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔇𝔰" => DSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔢" => eSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔬" => PCJda54a286946142d3_BranchPhases.offset sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p)
set_option hygiene false in
local notation "ℭ" => PCJda54a286946142d3_BranchPhases.cache sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p)

def KSite (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) : Fin V → Prop :=
  Rest.srcK4 (d := 𝔡) (eX := (𝔇𝔰).se.extra) (pX := (𝔇𝔰).sp.extra) (gW := (𝔇𝔰).gW)
    (cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode)
    (terminalSite selector xtra mask packets rows sources gamma hg hh p V hV)

/-! ## The kept words -/

def K0Site (V : ℕ) (hV : (𝔡).U ≤ V) (mode : Bool) (frameW qW : List Bool) (cdW : Fin 19 → List Bool)
    (resW : ℕ → List Bool) (Vv NC : ℕ) (x : Fin V) : List Bool :=
  if h : ∃ i, cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode i = x then cdW (Classical.choose h)
  else if x.val = 1 then frameW
  else if x.val = 284 then qW
  else if x.val = 278 then List.replicate Vv true
  else if x.val = 279 then List.replicate Vv false
  else if x = terminalSite selector xtra mask packets rows sources gamma hg hh p V hV then List.replicate NC true
  else resW (x.val - ((𝔡).B + 29 + restPc (𝔇𝔰).se.extra (𝔇𝔰).sp.extra (𝔇𝔰).gW))

end kept

end
end NearCubicWires.SourceSkeleton.KeptW
end

