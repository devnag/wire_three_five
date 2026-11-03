import Proof.SourceAssembly.SourceSkelFillV5
import Proof.SourceAssembly.SourceSkelInitE2
import Proof.SourceAssembly.SourcePhaseFrame
import Proof.SourceAssembly.SourceFirstFront3

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
namespace NearCubicWires.SourceSkeleton.FirstW
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsR (gWR)
open NearCubicWires.SourceSkeleton.ParamsV4 (LW fPW sfPW)
open NearCubicWires.SourceSkeleton.Fill (XtraW)
open NearCubicWires.SourceSkeleton.FillV5
noncomputable section

/-! ## 1. The site at v5 -/

abbrev kSite (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  SourceParent.kOf (fPW selector xtra mask packets rows).capIndex (fPW selector xtra mask packets rows).remainingDegree
    sources gamma hg hh p

abbrev rSite (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  (fPW selector xtra mask packets rows).r sources gamma hg hh p

abbrev DSite (selector : CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    RestData (decompositionOf sources) :=
  restDataOf (gWR selector mask packets rows) sources gamma hg hh p

abbrev resSite (selector : CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  resPV5 selector mask packets rows sources gamma hg hh p

abbrev dSite (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : Dims :=
  dimsOf mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p) p
    (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p)

abbrev scrSite (selector : CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  scratchOf mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p)

/-- The source universe at v5 (`= UAt`). -/
abbrev USite (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  UAt mask packets rows (resPV5 selector mask packets rows) (fPW selector xtra mask packets rows) sources gamma hg hh p

/-- S's twelve-resident extension on the v5 region (as `refillFam3`). -/
theorem eSite (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    (dSite selector xtra mask packets rows sources gamma hg hh p).RestExt3
      (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra
      (DSite selector mask packets rows sources gamma hg hh p).gW :=
  restExt3X mask packets rows sources (DSite selector mask packets rows sources gamma hg hh p)
    (xRV5 selector mask packets rows sources gamma hg hh p) (hxRV5 selector mask packets rows sources gamma hg hh p) p _ _

/-- `F ≤ U` on the v5 layout. -/
theorem F_le_USite (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    (dSite selector xtra mask packets rows sources gamma hg hh p).F ≤ (dSite selector xtra mask packets rows sources gamma hg hh p).U := by
  simp only [Dims.U, Dims.G]
  omega

/-! ## 2. Kept-set tapes on any universe `V ≥ U` -/

/-- The query cache's tape `i` (mode `mode`), as a tape of any universe `V ≥ U`. -/
def cacheSite (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (V : ℕ) (hV : (dSite selector xtra mask packets rows sources gamma hg hh p).U ≤ V) (mode : Bool) (i : Fin 19) : Fin V :=
  ⟨(PCJda54a286946142d3_BranchPhases.cache sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
      (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) mode i).val, by
    have hc := SourcePhase.cache_range sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
      (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) mode i
    have hFU := F_le_USite selector xtra mask packets rows sources gamma hg hh p
    have hF : (dSite selector xtra mask packets rows sources gamma hg hh p).F =
        PCJda54a286946142d3_BranchPhases.offset sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
          (rSite selector xtra mask packets rows sources gamma hg hh p) + 1155 := rfl
    omega⟩

theorem cacheSite_val (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (V : ℕ) (hV : (dSite selector xtra mask packets rows sources gamma hg hh p).U ≤ V) (mode : Bool) (i : Fin 19) :
    (cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode i).val =
      (PCJda54a286946142d3_BranchPhases.cache sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
        (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) mode i).val :=
  rfl

/-- S's `Selected.terminal` (`offset + 53`), as a tape of any universe `V ≥ U`. -/
def terminalSite (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (V : ℕ) (hV : (dSite selector xtra mask packets rows sources gamma hg hh p).U ≤ V) : Fin V :=
  ⟨PCJda54a286946142d3_BranchPhases.offset sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
      (rSite selector xtra mask packets rows sources gamma hg hh p) + 53, by
    have hFU := F_le_USite selector xtra mask packets rows sources gamma hg hh p
    have hF : (dSite selector xtra mask packets rows sources gamma hg hh p).F =
        PCJda54a286946142d3_BranchPhases.offset sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
          (rSite selector xtra mask packets rows sources gamma hg hh p) + 1155 := rfl
    omega⟩

/-- The query copy tape `284`, as a tape of any universe `V ≥ U`. -/
def q284Site (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (V : ℕ) (hV : (dSite selector xtra mask packets rows sources gamma hg hh p).U ≤ V) : Fin V :=
  ⟨284, by
    have hFU := F_le_USite selector xtra mask packets rows sources gamma hg hh p
    have hF : (dSite selector xtra mask packets rows sources gamma hg hh p).F =
        PCJda54a286946142d3_BranchPhases.offset sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
          (rSite selector xtra mask packets rows sources gamma hg hh p) + 1155 := rfl
    have ho := PCJda54a286946142d3_BranchPhases.offset_ge sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
      (rSite selector xtra mask packets rows sources gamma hg hh p)
    omega⟩

/-! ## 3. SI's placement at v5 (first universe `USite + 1`) -/

/-- **The init's placement at the v5 site**: arity template = cache tape 13, phase width = `Wd ph 218`. -/
def plSite (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (mode : Bool) (ph : Phase) :
    Place (dSite selector xtra mask packets rows sources gamma hg hh p)
      (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra
      (DSite selector mask packets rows sources gamma hg hh p).gW
      (hRx4 selector mask packets rows sources gamma hg hh p) (SourceBudget.Params.hVN selector sources gamma hg hh p)
      (initX (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) sources gamma hg hh p)
      (USite selector xtra mask packets rows sources gamma hg hh p + 1) where
  ext := ⟨(eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1, by
      show 32 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra
          (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW +
          initX (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) sources gamma hg hh p ≤
        39 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra
          (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW +
          (xROf (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) sources gamma hg hh p +
            NearCubicWires.SourceStart.MetaStepGF.wMG selector sources p packets (LW selector mask packets rows sources gamma hg hh p))
      unfold xROf
      omega, le_refl _⟩
  hT := Nat.le_succ _
  ar := cacheSite selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode 13
  wd := ⟨(SourceParent.Wd sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
      (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) ph 218).val, by
    have h := (SourceParent.Wd sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
      (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) ph 218).isLt
    have hU := dims_U mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p) p
      (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p)
    exact lt_of_lt_of_eq h hU.symm⟩
  har := by
    have hc := SourcePhase.cache_range sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
      (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) mode 13
    rw [cacheSite_val]
    show _ < PCJda54a286946142d3_BranchPhases.offset sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
      (rSite selector xtra mask packets rows sources gamma hg hh p) + 1155 ∧ _
    omega
  hwd := by
    have h1 := wordSlot_lt sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
      (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) ph 218
    have h2 : SourcePhase.Region (PCJda54a286946142d3_BranchPhases.offset sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
        (rSite selector xtra mask packets rows sources gamma hg hh p)) (SourceParent.Wd sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
        (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) ph 218).val := SourcePhase.wordSlots_region _ _ (PCJda54a286946142d3_BranchPhases.offset_ge sources p
      (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p))
      (PCJda54a286946142d3_BranchPhases.fresh_lt sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
        (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p)) ph 218
    have ho := PCJda54a286946142d3_BranchPhases.offset_ge sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
      (rSite selector xtra mask packets rows sources gamma hg hh p)
    unfold SourcePhase.Region at h2
    show (SourceParent.Wd sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
        (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) ph 218).val < PCJda54a286946142d3_BranchPhases.offset sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
      (rSite selector xtra mask packets rows sources gamma hg hh p) + 1155 ∧ ((SourceParent.Wd sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
        (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) ph 218).val < 278 ∨ 284 ≤ (SourceParent.Wd sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
        (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) ph 218).val)
    exact ⟨h1, by omega⟩
  hne := by
    intro h
    have hv := congrArg Fin.val h
    rw [cacheSite_val] at hv
    have hn := SourcePhase.not_cache sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
      (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) mode
      (SourceParent.Wd sources p (kSite selector xtra mask packets rows sources gamma hg hh p)
        (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) ph 218)
      (SourcePhase.wd_ge_two (sources := sources) (p := p) (k := kSite selector xtra mask packets rows sources gamma hg hh p)
        (r := rSite selector xtra mask packets rows sources gamma hg hh p) (scratch := scrSite selector mask packets rows sources gamma hg hh p)
        ph 218 (by decide))
      (SourcePhase.wordSlots_region _ _ _ _ ph 218) 13
    exact hn (Fin.ext hv.symm)

/-- The header room (`HeadExt` at `NS = initNS`). -/
theorem hhSite (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    InitRun.HeadExt (dSite selector xtra mask packets rows sources gamma hg hh p)
      (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra
      (DSite selector mask packets rows sources gamma hg hh p).gW
      (initX (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) sources gamma hg hh p)
      (initNS sources gamma hg hh p) := ⟨by
  show 64 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra
      (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW +
      initX (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) sources gamma hg hh p +
      initNS sources gamma hg hh p ≤
    39 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra
      (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW +
      (xROf (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) sources gamma hg hh p +
        NearCubicWires.SourceStart.MetaStepGF.wMG selector sources p packets (LW selector mask packets rows sources gamma hg hh p))
  unfold xROf
  omega⟩

/-- The init's extension scratch at v5: `NE = initNE + wMG`. -/
abbrev NESite (selector : CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  initNE sources gamma hg hh p +
    NearCubicWires.SourceStart.MetaStepGF.wMG selector sources p packets (LW selector mask packets rows sources gamma hg hh p)

/-- The extension room (`ResExt` at `NS = initNS`, `NE = NESite`). -/
theorem hESite (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    InitS.ResExt (dSite selector xtra mask packets rows sources gamma hg hh p)
      (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra
      (DSite selector mask packets rows sources gamma hg hh p).gW
      (initX (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) sources gamma hg hh p)
      (initNS sources gamma hg hh p) (NESite selector mask packets rows sources gamma hg hh p) := ⟨by
  show 64 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra
      (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW +
      initX (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) sources gamma hg hh p +
      initNS sources gamma hg hh p + NESite selector mask packets rows sources gamma hg hh p ≤
    39 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra
      (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW +
      (xROf (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) sources gamma hg hh p +
        NearCubicWires.SourceStart.MetaStepGF.wMG selector sources p packets (LW selector mask packets rows sources gamma hg hh p))
  unfold xROf NESite
  omega⟩

theorem hNESite (selector : CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    InitS.uAll (dE sources gamma hg hh p) (cwE sources gamma hg hh p) ≤ NESite selector mask packets rows sources gamma hg hh p := by
  unfold NESite initNE
  omega

abbrev G7W (selector : CyclicChoice.Laws) (xtra : XtraW selector) :=
  ∀ (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (gamma : Real) (hg : 0 < gamma)
    (hh : gamma < 1/2) (p : Parameters sources gamma) (mode : Bool) (ph : Phase) (V : Nat),
    UAt mask packets rows (resPV5 selector mask packets rows) (fPW selector xtra mask packets rows) sources gamma hg hh p ≤ V →
      Σ s, Machine V s

def g7OfW (selector : CyclicChoice.Laws) (xtra : XtraW selector) (G7 : G7W selector xtra) : G7HoleV5 selector xtra :=
  fun mask packets rows sources gamma hg hh p mode ph => G7 mask packets rows sources gamma hg hh p mode ph _ le_rfl

def initW (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (mode : Bool) (ph : Phase) :=
  InitS.guardAllXE (plSite selector xtra mask packets rows sources gamma hg hh p mode ph) (hhSite selector xtra mask packets rows sources gamma hg hh p) initNR (by decide) (hESite selector xtra mask packets rows sources gamma hg hh p)
    (LW selector mask packets rows sources gamma hg hh p) 1 (SourceBudget.Params.cVcN selector sources gamma hg hh p)
    (sC sources gamma hg hh p) (rC sources gamma hg hh p) (pE sources gamma hg hh p) (pC sources gamma hg hh p) 3 1
    (ldE sources gamma hg hh p) (ldC sources gamma hg hh p) (le_refl _) mode (SourceBudget.Params.tgOf sources gamma hg hh p)
    (dE sources gamma hg hh p) (dC sources gamma hg hh p) (cwE sources gamma hg hh p) (cwC sources gamma hg hh p)
    (hNESite selector mask packets rows sources gamma hg hh p)
    (NearCubicWires.SourceStart.MetaStepGF.metaMG (plSite selector xtra mask packets rows sources gamma hg hh p mode ph) (hhSite selector xtra mask packets rows sources gamma hg hh p) selector sources p packets
      (LW selector mask packets rows sources gamma hg hh p) (InitS.uAll (dE sources gamma hg hh p) (cwE sources gamma hg hh p) + 7))

def firstW (selector : CyclicChoice.Laws) (xtra : XtraW selector) (G7 : G7W selector xtra) : FirstHoleV5 selector xtra :=
  fun mask packets rows sources gamma hg hh p mode ph =>
    ⟨_, Rest.firstPro3 (DSite selector mask packets rows sources gamma hg hh p).se (DSite selector mask packets rows sources gamma hg hh p).sp
      (eSite selector xtra mask packets rows sources gamma hg hh p) (Nat.le_succ _) (initW selector xtra mask packets rows sources gamma hg hh p mode ph)
      (G7 mask packets rows sources gamma hg hh p mode ph _ (Nat.le_succ _)).2
      (Fin.last _) (cacheSite selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode 15) (q284Site selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _))
      (cacheSite selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode 17) (cacheSite selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode 18)⟩

end
end NearCubicWires.SourceSkeleton.FirstW
end

