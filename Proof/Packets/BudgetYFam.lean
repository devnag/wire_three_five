import Proof.Packets.BudgetCallRest
import Proof.Packets.BudgetSiteAssembly
import Proof.Packets.BudgetPoly
import Proof.Packets.PacketsMetaCutoffStage

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget
open NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-! ## Closed data: P's cold cache constants, PM/PG's stages -/

/-- P's cold-cache coefficient (`Cold.coldBudget_poly`, POOL-8). -/
def coldC : ℕ := Classical.choose Cold.coldBudget_poly
/-- P's cold-cache exponent. -/
def coldD : ℕ := Classical.choose (Classical.choose_spec Cold.coldBudget_poly)

theorem cold_spec : ∀ (q : ℕ) (x : BinaryCacheColdJoin.Args q), BinaryCacheColdRun.budget x ≤
    coldC * ((exactListWord x.gs).length + x.gs.length + q + 2^x.live.card + 1)^coldD :=
  Classical.choose_spec (Classical.choose_spec Cold.coldBudget_poly)

abbrev seOf (sources : EightSources) : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources)
    (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)) :=
  PacketsMeta.Seed.seedCountStage (decompositionOf sources)

abbrev spOf (sources : EightSources) : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources)
    (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources)) :=
  PacketsGlue.RequestMeta.primeCountStage (decompositionOf sources) (PacketsMeta.cutoffStage (decompositionOf sources))

/-- A per-parameter size-constant family; the last argument is the live scale `L` (AD's header class reads it). -/
abbrev CallKFam : Type :=
  (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ → CallK

section fam
variable {selector : CyclicChoice.Laws} (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (degreeOf targetOf : ParNat) (KF : CallKFam)

/-- The small-size degree covering every small summand of the call. -/
def DmOf (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  (packets (decompositionOf sources)).degree + (rows (decompositionOf sources) (printerOf sources)).degree +
    (betaE (decompositionOf sources) (degreeOf sources gamma hg hh p) + 1)*coldD + (seOf sources).degree +
    (spOf sources).degree + 2*(163+3) + 1

theorem DmOf_spec (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    (packets (decompositionOf sources)).degree ≤ DmOf packets rows degreeOf sources gamma hg hh p ∧
    (rows (decompositionOf sources) (printerOf sources)).degree ≤ DmOf packets rows degreeOf sources gamma hg hh p ∧
    (betaE (decompositionOf sources) (degreeOf sources gamma hg hh p) + 1)*coldD ≤
      DmOf packets rows degreeOf sources gamma hg hh p ∧
    (seOf sources).degree ≤ DmOf packets rows degreeOf sources gamma hg hh p ∧
    (spOf sources).degree ≤ DmOf packets rows degreeOf sources gamma hg hh p ∧
    2*(163+3) ≤ DmOf packets rows degreeOf sources gamma hg hh p ∧ 1 ≤ DmOf packets rows degreeOf sources gamma hg hh p := by
  unfold DmOf; omega

/-- **The refill class family `y`** (coefficients at the live scale `Lf`). -/
def yFam (Lf : ParNat) : ClsFam where
  dP := fun s g hg hh p => (KF s g hg hh p 0).D mask.degree
  hT := fun s g hg hh p => (KF s g hg hh p 0).H (rows (decompositionOf s) (printerOf s)).degree
  hS := fun s g hg hh p L => (KF s g hg hh p L).S
  cP := fun s g hg hh p k =>
    Classical.choose (ycall_cls mask (packets (decompositionOf s)) (rows (decompositionOf s) (printerOf s)) (seOf s) (spOf s)
      (degreeOf s g hg hh p) (targetOf s g hg hh p) coldC coldD cold_spec (KF s g hg hh p (Lf s g hg hh p))
      (DmOf packets rows degreeOf s g hg hh p) (DmOf_spec packets rows degreeOf s g hg hh p)) *
    C10PartsSchedule.widthConst s k ^ ((KF s g hg hh p 0).D mask.degree)
  cT := fun s g hg hh p _ =>
    Classical.choose (Classical.choose_spec (ycall_cls mask (packets (decompositionOf s)) (rows (decompositionOf s) (printerOf s))
      (seOf s) (spOf s) (degreeOf s g hg hh p) (targetOf s g hg hh p) coldC coldD cold_spec (KF s g hg hh p (Lf s g hg hh p))
      (DmOf packets rows degreeOf s g hg hh p) (DmOf_spec packets rows degreeOf s g hg hh p)))
  cS := fun s g hg hh p _ =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec (ycall_cls mask (packets (decompositionOf s))
      (rows (decompositionOf s) (printerOf s)) (seOf s) (spOf s) (degreeOf s g hg hh p) (targetOf s g hg hh p) coldC coldD
      cold_spec (KF s g hg hh p (Lf s g hg hh p)) (DmOf packets rows degreeOf s g hg hh p)
      (DmOf_spec packets rows degreeOf s g hg hh p))))

/-- **The first cycle's `Rc`-free class family `yF0`** (coefficients at the live scale `Lf`). -/
def yF0Fam (Lf : ParNat) : ClsFam where
  dP := fun s g hg hh p => (KF s g hg hh p 0).D mask.degree
  hT := fun s g hg hh p => (KF s g hg hh p 0).H (rows (decompositionOf s) (printerOf s)).degree
  hS := fun s g hg hh p L => (KF s g hg hh p L).S
  cP := fun s g hg hh p k =>
    Classical.choose (yF0call_cls mask (packets (decompositionOf s)) (rows (decompositionOf s) (printerOf s)) (seOf s) (spOf s)
      (degreeOf s g hg hh p) (targetOf s g hg hh p) coldC coldD cold_spec (KF s g hg hh p (Lf s g hg hh p))
      (DmOf packets rows degreeOf s g hg hh p) (DmOf_spec packets rows degreeOf s g hg hh p)) *
    C10PartsSchedule.widthConst s k ^ ((KF s g hg hh p 0).D mask.degree)
  cT := fun s g hg hh p _ =>
    Classical.choose (Classical.choose_spec (yF0call_cls mask (packets (decompositionOf s))
      (rows (decompositionOf s) (printerOf s)) (seOf s) (spOf s) (degreeOf s g hg hh p) (targetOf s g hg hh p) coldC coldD
      cold_spec (KF s g hg hh p (Lf s g hg hh p)) (DmOf packets rows degreeOf s g hg hh p)
      (DmOf_spec packets rows degreeOf s g hg hh p)))
  cS := fun s g hg hh p _ =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec (yF0call_cls mask (packets (decompositionOf s))
      (rows (decompositionOf s) (printerOf s)) (seOf s) (spOf s) (degreeOf s g hg hh p) (targetOf s g hg hh p) coldC coldD
      cold_spec (KF s g hg hh p (Lf s g hg hh p)) (DmOf packets rows degreeOf s g hg hh p)
      (DmOf_spec packets rows degreeOf s g hg hh p))))

end fam

end
end NearCubicWires.SourceBudget
end

