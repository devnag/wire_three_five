import Proof.CaseAnalysis.FinalLedgerBounds
import Proof.CaseAnalysis.FinalCallFuelMono

namespace NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open RepairOrdinary.CloseoutFinalC10StageSeam (dockedFuel)
open RepairOrdinary.CloseoutFinalC10WorkerDock (joinScalarWidth)
open RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  The width, and the two directions it is pinned in -/

/-- The paper's `q(N)`: the selected source's native width at the ordinary clock. -/
def widthAt (sources : EightSources) (k N : ℕ) : ℕ :=
  (outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth N

/-- **The schedule**: a fixed power of `q(N)+1`, i.e. the paper's `q^{O(1)}`
(`paper.tex:1384`). -/
def widthPower (sources : EightSources) (k r N : ℕ) : ℕ := (widthAt sources k N + 1) ^ r

theorem one_le_widthPower (sources : EightSources) (k r N : ℕ) :
    1 ≤ widthPower sources k r N := Nat.one_le_pow _ _ (by omega)

/-- The constant of `nativeWidth_succ_le_logScale`
(`Proof/CaseAnalysis/FinalLedgerBounds.lean`). -/
def widthConst (sources : EightSources) (k : ℕ) : ℕ :=
  ProjectionNormalization.HierarchySourceCost.widthCoefficient (fixedProjection sources)
      (sources.hierarchy (fun n => n ^ (k + 2)) (PolynomialClock.ordinaryClock k)).hierarchy
      (padding sources k (PolynomialClock.ordinaryClock k))
    * (natBitLength
        (sources.hierarchy (fun n => n ^ (k + 2))
          (PolynomialClock.ordinaryClock k)).hierarchy.coefficient + k + 4) + 1

/-- `q(N)+1` is at most a constant times `logScale N` -- LEDGER's bridge, at the
route's own clock. -/
theorem widthAt_succ_le (sources : EightSources) (k N : ℕ) :
    widthAt sources k N + 1 ≤ widthConst sources k * logScale N :=
  C10LedgerBounds.nativeWidth_succ_le_logScale sources k (PolynomialClock.ordinaryClock k) N

/-- **The schedule is polylogarithmic in `N`.**  This is the half of
`q(N) = Theta(log N)` that `hrest` consumes. -/
theorem widthPower_le_logScale (sources : EightSources) (k r N : ℕ) :
    widthPower sources k r N ≤ widthConst sources k ^ r * logScale N ^ r := by
  unfold widthPower
  calc (widthAt sources k N + 1) ^ r ≤ (widthConst sources k * logScale N) ^ r :=
        Nat.pow_le_pow_left (widthAt_succ_le sources k N) r
    _ = widthConst sources k ^ r * logScale N ^ r := mul_pow _ _ _

/-! ## Section 2  The schedule, field by field -/

/-- `StageBlock.hthreshold`'s own demand (`Proof/CaseAnalysis/FinalStageContracts.lean`):
a closed constant of the source. -/
def thresholdFloor (sources : EightSources) : ℕ :=
  C10ThresholdWidths.thresholdWidth (constantsOf sources)

/-- The record width: the threshold floor plus a fixed power of `q(N)`. -/
def entryWidthSchedule (sources : EightSources) (k r N : ℕ) : ℕ :=
  thresholdFloor sources + widthPower sources k r N

def clauseBitsSchedule (sources : EightSources) (k degree N : ℕ) : ℕ :=
  CloseoutLanguage.clauseWidth degree (widthAt sources k N)

/-! ## Section 3  The onset -/

def ledgerExponent (sources : EightSources) (r degree : ℕ) : ℕ :=
  6 + (fixedProjection sources).degrees.proofLog
    + C10SupplierFuel.stageExponent 560001 (4 * (r + 1)) 22 r (2 * degree + 1) + 2

/-- The coefficient of the polylogarithmic envelope of the whole residual bucket. -/
def restCoefficient (sources : EightSources) (k r : ℕ) : ℕ :=
  18600000 * widthConst sources k ^ (5 * (r + 1))

/-- The onset from which the residual bucket is under `N`, from
`SupplierCapacity.coefficient_mul_logScale_pow_eventually_le`
(`Proof/Supplier/SupplierCapacity.lean`). -/
def restOnset (sources : EightSources) (k r : ℕ) : ℕ :=
  Classical.choose (SupplierCapacity.coefficient_mul_logScale_pow_eventually_le
    (restCoefficient sources k r) (5 * (r + 1)))

/-- **The one onset.**  Three demands: A.8's `fullOnset`, the point at which
`q(N)` clears the threshold floor, and the residual bucket's own onset. -/
def partsOnset (sources : EightSources) (k r degree : ℕ) : ℕ :=
  max (2 ^ C10LogFitFull.fullOnset (ledgerExponent sources r degree))
    (max (2 ^ (thresholdFloor sources + 2)) (restOnset sources k r))

theorem width_ge_floor (sources : EightSources) (k r degree N : ℕ)
    (hN : partsOnset sources k r degree ≤ N) :
    thresholdFloor sources + 2 ≤ widthAt sources k N := by
  refine C10LedgerAssembly.nativeWidth_ge sources k (PolynomialClock.ordinaryClock k) _ N ?_
  exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN

/-! ## Section 4  The schedule is under a fixed power of the width -/

/-! ## Section 5  `hdriver`, `hrows`, `hrow` at the schedule -/

/-! ## Section 6  `hrest` -- the loader, the tail and the dock, all under `N` -/

/-! ## Section 7  The `Parts` instance -/

/-! ## Section 9  The payoff -/


end
end NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
