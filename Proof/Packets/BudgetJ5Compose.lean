import Proof.SourceAssembly.AdmissionPhase
import Proof.SourceAssembly.SourcePhaseFuel

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.Admission
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule

noncomputable section

structure J5Consts where
  dS : ℕ
  hT : ℕ
  hS : ℕ
  m : ℕ
  L : ℕ
  cP : ℕ
  cT : ℕ
  cS : ℕ
  nC : ℕ
  nE : ℕ
  sC : ℕ
  sE : ℕ
  xC : ℕ
  xE : ℕ
  eC : ℕ
  eE : ℕ
  wC : ℕ
  wE : ℕ

namespace J5Consts
variable (K : J5Consts) (a : RepairRepresentation.PointwisePCPPAlgorithm)

/-- One common source degree dominating every component's. -/
def D : ℕ := K.dS + K.nE + K.sE*PCPPQueryCachedBounds.degree a + 5*K.xE + 2*K.wE + K.eE

/-- The recipe's `remainingDegree`. -/
def degree : ℕ := K.nE + K.D a

/-- The table exponent (the `Split.order` constraint is `tableExp + σ + 2 ≤ L`). -/
def tableExp : ℕ := K.nE + K.hT

def smallExp : ℕ := K.nE + K.hS

/-- One phase's common source-polynomial coefficient (site + PCPP query term + fold + entry). -/
def base : ℕ :=
  K.cP + (4*PCPPQueryCachedBounds.coefficient a*K.sC^PCPPQueryCachedBounds.degree a + 7) +
    3800000*K.xC^5 + K.eC

def phaseP : ℕ := K.base a + K.nC*(K.base a + K.base a + 4*K.nC + 24) + K.base a + 5
def phaseT : ℕ := K.cT + K.nC*(K.cT + K.cT) + K.cT
def phaseS : ℕ := K.cS + K.nC*(K.cS + K.cS) + K.cS

def coefP : ℕ := 3*K.phaseP a + (1000000*K.wC^2 + 5)
def coefT : ℕ := 3*K.phaseT
def coefS : ℕ := 3*K.phaseS

/-- **The J5 right-hand side**: `remainingFuel n := K.fuel a n (q n)`. -/
def fuel (n qn : ℕ) : ℕ :=
  splitRHS (K.degree a) K.tableExp K.smallExp K.m K.L (K.coefP a) K.coefT K.coefS n qn

end J5Consts

/-- **The recipe's `Split`** for `remainingFuel := K.fuel a n (q n)` (`Admission.splitOfRHS`): the bound is
`le_refl`, the source degree is `K.degree a`, and the order is the live scale above the table exponent. -/
def split (K : J5Consts) (a : RepairRepresentation.PointwisePCPPAlgorithm) (σ : ℕ) (q : ℕ → ℕ)
    (hm : 2 ≤ K.m) (horder : K.tableExp + σ + 2 ≤ K.L) :
    RuntimeShape.Split σ q (K.degree a) (fun n => K.fuel a n (q n)) :=
  splitOfRHS σ q (K.degree a) K.tableExp K.smallExp K.m K.L (K.coefP a) K.coefT K.coefS hm horder

end
end NearCubicWires.SourceBudget

