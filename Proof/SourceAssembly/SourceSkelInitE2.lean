import Proof.SourceAssembly.SourceSkelInitXA
import Proof.SourceAssembly.SourceSkelInitE

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator RepairRepresentation
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.InitS
noncomputable section

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

/-! ## from `SourceSkelInitS` (E-copies) -/

/-- The composed init on SI's placement: SI's `init2Machine`, then SI's `headM`. -/
def initFME (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target : Nat) :=
  Composition.machine (NearCubicWires.SourceSkeleton.InitE.init2MachineE pl L C cVc cS cR) (pl.headM hh DP CP DW CW DL CL hN mode L target)

/-- **The init on S's port map**: `initFME`, relocated (ONE fixed machine per layout, caps, mode, `L`, `target`, `NR`). -/
def initSMachineE (NR : Nat) (hNR : NR ≤ 32) (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS)
    (mode : Bool) (target : Nat) :=
  RecoveryFocus.machine (InitMove.piF (sb d eX pX gW) X NR T (room pl hh NR hNR))
    (initFME pl hh L C cVc cS cR DP CP DW CW DL CL hN mode target)

/-- Its cost (unchanged by the relocation). -/
def initSCostE (L C cVc cS cR DP CP DW CW DL CL : Nat) (mode : Bool) (target q b : Nat) : Nat :=
  NearCubicWires.SourceSkeleton.InitE.init2CostE pl L C cVc cS cR q b + 1 + Place.headCost DP CP DW CW DL CL mode L target q (Once.Rc eR L C q)

/-! ## from `SourceSkelInitRes` (E-copies) -/

/-- **The init on S's port map with `1^Rk`, `0^(Rk+2)` and `1^D`**: `initS ; rk ; d` (ONE fixed machine). -/
def initRMachineE (NR : Nat) (hNR : NR ≤ 32) {NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target DD CD : Nat)
    (hu : 18 + 14 + 2*DD ≤ NE) :=
  Composition.machine
    (Composition.machine (initSMachineE pl hh NR hNR L C cVc cS cR DP CP DW CW DL CL hN mode target)
      (rkM pl hh hE 0 (by omega)))
    (dM pl hh hE 18 DD CD hu)

def initRCostE (L C cVc cS cR DP CP DW CW DL CL : Nat) (mode : Bool) (target q b DD CD : Nat) : Nat :=
  initSCostE pl L C cVc cS cR DP CP DW CW DL CL mode target q b + 1 + rkCost (Once.Rc eR L C q) + 1 +
    PCPSerializerCapacity.Power.budget DD CD q

/-! ## from `SourceSkelInitAll` (E-copies) -/

/-- **The whole init** (ONE fixed machine). -/
def initAllMachineE (NR : Nat) (hNR : NR ≤ 32) {NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target DD CD Dcw Ccw : Nat)
    (hNE : uAll DD Dcw ≤ NE) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (initRMachineE pl hh NR hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target DD CD (by unfold uAll at hNE; omega))
    (cwM pl hh mode (18 + 14 + 2*DD)))
    (polyResM pl hh hE 9 (by decide) (18 + 14 + 2*DD + 81) Dcw Ccw (by unfold uAll at hNE; omega)))
    (g0M pl hh (18 + 14 + 2*DD + 81 + 14 + 2*Dcw)))
    (g1M pl hh (18 + 14 + 2*DD + 81 + 14 + 2*Dcw + 4))

def initAllCostE (L C cVc cS cR DP CP DW CW DL CL : Nat) (mode : Bool) (target q b DD CD Dcw Ccw : Nat) : Nat :=
  initRCostE pl L C cVc cS cR DP CP DW CW DL CL mode target q b DD CD + 1 + cwCost mode (CL*(q+1)^DL) + 1 +
    PCPSerializerCapacity.Power.budget Dcw Ccw q + 1 + ((2*q+6) + 1 + (2*(q+q)+6)) + 1 +
    ((2 * (List.replicate 2 true).length + 2) + 1 + SourceRequest.CurComp.subCost (InitPost.Ms L q))

/-! ## from `SourceSkelInitXA` (E-copies) -/

def initAllXMachineE (NR : Nat) (hNR : NR ≤ 32) {NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target DD CD Dcw Ccw : Nat)
    (hNE : uAll DD Dcw ≤ NE) {sM : Nat} (M : Machine T sM) :=
  Composition.machine (Composition.machine (Composition.machine
    (initAllMachineE pl hh NR hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target DD CD Dcw Ccw hNE)
    (tkM pl hh (uAll DD Dcw))) (bM pl hh (uAll DD Dcw + 5))) M

/-- The extended init's cost. -/
def initAllXCostE (L C cVc cS cR DP CP DW CW DL CL : Nat) (mode : Bool) (target q b DD CD Dcw Ccw mcost : Nat) : Nat :=
  initAllCostE pl L C cVc cS cR DP CP DW CW DL CL mode target q b DD CD Dcw Ccw + 1 + tkCost (normalizedLiveCount q L) + 1 +
    (2*b+6) + 1 + mcost

/-- **The guarded extended init** (S's guard on the clear driver's cell). -/
def guardAllXE (NR : Nat) (hNR : NR ≤ 32) {NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target DD CD Dcw Ccw : Nat)
    (hNE : uAll DD Dcw ≤ NE) {sM : Nat} (M : Machine T sM) :=
  CloseoutRowsOriginalSwitch.machine (CloseoutRowsOriginalSwitch.stop T)
    (initAllXMachineE pl hh NR hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target DD CD Dcw Ccw hNE M) (d.scr pl.hT 11)

end
end NearCubicWires.SourceSkeleton.InitS
end

