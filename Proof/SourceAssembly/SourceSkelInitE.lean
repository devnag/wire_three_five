import Proof.SourceAssembly.SourceInitMasters

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.SupplierEstimator
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.InitE
noncomputable section

/-- The rewind block `278..283`. -/
def m278 {T : Nat} : Fin T → Bool := fun x => decide (278 ≤ x.val ∧ x.val < 284)

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

/-- **The one-time init with the rewind block cleared** (ONE fixed machine per layout and constants). -/
def initMachineE (L C cVc cS cR : ℕ) :=
  Composition.machine
    (Composition.machine
      (Once.onceMachine eR eV L C cVc pl.ds pl.b0 (d.scr pl.hT 11) (d.scr pl.hT 12) pl.mask)
      (CloseoutWitness.SelectedErase.machine (m278 (T := T)) (pl.ds (Dimension.pV eR eV)) pl.b0))
    (RecoveryFocus.machine pl.s2 (InitPost.machine L cS cR))

def initCostE (_pl : Place d eX pX gW eR eV X T) (L C cVc cS cR q b : ℕ) : ℕ :=
  (Once.onceCost eR eV L C cVc q + 1 + (2 * (cVc * RuntimeShape.tableClass L eV q) + 4)) + 1 +
    InitPost.cost L cS cR q b (cVc * RuntimeShape.tableClass L eV q) (Once.Rc eR L C q)

/-- The init with the transfer appended (SI's `init2Machine` over `initMachineE`). -/
def init2MachineE (L C cVc cS cR : ℕ) := Composition.machine (initMachineE pl L C cVc cS cR) pl.xferMachine

def init2CostE (L C cVc cS cR q b : ℕ) : ℕ :=
  initCostE pl L C cVc cS cR q b + 1 + xferCost (Once.Rc eR L C q)

end
end NearCubicWires.SourceSkeleton.InitE
end

