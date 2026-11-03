import Proof.SourceAssembly.SourceSkelInitAll
import Proof.SourceAssembly.SourceInitSlopes

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

/-! ## 1. `hrG 5 = pad Rc (1^b)` -/

/-- Copy `rsT 3 = pad Rc 1^b` onto strip slot 19 (blank `u`, log `u+1`). -/
def bM (u : Nat) :=
  RecoveryFocus.machine (![Dims.rsT pl.ext.rest pl.hT 3, extF (NS := NS) pl u, stripT pl hh 19 (by decide),
    extF (NS := NS) pl (u+1)] : Fin 4 → Fin T) ClockUnarySum.machine

/-! ## 2. `hrG 2 = pad Rc (tape K)` -/

/-- The fixed word `tape 2` onto `u` (log `u+1`); `hrG 1 / 2` onto `u+2` (log `u+3`); the template of `u+2` onto strip slot 16 (log `u+4`). -/
def tkM (u : Nat) :=
  Composition.machine (Composition.machine
    (RecoveryFocus.machine (![extF (NS := NS) pl u, extF (NS := NS) pl (u+1)] : Fin 2 → Fin T)
      (HierarchyFixedWord.machine (UnaryTemplate.tape 2)))
    (RecoveryFocus.machine (![stripT pl hh 15 (by decide), extF (NS := NS) pl u, extF (NS := NS) pl (u+2),
      extF (NS := NS) pl (u+3)] : Fin 4 → Fin T) MatrixBucketDivide.machine))
    (RecoveryFocus.machine (![extF (NS := NS) pl (u+2), stripT pl hh 16 (by decide), extF (NS := NS) pl (u+4)] : Fin 3 → Fin T)
      (DimensionTemplate.machine false))

/-- The cost of `tkM`. -/
def tkCost (K : Nat) : Nat := (2 * (UnaryTemplate.tape 2).length + 2) + 1 + (8*(2*K)+6) + 1 + (2*K+8)

end
end NearCubicWires.SourceSkeleton.InitS
end

