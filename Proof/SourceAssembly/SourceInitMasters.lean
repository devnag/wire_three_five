import Proof.SourceAssembly.SourceInitRun
import Proof.SourceAssembly.SourceRefresh

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.SupplierEstimator
open PCJ1fef9807c6954e94_Native
namespace NearCubicWires.SourceConstruction.InitRun
noncomputable section

/-! ## 1. The transfer machine -/

/-- The four driver heads (`drv 0 1 2 4 = B+15 .. B+18`) move left by one. -/
def backDirs (d : Dims) (T : Nat) : Fin T → HeadMove := fun x =>
  if d.B + 15 ≤ x.val ∧ x.val ≤ d.B + 18 then HeadMove.left else HeadMove.stay

def backM (d : Dims) (T : Nat) := DecompositionCountPosition.move (backDirs d T)

/-- The five master words, in `Inv`'s order `U0, S, Rw, B, v` (`S = cS(V+1)`, `Rw = cR(V+1)`, `B = V+1`, `v = b`). -/
def masterW (L cS cR q b Rc Vv : ℕ) : Fin 5 → List Bool :=
  ![ZeroPadding.pad Rc (List.replicate (U0 L q) true), ZeroPadding.pad Rc (UnaryTemplate.tape (cS*(Vv+1))),
    ZeroPadding.pad Rc (UnaryTemplate.tape (cR*(Vv+1))), ZeroPadding.pad Rc (UnaryTemplate.tape (Vv+1)),
    ZeroPadding.pad Rc (UnaryTemplate.tape b)]

/-- The transfer's cost. -/
def xferCost (Rc : ℕ) : ℕ :=
  1 + 1 + ((2*Rc+4) + 1 + ((2*Rc+4) + 1 + ((2*Rc+4) + 1 + ((2*Rc+4) + 1 + (2*Rc+4)))))

/-- S's layout fact `RestExt2` (ten prologue residents) holds on the init's placement. -/
theorem Place.ext2 {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) :
    d.RestExt2 eX pX gW := ⟨pl.ext.rest, by have := pl.ext.hjunk; omega⟩

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

/-- The copy of target `i` onto master `i`. -/
def saveM (i : Fin 5) :=
  RecoveryFocus.machine (![Dims.rfT pl.ext2 pl.hT i, Dims.mT pl.ext2 pl.hT i, d.scr pl.hT 11, d.scr pl.hT 12] :
    Fin 4 → Fin T) RecoveryBoundedTapeCopy.machine

/-- **The transfer machine**: heads back, then five copies. -/
def xferMachine :=
  Composition.machine (backM d T) (Composition.machine (pl.saveM 0) (Composition.machine (pl.saveM 1)
    (Composition.machine (pl.saveM 2) (Composition.machine (pl.saveM 3) (pl.saveM 4)))))

def init2Cost (L C cVc cS cR q b : ℕ) : ℕ :=
  pl.initCost L C cVc cS cR q b + 1 + xferCost (Once.Rc eR L C q)

/-! ## 2. Values -/


/-! ## 3. The transfer run -/

end Place

/-! ## 4. The exit, in `Inv`'s and the first prologue's terms -/

namespace Place

/-! ## 5. The run -/

end Place

end
end NearCubicWires.SourceConstruction.InitRun
end
