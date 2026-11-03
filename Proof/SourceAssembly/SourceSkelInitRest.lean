import Proof.SourceAssembly.SourceSkelInitCwid
import Proof.SourceAssembly.SourceRequestCurComp

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

/-! ## 1. `frame` of a unary word -/

theorem frame_ones (k : Nat) : frame (List.replicate k true) = List.replicate (2*k) true ++ [false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    show true :: true :: frame (List.replicate k true) = _
    rw [ih, show 2 * (k+1) = (2*k).succ.succ by omega, List.replicate_succ, List.replicate_succ]
    rfl

theorem pad_frame_ones (Rc k : Nat) (h : 2*k + 1 ≤ Rc) :
    ZeroPadding.pad Rc (frame (List.replicate k true)) = ZeroPadding.pad Rc (List.replicate (2*k) true) := by
  rw [frame_ones, ExtDecompositionBatch.pad_exact, ExtDecompositionBatch.pad_exact]
  simp only [List.length_append, List.length_replicate, List.length_singleton, List.append_assoc]
  congr 1
  rw [show Rc - 2*k = (Rc - (2*k + 1)) + 1 by omega]
  rfl

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

/-! ## 2. A cap `C·(q+1)^D` from `rsT 4` onto any strip slot -/

def polyResM {NE : Nat} (hE : ResExt d eX pX gW X NS NE) (i : Nat) (hi : i < 32) (u Dp Cp : Nat)
    (hu : u + 14 + 2*Dp ≤ NE) :=
  polyAtM (Dims.rsT pl.ext.rest pl.hT 4) (stripT pl hh i hi) (eb d eX pX gW X NS + u) Dp Cp (by
    have := ext_lt pl hE (u + 13 + 2*Dp) (by omega); omega)

/-! ## 3. `hrG 0 = pad Rc (frame 1^q)`: copy `rsT 4`, then sum -/

/-- Copy `rsT 4` onto `u` (blank `u+1`, log `u+2`), then `rsT 4 + u` onto strip slot 14 (log `u+3`). -/
def g0M (u : Nat) :=
  Composition.machine
    (RecoveryFocus.machine (![Dims.rsT pl.ext.rest pl.hT 4, extF (NS := NS) pl u, extF (NS := NS) pl (u+2),
      extF (NS := NS) pl (u+1)] : Fin 4 → Fin T) ClockUnarySum.machine)
    (RecoveryFocus.machine (![Dims.rsT pl.ext.rest pl.hT 4, extF (NS := NS) pl (u+2), stripT pl hh 14 (by decide),
      extF (NS := NS) pl (u+3)] : Fin 4 → Fin T) ClockUnarySum.machine)

/-- The subtraction's dock by value: `0 ↦ rsT 1`, `1 ↦ u` (the `1^2`), `2 ↦` strip slot 15, `j ≥ 3 ↦ u + j - 1`. -/
def subSl (u : Nat) : Fin 9 → Fin T := fun j =>
  if j.val = 0 then Dims.rsT pl.ext.rest pl.hT 1
  else if j.val = 1 then extF (NS := NS) pl u
  else if j.val = 2 then stripT pl hh 15 (by decide)
  else extF (NS := NS) pl (u + j.val - 1)

/-- `1^2` onto `u` (log `u+1`), then `rsT 1 − 1^2` onto strip slot 15. -/
def g1M (u : Nat) :=
  Composition.machine
    (RecoveryFocus.machine (![extF (NS := NS) pl u, extF (NS := NS) pl (u+1)] : Fin 2 → Fin T)
      (HierarchyFixedWord.machine (List.replicate 2 true)))
    (SourceRequest.CurComp.subM (subSl pl hh u))

end
end NearCubicWires.SourceSkeleton.InitS
end
