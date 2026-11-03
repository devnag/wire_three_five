import Proof.SourceAssembly.SourceSkelInitRes

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

section stages
variable {T : Nat}

/-! ## Horner's rule -/

/-- One Horner step `v ↦ v·p + a` on the tapes `Y Lp Cw V' Ls` (template `TP`, shared blank word log `LW`). -/
def hStepM (V TP LW Y Lp Cw V' Ls : Fin T) (a : Nat) :=
  Composition.machine (RecoveryFocus.machine (![V, TP, Y, Lp] : Fin 4 → Fin T) ClockUnaryProduct.machine)
    (Composition.machine
      (RecoveryFocus.machine (![Cw, LW] : Fin 2 → Fin T) (HierarchyFixedWord.machine (List.replicate a true)))
      (RecoveryFocus.machine (![Y, Cw, V', Ls] : Fin 4 → Fin T) ClockUnarySum.machine))

def hStepCost (p v a : Nat) : Nat :=
  (2*(v*(2*p+3)+2)+2) + 1 + ((2 * (List.replicate a true).length + 2) + 1 + (2*(v*p+a)+6))

/-- The chain over the coefficient list (step `i` on `f (u+5i) .. f (u+5i+4)`). -/
def hChain (f : Nat → Fin T) (TP LW : Fin T) : List Nat → Fin T → Nat → (Σ s, Machine T s)
  | [], _, _ => ⟨_, CloseoutRowsOriginalSwitch.stop T⟩
  | a :: cs, V, u => ⟨_, Composition.machine (hStepM V TP LW (f u) (f (u+1)) (f (u+2)) (f (u+3)) (f (u+4)) a)
      (hChain f TP LW cs (f (u+3)) (u+5)).2⟩

def hCost (p : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | a :: cs, v => hStepCost p v a + 1 + hCost p cs (v*p + a)

/-- Horner's value. -/
def hVal (p : Nat) : List Nat → Nat → Nat
  | [], v => v
  | a :: cs, v => hVal p cs (v*p + a)

end stages

end
end NearCubicWires.SourceSkeleton.InitS
end
