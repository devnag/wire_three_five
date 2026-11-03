import Proof.SourceAssembly.SourceDimension

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.SupplierEstimator
namespace NearCubicWires.SourceConstruction.Once
noncomputable section
open Dimension

variable (hR hV : ℕ)

/-- The copier's four tapes: the pipeline's `Rc`, a blank scratch `b0`, the driver, the log. -/
def copySlots {U : ℕ} (ds : Fin (P hR hV) → Fin U) (b0 drv log : Fin U) : Fin 4 → Fin U :=
  ![ds (pR hR hV), b0, drv, log]

/-- The one-time producer (the guard's blank branch). -/
def onceMachine {U : ℕ} (L C cVc : ℕ) (ds : Fin (P hR hV) → Fin U) (b0 drv log : Fin U)
    (mask : Fin U → Bool) :=
  Composition.machine (Composition.machine
    (RecoveryFocus.machine ds (Dimension.machine hR hV L C cVc))
    (RecoveryFocus.machine (copySlots hR hV ds b0 drv log) ClockUnarySum.machine))
    (CloseoutWitness.SelectedErase.machine mask drv log)

/-- The clear capacity. -/
abbrev Rc (L C q : ℕ) : ℕ := C * RuntimeShape.tableClass L hR q

def onceCost (L C cVc q : ℕ) : ℕ :=
  (Dimension.cost hR hV L C cVc q + 1 + (2*Rc hR L C q+6)) + 1 + (2*Rc hR L C q+4)

/-- **Once, table class**: the producer, with its erase and copy, `≤ c·tableClass L (hR+1) q`. -/
theorem onceCost_class (L C cVc q : ℕ) (h2 : 2 ≤ hR) (hVR : hV + 1 ≤ hR) :
    onceCost hR hV L C cVc q ≤
      (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
        BlockPlatform.UnaryCalc.polyCoefficient hV cVc + 300 + 10*C + 6 + 10*cVc + 6 + 2 + 4*C + 12) *
        RuntimeShape.tableClass L (hR+1) q := by
  have hc := Dimension.cost_class hR hV L C cVc q h2 hVR
  have hm : Rc hR L C q ≤ C * RuntimeShape.tableClass L (hR+1) q :=
    Nat.mul_le_mul_left _ (RuntimeShape.tableClass_mono (by omega))
  have hone := SourceConstruction.one_le_tableClass L (hR+1) q
  unfold onceCost
  have e : (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
        BlockPlatform.UnaryCalc.polyCoefficient hV cVc + 300 + 10*C + 6 + 10*cVc + 6 + 2 + 4*C + 12) *
        RuntimeShape.tableClass L (hR+1) q =
      (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
        BlockPlatform.UnaryCalc.polyCoefficient hV cVc + 300 + 10*C + 6 + 10*cVc + 6 + 2) *
        RuntimeShape.tableClass L (hR+1) q + 4*(C * RuntimeShape.tableClass L (hR+1) q) +
        12 * RuntimeShape.tableClass L (hR+1) q := by ring
  rw [e]
  omega

end
end NearCubicWires.SourceConstruction.Once
end
