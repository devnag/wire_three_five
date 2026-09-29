import Proof.Wire_3_5.Recovery.CertWidth

/-! # C6 front, U2: the width's tail `y ↦ y + A_pad⌈log₂(y+2)⌉ + A_pad` (P3:3637-3640)

Realizes the last two terms of "`q(N)=⌈log₂T(N)⌉+A_pad⌈log₂(log₂T(N)+2)⌉+A_pad`" (P3:3637-3640): from `1^y`
(`y = ⌈log₂T(N)⌉`, `Proof.Wire_3_5.UnionMachine.FrontClog`) the machine leaves `1^{y + (⌈log₂(y+2)⌉+1)·A}`.
It is steps 3–9 of `widthMachine` (`Proof.Wire_3_5.Recovery.CertWidth`, which computes the same tail from
`1^{a(k+2)}` at dyadic lengths) run from `1^y` on tape 3: the fixed word `11`, base's `ClockUnarySum` (`y + 2`), the
schedule's `Clog`, `UWalkUnary`, the fixed word `0 1^A`, `UWalkNumbers` product, `ClockUnarySum`. Only the input
differs, so every step is docked exactly as the construction docks it (dock, never rebuild).

Main statement: **`tail_ready`**. Paper quantity: the width's tail `y + A_pad⌈log₂(y+2)⌉ + A_pad`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontWidthTail
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Transfer

variable (A : ℕ)

/-- **The tail machine**: the width steps 3–9 on the 28-tape layout. -/
noncomputable def tailMachine :=
  Composition.machine (RecoveryFocus.machine slotsF2 (HierarchyFixedWord.machine wordTwo))
  (Composition.machine (RecoveryFocus.machine slotsS1 ClockUnarySum.machine)
  (Composition.machine (RecoveryFocus.machine slotsC RepairSource.CloseoutSchedule.Clog.machine)
  (Composition.machine (RecoveryFocus.machine slotsU (UWalkUnary.machine false true))
  (Composition.machine (RecoveryFocus.machine slotsF3 (HierarchyFixedWord.machine (wordA A)))
  (Composition.machine (RecoveryFocus.machine slotsP2 ClockUnaryProduct.machine)
    (RecoveryFocus.machine slotsS2 ClockUnarySum.machine))))))

/-- The input: `1^y` on tape 3. -/
def tailInput (y : ℕ) : Fin 28 → List Bool := fun i => if i.val = 3 then List.replicate y true else []

/-- The tail's value. -/
def tailOf (y : ℕ) : ℕ := y + (Nat.clog 2 (y + 2) + 1) * A

theorem tailOf_eq (y : ℕ) : tailOf A y = y + A * Nat.clog 2 (y + 2) + A := by unfold tailOf; ring

end NearCubicWires.WireExponent3_5.UnionMachine.FrontWidthTail
