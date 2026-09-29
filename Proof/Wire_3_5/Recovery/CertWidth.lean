import Proof.Wire_3_5.Recovery.CertSchedule

/-! # The width `q(2^a)` computed by an ordinary machine (P3:3637-3640, 3738-3741; D1.6, the prefix stage)

Realizes the first arithmetic step of the `E^NP` program's prefix: from the source index `a` (in unary) the program
computes the width `q(N_a) = ⌈log₂ T(N_a)⌉ + A_pad⌈log₂(log₂ T(N_a)+2)⌉ + A_pad` at `N_a = 2^a`, `T(N) = N^{k+2}`
(P3:3637-3640), which is `widthAt k A_pad a = a(k+2) + A_pad⌈log₂(a(k+2)+2)⌉ + A_pad` (`widthAt_eq`), by a
straight line of base's unary machines: fixed words, `ClockUnaryProduct`, `ClockUnarySum`, the schedule's `Clog` and
`UWalkUnary`.

Paper quantities: the width `q(2^a)`; **`widthMachine k A`** on 28 tapes and **`widthMachine_ready`**: from `1^a` on
tape 0 it halts at restored heads with `1^{q(2^a)}` on tape 26 (and `1^a` still on tape 0); and `L(q) = ⌈log₂(q+2)⌉`
(P3:3818-3822's `L`): **`lqMachine`** on 20 tapes and **`lqMachine_ready`** (`1^q` ↦ `1^{L(q)}` on tape 16). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

theorem ready_of_root {t s : ℕ} {p : Machine t s} {n : ℕ} {input output : Fin t → List Bool}
    (h : RecoveryRootRound.ReadyRun p n input output) : ClockJoin.ReadyRun p n input output := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  exact ⟨r, hr, ht, hh, hs.le⟩

section Width
variable (k A : ℕ)

/-- The fixed word `0 1^{k+2}` (the multiplier of `a`). -/
def wordK : List Bool := false :: List.replicate (k + 2) true
/-- The fixed word `1^2`. -/
def wordTwo : List Bool := [true, true]
/-- The fixed word `0 1^{A}` (the multiplier `A_pad`). -/
def wordA : List Bool := false :: List.replicate A true

def slotsF1 : Fin 2 → Fin 28 := ![1, 2]
def slotsP1 : Fin 4 → Fin 28 := ![0, 1, 3, 4]
def slotsF2 : Fin 2 → Fin 28 := ![5, 6]
def slotsS1 : Fin 4 → Fin 28 := ![3, 5, 7, 8]
def slotsC : Fin 12 → Fin 28 := ![7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
def slotsU : Fin 3 → Fin 28 := ![18, 20, 21]
def slotsF3 : Fin 2 → Fin 28 := ![22, 23]
def slotsP2 : Fin 4 → Fin 28 := ![20, 22, 24, 25]
def slotsS2 : Fin 4 → Fin 28 := ![3, 24, 26, 27]

/-- **The width machine**: nine focused steps computing `1^{q(2^a)}` on tape 26 from `1^a` on tape 0. -/
noncomputable def widthMachine :=
  Composition.machine (RecoveryFocus.machine slotsF1 (HierarchyFixedWord.machine (wordK k)))
  (Composition.machine (RecoveryFocus.machine slotsP1 ClockUnaryProduct.machine)
  (Composition.machine (RecoveryFocus.machine slotsF2 (HierarchyFixedWord.machine wordTwo))
  (Composition.machine (RecoveryFocus.machine slotsS1 ClockUnarySum.machine)
  (Composition.machine (RecoveryFocus.machine slotsC RepairSource.CloseoutSchedule.Clog.machine)
  (Composition.machine (RecoveryFocus.machine slotsU (UWalkUnary.machine false true))
  (Composition.machine (RecoveryFocus.machine slotsF3 (HierarchyFixedWord.machine (wordA A)))
  (Composition.machine (RecoveryFocus.machine slotsP2 ClockUnaryProduct.machine)
    (RecoveryFocus.machine slotsS2 ClockUnarySum.machine))))))))

/-- The input: `1^a` on tape 0. -/
def widthInput (a : ℕ) : Fin 28 → List Bool := fun i => if i.val = 0 then List.replicate a true else []

/-- The width's intermediate quantities. -/
def xOf (a : ℕ) : ℕ := a * (k + 2)
def yOf (a : ℕ) : ℕ := Nat.clog 2 (xOf k a + 2)

theorem widthAt_split (a : ℕ) : widthAt k A a = xOf k a + (yOf k a + 1) * A := by
  simp only [widthAt, xOf, yOf]; ring

end Width

/-! ## `L(q) = ⌈log₂(q+2)⌉` -/

section Lq

def slotsLF : Fin 2 → Fin 20 := ![1, 2]
def slotsLS : Fin 4 → Fin 20 := ![0, 1, 3, 4]
def slotsLC : Fin 12 → Fin 20 := ![3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def slotsLU : Fin 3 → Fin 20 := ![14, 16, 17]

/-- **The `L` machine**: from `1^q` on tape 0, `1^{⌈log₂(q+2)⌉}` on tape 16. -/
noncomputable def lqMachine :=
  Composition.machine (RecoveryFocus.machine slotsLF (HierarchyFixedWord.machine wordTwo))
  (Composition.machine (RecoveryFocus.machine slotsLS ClockUnarySum.machine)
  (Composition.machine (RecoveryFocus.machine slotsLC RepairSource.CloseoutSchedule.Clog.machine)
    (RecoveryFocus.machine slotsLU (UWalkUnary.machine false false))))

def lqInput (q : ℕ) : Fin 20 → List Bool := fun i => if i.val = 0 then List.replicate q true else []

end Lq

end NearCubicWires.WireExponent3_5.Transfer
