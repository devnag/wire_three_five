import Proof.Wire_3_5.Recovery.CertSched

/-! # The schedule loop's setup at one width (P3:3818-3822; D1.6, the prefix stage)

Realizes the start of the schedule computation at a width `q` with `L = L(q)`: the loop of M18 starts from
`a₀ = (v−2u)^{16}·L³`, `b₀ = (2v)^{16}` and the counter `1` (`roundCount_sched`), each held on a port padded with `false`
to the value capacity `total`. The setup erases the three ports (base's `RecoveryScratchErase`, driver `1^{total}`) and
writes the three values onto them: `L² = L·L`, `L³ = L²·L` (base's unary product with `DimensionTemplate`'s word of `L`),
`a₀ = L³·(v−2u)^{16}`, and the fixed words `1^{(2v)^{16}}`, `1^1`.

Paper quantity: the loop's initial state `(a₀, b₀, 1)`; **`setupMachine u v`** (17 tapes) and **`setupMachine_ready`**:
from `1^L` and stale ports of length `≤ total` it leaves the ports `1^{a₀}`, `1^{b₀}`, `1^1` padded to `total`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

section Setup
variable (u v : ℕ)

def slotsSE : Fin 5 → Fin 17 := ![1, 2, 3, 4, 5]
def slotsST : Fin 3 → Fin 17 := ![0, 6, 7]
def slotsSP1 : Fin 4 → Fin 17 := ![0, 6, 8, 9]
def slotsSP2 : Fin 4 → Fin 17 := ![8, 6, 10, 11]
def slotsSQ : Fin 2 → Fin 17 := ![12, 13]
def slotsSP3 : Fin 4 → Fin 17 := ![10, 12, 1, 14]
def slotsSB : Fin 2 → Fin 17 := ![2, 15]
def slotsSO : Fin 2 → Fin 17 := ![3, 16]

/-- **The setup machine**: erase the ports, `L² , L³`, `a₀ = L³·(v−2u)^{16}`, `b₀ = (2v)^{16}`, the counter `1`. -/
noncomputable def setupMachine :=
  Composition.machine (RecoveryFocus.machine slotsSE (RecoveryScratchErase.resetMachine 3))
  (Composition.machine (RecoveryFocus.machine slotsST (RepairSource.ProjectionNormalization.DimensionTemplate.machine false))
  (Composition.machine (RecoveryFocus.machine slotsSP1 ClockUnaryProduct.machine)
  (Composition.machine (RecoveryFocus.machine slotsSP2 ClockUnaryProduct.machine)
  (Composition.machine (RecoveryFocus.machine slotsSQ (HierarchyFixedWord.machine
      (CompareMachine.word ((v - 2 * u) ^ 16))))
  (Composition.machine (RecoveryFocus.machine slotsSP3 ClockUnaryProduct.machine)
  (Composition.machine (RecoveryFocus.machine slotsSB (HierarchyFixedWord.machine (List.replicate ((2 * v) ^ 16) true)))
    (RecoveryFocus.machine slotsSO (HierarchyFixedWord.machine [true]))))))))

def setupInput (L : ℕ) (A B E : List Bool) (total capT : ℕ) : Fin 17 → List Bool :=
  ![List.replicate L true, A, B, E, List.replicate total true, List.replicate capT false, [], [], [], [], [], [], [], [],
    [], [], []]

end Setup

end NearCubicWires.WireExponent3_5.Transfer
