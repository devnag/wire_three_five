import Proof.Wire_3_5.Compiler.MachineTopWrite

/-! # C3 v2 top level, T2: the constant tapes of the compiler stages (P3:1916-1936)

Paper: the stages of alg:compiler (P3:1916-1936) run on registers and templates whose widths are fixed by the
parameters: entries of width `Q' + P_ex + 1` (the thermometer size field, a marker, the mask), the counter of `m` bits
over the `2^m` sub-lists (P3:1918-1920), and the signed fields of `p + 1` bits. This stage writes every constant tape
the compiler stages and the emit stage start from, from the unary parameters loaded by T1 (layout of 33 tapes):
0 `1^{Q'}`, 1 `1^{P_ex}`, 2 `1^m`, 3 `1^{p+1}`, 4 `1^{width}`; 5–13 the nine zero registers `R, R2, R3, X, Y, Gw, Rp, Zu,
Z2u`, 14 the zero template `ZT`; 15 the entry of the empty union, 16 `lastT`, 17 `levelT`, 18 the counter
`frame (binary m 0)`, 19 `frame (1^m)`, 20 the zero field `TZ`, 21 `1^{2·width}`, 22 the empty stack stream; 23–31 the
one-cell flags; 32 the shared log. **`init_run`**: every constant is written and every head is back at cell 0. The
paper quantities are the stages' registers and templates. Main declarations: the slot maps, `initM`, `initCost`,
**`init_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Top
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform

def iZ0 : Fin 4 → Fin 33 := ![0, 1, 5, 32]
def iZ1 : Fin 4 → Fin 33 := ![0, 1, 6, 32]
def iZ2 : Fin 4 → Fin 33 := ![0, 1, 7, 32]
def iZ3 : Fin 4 → Fin 33 := ![0, 1, 8, 32]
def iZ4 : Fin 4 → Fin 33 := ![0, 1, 9, 32]
def iZ5 : Fin 4 → Fin 33 := ![0, 1, 10, 32]
def iZ6 : Fin 4 → Fin 33 := ![0, 1, 11, 32]
def iZ7 : Fin 4 → Fin 33 := ![0, 1, 12, 32]
def iZ8 : Fin 4 → Fin 33 := ![0, 1, 13, 32]
def iZ9 : Fin 4 → Fin 33 := ![0, 1, 14, 32]
def iE : Fin 4 → Fin 33 := ![0, 1, 15, 32]
def iL : Fin 4 → Fin 33 := ![0, 1, 16, 32]
def iV : Fin 4 → Fin 33 := ![0, 1, 17, 32]
def iJ : Fin 3 → Fin 33 := ![2, 18, 32]
def iM : Fin 3 → Fin 33 := ![2, 19, 32]
def iP : Fin 3 → Fin 33 := ![3, 20, 32]
def iW : Fin 3 → Fin 33 := ![4, 21, 32]
def iS : Fin 3 → Fin 33 := ![4, 22, 32]
def iC : Fin 10 → Fin 33 := ![23, 24, 25, 26, 27, 28, 29, 30, 31, 32]

theorem iZ0_inj : Function.Injective iZ0 := by decide

theorem install_iZ0 (A : Fin 33 → List Bool) (v : Fin 4 → List Bool) :
    install iZ0 A v = ![v 0, v 1, A 2, A 3, A 4, v 2, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 3] := by
  funext i
  fin_cases i
  · exact install_slot iZ0 iZ0_inj A v 0
  · exact install_slot iZ0 iZ0_inj A v 1
  · exact install_other iZ0 A v 2 (by decide)
  · exact install_other iZ0 A v 3 (by decide)
  · exact install_other iZ0 A v 4 (by decide)
  · exact install_slot iZ0 iZ0_inj A v 2
  · exact install_other iZ0 A v 6 (by decide)
  · exact install_other iZ0 A v 7 (by decide)
  · exact install_other iZ0 A v 8 (by decide)
  · exact install_other iZ0 A v 9 (by decide)
  · exact install_other iZ0 A v 10 (by decide)
  · exact install_other iZ0 A v 11 (by decide)
  · exact install_other iZ0 A v 12 (by decide)
  · exact install_other iZ0 A v 13 (by decide)
  · exact install_other iZ0 A v 14 (by decide)
  · exact install_other iZ0 A v 15 (by decide)
  · exact install_other iZ0 A v 16 (by decide)
  · exact install_other iZ0 A v 17 (by decide)
  · exact install_other iZ0 A v 18 (by decide)
  · exact install_other iZ0 A v 19 (by decide)
  · exact install_other iZ0 A v 20 (by decide)
  · exact install_other iZ0 A v 21 (by decide)
  · exact install_other iZ0 A v 22 (by decide)
  · exact install_other iZ0 A v 23 (by decide)
  · exact install_other iZ0 A v 24 (by decide)
  · exact install_other iZ0 A v 25 (by decide)
  · exact install_other iZ0 A v 26 (by decide)
  · exact install_other iZ0 A v 27 (by decide)
  · exact install_other iZ0 A v 28 (by decide)
  · exact install_other iZ0 A v 29 (by decide)
  · exact install_other iZ0 A v 30 (by decide)
  · exact install_other iZ0 A v 31 (by decide)
  · exact install_slot iZ0 iZ0_inj A v 3

theorem dockH_iZ0 (H : Fin 33 → ℕ) (v : Fin 4 → ℕ) :
    dockH iZ0 H v = ![v 0, v 1, H 2, H 3, H 4, v 2, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot iZ0 iZ0_inj H v 0
  · exact dockH_slot iZ0 iZ0_inj H v 1
  · exact dockH_other iZ0 H v 2 (by decide)
  · exact dockH_other iZ0 H v 3 (by decide)
  · exact dockH_other iZ0 H v 4 (by decide)
  · exact dockH_slot iZ0 iZ0_inj H v 2
  · exact dockH_other iZ0 H v 6 (by decide)
  · exact dockH_other iZ0 H v 7 (by decide)
  · exact dockH_other iZ0 H v 8 (by decide)
  · exact dockH_other iZ0 H v 9 (by decide)
  · exact dockH_other iZ0 H v 10 (by decide)
  · exact dockH_other iZ0 H v 11 (by decide)
  · exact dockH_other iZ0 H v 12 (by decide)
  · exact dockH_other iZ0 H v 13 (by decide)
  · exact dockH_other iZ0 H v 14 (by decide)
  · exact dockH_other iZ0 H v 15 (by decide)
  · exact dockH_other iZ0 H v 16 (by decide)
  · exact dockH_other iZ0 H v 17 (by decide)
  · exact dockH_other iZ0 H v 18 (by decide)
  · exact dockH_other iZ0 H v 19 (by decide)
  · exact dockH_other iZ0 H v 20 (by decide)
  · exact dockH_other iZ0 H v 21 (by decide)
  · exact dockH_other iZ0 H v 22 (by decide)
  · exact dockH_other iZ0 H v 23 (by decide)
  · exact dockH_other iZ0 H v 24 (by decide)
  · exact dockH_other iZ0 H v 25 (by decide)
  · exact dockH_other iZ0 H v 26 (by decide)
  · exact dockH_other iZ0 H v 27 (by decide)
  · exact dockH_other iZ0 H v 28 (by decide)
  · exact dockH_other iZ0 H v 29 (by decide)
  · exact dockH_other iZ0 H v 30 (by decide)
  · exact dockH_other iZ0 H v 31 (by decide)
  · exact dockH_slot iZ0 iZ0_inj H v 3

theorem iZ1_inj : Function.Injective iZ1 := by decide

theorem install_iZ1 (A : Fin 33 → List Bool) (v : Fin 4 → List Bool) :
    install iZ1 A v = ![v 0, v 1, A 2, A 3, A 4, A 5, v 2, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 3] := by
  funext i
  fin_cases i
  · exact install_slot iZ1 iZ1_inj A v 0
  · exact install_slot iZ1 iZ1_inj A v 1
  · exact install_other iZ1 A v 2 (by decide)
  · exact install_other iZ1 A v 3 (by decide)
  · exact install_other iZ1 A v 4 (by decide)
  · exact install_other iZ1 A v 5 (by decide)
  · exact install_slot iZ1 iZ1_inj A v 2
  · exact install_other iZ1 A v 7 (by decide)
  · exact install_other iZ1 A v 8 (by decide)
  · exact install_other iZ1 A v 9 (by decide)
  · exact install_other iZ1 A v 10 (by decide)
  · exact install_other iZ1 A v 11 (by decide)
  · exact install_other iZ1 A v 12 (by decide)
  · exact install_other iZ1 A v 13 (by decide)
  · exact install_other iZ1 A v 14 (by decide)
  · exact install_other iZ1 A v 15 (by decide)
  · exact install_other iZ1 A v 16 (by decide)
  · exact install_other iZ1 A v 17 (by decide)
  · exact install_other iZ1 A v 18 (by decide)
  · exact install_other iZ1 A v 19 (by decide)
  · exact install_other iZ1 A v 20 (by decide)
  · exact install_other iZ1 A v 21 (by decide)
  · exact install_other iZ1 A v 22 (by decide)
  · exact install_other iZ1 A v 23 (by decide)
  · exact install_other iZ1 A v 24 (by decide)
  · exact install_other iZ1 A v 25 (by decide)
  · exact install_other iZ1 A v 26 (by decide)
  · exact install_other iZ1 A v 27 (by decide)
  · exact install_other iZ1 A v 28 (by decide)
  · exact install_other iZ1 A v 29 (by decide)
  · exact install_other iZ1 A v 30 (by decide)
  · exact install_other iZ1 A v 31 (by decide)
  · exact install_slot iZ1 iZ1_inj A v 3

theorem dockH_iZ1 (H : Fin 33 → ℕ) (v : Fin 4 → ℕ) :
    dockH iZ1 H v = ![v 0, v 1, H 2, H 3, H 4, H 5, v 2, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot iZ1 iZ1_inj H v 0
  · exact dockH_slot iZ1 iZ1_inj H v 1
  · exact dockH_other iZ1 H v 2 (by decide)
  · exact dockH_other iZ1 H v 3 (by decide)
  · exact dockH_other iZ1 H v 4 (by decide)
  · exact dockH_other iZ1 H v 5 (by decide)
  · exact dockH_slot iZ1 iZ1_inj H v 2
  · exact dockH_other iZ1 H v 7 (by decide)
  · exact dockH_other iZ1 H v 8 (by decide)
  · exact dockH_other iZ1 H v 9 (by decide)
  · exact dockH_other iZ1 H v 10 (by decide)
  · exact dockH_other iZ1 H v 11 (by decide)
  · exact dockH_other iZ1 H v 12 (by decide)
  · exact dockH_other iZ1 H v 13 (by decide)
  · exact dockH_other iZ1 H v 14 (by decide)
  · exact dockH_other iZ1 H v 15 (by decide)
  · exact dockH_other iZ1 H v 16 (by decide)
  · exact dockH_other iZ1 H v 17 (by decide)
  · exact dockH_other iZ1 H v 18 (by decide)
  · exact dockH_other iZ1 H v 19 (by decide)
  · exact dockH_other iZ1 H v 20 (by decide)
  · exact dockH_other iZ1 H v 21 (by decide)
  · exact dockH_other iZ1 H v 22 (by decide)
  · exact dockH_other iZ1 H v 23 (by decide)
  · exact dockH_other iZ1 H v 24 (by decide)
  · exact dockH_other iZ1 H v 25 (by decide)
  · exact dockH_other iZ1 H v 26 (by decide)
  · exact dockH_other iZ1 H v 27 (by decide)
  · exact dockH_other iZ1 H v 28 (by decide)
  · exact dockH_other iZ1 H v 29 (by decide)
  · exact dockH_other iZ1 H v 30 (by decide)
  · exact dockH_other iZ1 H v 31 (by decide)
  · exact dockH_slot iZ1 iZ1_inj H v 3

theorem iZ2_inj : Function.Injective iZ2 := by decide

theorem install_iZ2 (A : Fin 33 → List Bool) (v : Fin 4 → List Bool) :
    install iZ2 A v = ![v 0, v 1, A 2, A 3, A 4, A 5, A 6, v 2, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 3] := by
  funext i
  fin_cases i
  · exact install_slot iZ2 iZ2_inj A v 0
  · exact install_slot iZ2 iZ2_inj A v 1
  · exact install_other iZ2 A v 2 (by decide)
  · exact install_other iZ2 A v 3 (by decide)
  · exact install_other iZ2 A v 4 (by decide)
  · exact install_other iZ2 A v 5 (by decide)
  · exact install_other iZ2 A v 6 (by decide)
  · exact install_slot iZ2 iZ2_inj A v 2
  · exact install_other iZ2 A v 8 (by decide)
  · exact install_other iZ2 A v 9 (by decide)
  · exact install_other iZ2 A v 10 (by decide)
  · exact install_other iZ2 A v 11 (by decide)
  · exact install_other iZ2 A v 12 (by decide)
  · exact install_other iZ2 A v 13 (by decide)
  · exact install_other iZ2 A v 14 (by decide)
  · exact install_other iZ2 A v 15 (by decide)
  · exact install_other iZ2 A v 16 (by decide)
  · exact install_other iZ2 A v 17 (by decide)
  · exact install_other iZ2 A v 18 (by decide)
  · exact install_other iZ2 A v 19 (by decide)
  · exact install_other iZ2 A v 20 (by decide)
  · exact install_other iZ2 A v 21 (by decide)
  · exact install_other iZ2 A v 22 (by decide)
  · exact install_other iZ2 A v 23 (by decide)
  · exact install_other iZ2 A v 24 (by decide)
  · exact install_other iZ2 A v 25 (by decide)
  · exact install_other iZ2 A v 26 (by decide)
  · exact install_other iZ2 A v 27 (by decide)
  · exact install_other iZ2 A v 28 (by decide)
  · exact install_other iZ2 A v 29 (by decide)
  · exact install_other iZ2 A v 30 (by decide)
  · exact install_other iZ2 A v 31 (by decide)
  · exact install_slot iZ2 iZ2_inj A v 3

theorem dockH_iZ2 (H : Fin 33 → ℕ) (v : Fin 4 → ℕ) :
    dockH iZ2 H v = ![v 0, v 1, H 2, H 3, H 4, H 5, H 6, v 2, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot iZ2 iZ2_inj H v 0
  · exact dockH_slot iZ2 iZ2_inj H v 1
  · exact dockH_other iZ2 H v 2 (by decide)
  · exact dockH_other iZ2 H v 3 (by decide)
  · exact dockH_other iZ2 H v 4 (by decide)
  · exact dockH_other iZ2 H v 5 (by decide)
  · exact dockH_other iZ2 H v 6 (by decide)
  · exact dockH_slot iZ2 iZ2_inj H v 2
  · exact dockH_other iZ2 H v 8 (by decide)
  · exact dockH_other iZ2 H v 9 (by decide)
  · exact dockH_other iZ2 H v 10 (by decide)
  · exact dockH_other iZ2 H v 11 (by decide)
  · exact dockH_other iZ2 H v 12 (by decide)
  · exact dockH_other iZ2 H v 13 (by decide)
  · exact dockH_other iZ2 H v 14 (by decide)
  · exact dockH_other iZ2 H v 15 (by decide)
  · exact dockH_other iZ2 H v 16 (by decide)
  · exact dockH_other iZ2 H v 17 (by decide)
  · exact dockH_other iZ2 H v 18 (by decide)
  · exact dockH_other iZ2 H v 19 (by decide)
  · exact dockH_other iZ2 H v 20 (by decide)
  · exact dockH_other iZ2 H v 21 (by decide)
  · exact dockH_other iZ2 H v 22 (by decide)
  · exact dockH_other iZ2 H v 23 (by decide)
  · exact dockH_other iZ2 H v 24 (by decide)
  · exact dockH_other iZ2 H v 25 (by decide)
  · exact dockH_other iZ2 H v 26 (by decide)
  · exact dockH_other iZ2 H v 27 (by decide)
  · exact dockH_other iZ2 H v 28 (by decide)
  · exact dockH_other iZ2 H v 29 (by decide)
  · exact dockH_other iZ2 H v 30 (by decide)
  · exact dockH_other iZ2 H v 31 (by decide)
  · exact dockH_slot iZ2 iZ2_inj H v 3

theorem iZ3_inj : Function.Injective iZ3 := by decide

theorem install_iZ3 (A : Fin 33 → List Bool) (v : Fin 4 → List Bool) :
    install iZ3 A v = ![v 0, v 1, A 2, A 3, A 4, A 5, A 6, A 7, v 2, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 3] := by
  funext i
  fin_cases i
  · exact install_slot iZ3 iZ3_inj A v 0
  · exact install_slot iZ3 iZ3_inj A v 1
  · exact install_other iZ3 A v 2 (by decide)
  · exact install_other iZ3 A v 3 (by decide)
  · exact install_other iZ3 A v 4 (by decide)
  · exact install_other iZ3 A v 5 (by decide)
  · exact install_other iZ3 A v 6 (by decide)
  · exact install_other iZ3 A v 7 (by decide)
  · exact install_slot iZ3 iZ3_inj A v 2
  · exact install_other iZ3 A v 9 (by decide)
  · exact install_other iZ3 A v 10 (by decide)
  · exact install_other iZ3 A v 11 (by decide)
  · exact install_other iZ3 A v 12 (by decide)
  · exact install_other iZ3 A v 13 (by decide)
  · exact install_other iZ3 A v 14 (by decide)
  · exact install_other iZ3 A v 15 (by decide)
  · exact install_other iZ3 A v 16 (by decide)
  · exact install_other iZ3 A v 17 (by decide)
  · exact install_other iZ3 A v 18 (by decide)
  · exact install_other iZ3 A v 19 (by decide)
  · exact install_other iZ3 A v 20 (by decide)
  · exact install_other iZ3 A v 21 (by decide)
  · exact install_other iZ3 A v 22 (by decide)
  · exact install_other iZ3 A v 23 (by decide)
  · exact install_other iZ3 A v 24 (by decide)
  · exact install_other iZ3 A v 25 (by decide)
  · exact install_other iZ3 A v 26 (by decide)
  · exact install_other iZ3 A v 27 (by decide)
  · exact install_other iZ3 A v 28 (by decide)
  · exact install_other iZ3 A v 29 (by decide)
  · exact install_other iZ3 A v 30 (by decide)
  · exact install_other iZ3 A v 31 (by decide)
  · exact install_slot iZ3 iZ3_inj A v 3

theorem dockH_iZ3 (H : Fin 33 → ℕ) (v : Fin 4 → ℕ) :
    dockH iZ3 H v = ![v 0, v 1, H 2, H 3, H 4, H 5, H 6, H 7, v 2, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot iZ3 iZ3_inj H v 0
  · exact dockH_slot iZ3 iZ3_inj H v 1
  · exact dockH_other iZ3 H v 2 (by decide)
  · exact dockH_other iZ3 H v 3 (by decide)
  · exact dockH_other iZ3 H v 4 (by decide)
  · exact dockH_other iZ3 H v 5 (by decide)
  · exact dockH_other iZ3 H v 6 (by decide)
  · exact dockH_other iZ3 H v 7 (by decide)
  · exact dockH_slot iZ3 iZ3_inj H v 2
  · exact dockH_other iZ3 H v 9 (by decide)
  · exact dockH_other iZ3 H v 10 (by decide)
  · exact dockH_other iZ3 H v 11 (by decide)
  · exact dockH_other iZ3 H v 12 (by decide)
  · exact dockH_other iZ3 H v 13 (by decide)
  · exact dockH_other iZ3 H v 14 (by decide)
  · exact dockH_other iZ3 H v 15 (by decide)
  · exact dockH_other iZ3 H v 16 (by decide)
  · exact dockH_other iZ3 H v 17 (by decide)
  · exact dockH_other iZ3 H v 18 (by decide)
  · exact dockH_other iZ3 H v 19 (by decide)
  · exact dockH_other iZ3 H v 20 (by decide)
  · exact dockH_other iZ3 H v 21 (by decide)
  · exact dockH_other iZ3 H v 22 (by decide)
  · exact dockH_other iZ3 H v 23 (by decide)
  · exact dockH_other iZ3 H v 24 (by decide)
  · exact dockH_other iZ3 H v 25 (by decide)
  · exact dockH_other iZ3 H v 26 (by decide)
  · exact dockH_other iZ3 H v 27 (by decide)
  · exact dockH_other iZ3 H v 28 (by decide)
  · exact dockH_other iZ3 H v 29 (by decide)
  · exact dockH_other iZ3 H v 30 (by decide)
  · exact dockH_other iZ3 H v 31 (by decide)
  · exact dockH_slot iZ3 iZ3_inj H v 3

theorem iZ4_inj : Function.Injective iZ4 := by decide

theorem install_iZ4 (A : Fin 33 → List Bool) (v : Fin 4 → List Bool) :
    install iZ4 A v = ![v 0, v 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, v 2, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 3] := by
  funext i
  fin_cases i
  · exact install_slot iZ4 iZ4_inj A v 0
  · exact install_slot iZ4 iZ4_inj A v 1
  · exact install_other iZ4 A v 2 (by decide)
  · exact install_other iZ4 A v 3 (by decide)
  · exact install_other iZ4 A v 4 (by decide)
  · exact install_other iZ4 A v 5 (by decide)
  · exact install_other iZ4 A v 6 (by decide)
  · exact install_other iZ4 A v 7 (by decide)
  · exact install_other iZ4 A v 8 (by decide)
  · exact install_slot iZ4 iZ4_inj A v 2
  · exact install_other iZ4 A v 10 (by decide)
  · exact install_other iZ4 A v 11 (by decide)
  · exact install_other iZ4 A v 12 (by decide)
  · exact install_other iZ4 A v 13 (by decide)
  · exact install_other iZ4 A v 14 (by decide)
  · exact install_other iZ4 A v 15 (by decide)
  · exact install_other iZ4 A v 16 (by decide)
  · exact install_other iZ4 A v 17 (by decide)
  · exact install_other iZ4 A v 18 (by decide)
  · exact install_other iZ4 A v 19 (by decide)
  · exact install_other iZ4 A v 20 (by decide)
  · exact install_other iZ4 A v 21 (by decide)
  · exact install_other iZ4 A v 22 (by decide)
  · exact install_other iZ4 A v 23 (by decide)
  · exact install_other iZ4 A v 24 (by decide)
  · exact install_other iZ4 A v 25 (by decide)
  · exact install_other iZ4 A v 26 (by decide)
  · exact install_other iZ4 A v 27 (by decide)
  · exact install_other iZ4 A v 28 (by decide)
  · exact install_other iZ4 A v 29 (by decide)
  · exact install_other iZ4 A v 30 (by decide)
  · exact install_other iZ4 A v 31 (by decide)
  · exact install_slot iZ4 iZ4_inj A v 3

theorem dockH_iZ4 (H : Fin 33 → ℕ) (v : Fin 4 → ℕ) :
    dockH iZ4 H v = ![v 0, v 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, v 2, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot iZ4 iZ4_inj H v 0
  · exact dockH_slot iZ4 iZ4_inj H v 1
  · exact dockH_other iZ4 H v 2 (by decide)
  · exact dockH_other iZ4 H v 3 (by decide)
  · exact dockH_other iZ4 H v 4 (by decide)
  · exact dockH_other iZ4 H v 5 (by decide)
  · exact dockH_other iZ4 H v 6 (by decide)
  · exact dockH_other iZ4 H v 7 (by decide)
  · exact dockH_other iZ4 H v 8 (by decide)
  · exact dockH_slot iZ4 iZ4_inj H v 2
  · exact dockH_other iZ4 H v 10 (by decide)
  · exact dockH_other iZ4 H v 11 (by decide)
  · exact dockH_other iZ4 H v 12 (by decide)
  · exact dockH_other iZ4 H v 13 (by decide)
  · exact dockH_other iZ4 H v 14 (by decide)
  · exact dockH_other iZ4 H v 15 (by decide)
  · exact dockH_other iZ4 H v 16 (by decide)
  · exact dockH_other iZ4 H v 17 (by decide)
  · exact dockH_other iZ4 H v 18 (by decide)
  · exact dockH_other iZ4 H v 19 (by decide)
  · exact dockH_other iZ4 H v 20 (by decide)
  · exact dockH_other iZ4 H v 21 (by decide)
  · exact dockH_other iZ4 H v 22 (by decide)
  · exact dockH_other iZ4 H v 23 (by decide)
  · exact dockH_other iZ4 H v 24 (by decide)
  · exact dockH_other iZ4 H v 25 (by decide)
  · exact dockH_other iZ4 H v 26 (by decide)
  · exact dockH_other iZ4 H v 27 (by decide)
  · exact dockH_other iZ4 H v 28 (by decide)
  · exact dockH_other iZ4 H v 29 (by decide)
  · exact dockH_other iZ4 H v 30 (by decide)
  · exact dockH_other iZ4 H v 31 (by decide)
  · exact dockH_slot iZ4 iZ4_inj H v 3

theorem iZ5_inj : Function.Injective iZ5 := by decide

theorem install_iZ5 (A : Fin 33 → List Bool) (v : Fin 4 → List Bool) :
    install iZ5 A v = ![v 0, v 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, v 2, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 3] := by
  funext i
  fin_cases i
  · exact install_slot iZ5 iZ5_inj A v 0
  · exact install_slot iZ5 iZ5_inj A v 1
  · exact install_other iZ5 A v 2 (by decide)
  · exact install_other iZ5 A v 3 (by decide)
  · exact install_other iZ5 A v 4 (by decide)
  · exact install_other iZ5 A v 5 (by decide)
  · exact install_other iZ5 A v 6 (by decide)
  · exact install_other iZ5 A v 7 (by decide)
  · exact install_other iZ5 A v 8 (by decide)
  · exact install_other iZ5 A v 9 (by decide)
  · exact install_slot iZ5 iZ5_inj A v 2
  · exact install_other iZ5 A v 11 (by decide)
  · exact install_other iZ5 A v 12 (by decide)
  · exact install_other iZ5 A v 13 (by decide)
  · exact install_other iZ5 A v 14 (by decide)
  · exact install_other iZ5 A v 15 (by decide)
  · exact install_other iZ5 A v 16 (by decide)
  · exact install_other iZ5 A v 17 (by decide)
  · exact install_other iZ5 A v 18 (by decide)
  · exact install_other iZ5 A v 19 (by decide)
  · exact install_other iZ5 A v 20 (by decide)
  · exact install_other iZ5 A v 21 (by decide)
  · exact install_other iZ5 A v 22 (by decide)
  · exact install_other iZ5 A v 23 (by decide)
  · exact install_other iZ5 A v 24 (by decide)
  · exact install_other iZ5 A v 25 (by decide)
  · exact install_other iZ5 A v 26 (by decide)
  · exact install_other iZ5 A v 27 (by decide)
  · exact install_other iZ5 A v 28 (by decide)
  · exact install_other iZ5 A v 29 (by decide)
  · exact install_other iZ5 A v 30 (by decide)
  · exact install_other iZ5 A v 31 (by decide)
  · exact install_slot iZ5 iZ5_inj A v 3

theorem dockH_iZ5 (H : Fin 33 → ℕ) (v : Fin 4 → ℕ) :
    dockH iZ5 H v = ![v 0, v 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, v 2, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot iZ5 iZ5_inj H v 0
  · exact dockH_slot iZ5 iZ5_inj H v 1
  · exact dockH_other iZ5 H v 2 (by decide)
  · exact dockH_other iZ5 H v 3 (by decide)
  · exact dockH_other iZ5 H v 4 (by decide)
  · exact dockH_other iZ5 H v 5 (by decide)
  · exact dockH_other iZ5 H v 6 (by decide)
  · exact dockH_other iZ5 H v 7 (by decide)
  · exact dockH_other iZ5 H v 8 (by decide)
  · exact dockH_other iZ5 H v 9 (by decide)
  · exact dockH_slot iZ5 iZ5_inj H v 2
  · exact dockH_other iZ5 H v 11 (by decide)
  · exact dockH_other iZ5 H v 12 (by decide)
  · exact dockH_other iZ5 H v 13 (by decide)
  · exact dockH_other iZ5 H v 14 (by decide)
  · exact dockH_other iZ5 H v 15 (by decide)
  · exact dockH_other iZ5 H v 16 (by decide)
  · exact dockH_other iZ5 H v 17 (by decide)
  · exact dockH_other iZ5 H v 18 (by decide)
  · exact dockH_other iZ5 H v 19 (by decide)
  · exact dockH_other iZ5 H v 20 (by decide)
  · exact dockH_other iZ5 H v 21 (by decide)
  · exact dockH_other iZ5 H v 22 (by decide)
  · exact dockH_other iZ5 H v 23 (by decide)
  · exact dockH_other iZ5 H v 24 (by decide)
  · exact dockH_other iZ5 H v 25 (by decide)
  · exact dockH_other iZ5 H v 26 (by decide)
  · exact dockH_other iZ5 H v 27 (by decide)
  · exact dockH_other iZ5 H v 28 (by decide)
  · exact dockH_other iZ5 H v 29 (by decide)
  · exact dockH_other iZ5 H v 30 (by decide)
  · exact dockH_other iZ5 H v 31 (by decide)
  · exact dockH_slot iZ5 iZ5_inj H v 3

theorem iZ6_inj : Function.Injective iZ6 := by decide

theorem install_iZ6 (A : Fin 33 → List Bool) (v : Fin 4 → List Bool) :
    install iZ6 A v = ![v 0, v 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, v 2, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 3] := by
  funext i
  fin_cases i
  · exact install_slot iZ6 iZ6_inj A v 0
  · exact install_slot iZ6 iZ6_inj A v 1
  · exact install_other iZ6 A v 2 (by decide)
  · exact install_other iZ6 A v 3 (by decide)
  · exact install_other iZ6 A v 4 (by decide)
  · exact install_other iZ6 A v 5 (by decide)
  · exact install_other iZ6 A v 6 (by decide)
  · exact install_other iZ6 A v 7 (by decide)
  · exact install_other iZ6 A v 8 (by decide)
  · exact install_other iZ6 A v 9 (by decide)
  · exact install_other iZ6 A v 10 (by decide)
  · exact install_slot iZ6 iZ6_inj A v 2
  · exact install_other iZ6 A v 12 (by decide)
  · exact install_other iZ6 A v 13 (by decide)
  · exact install_other iZ6 A v 14 (by decide)
  · exact install_other iZ6 A v 15 (by decide)
  · exact install_other iZ6 A v 16 (by decide)
  · exact install_other iZ6 A v 17 (by decide)
  · exact install_other iZ6 A v 18 (by decide)
  · exact install_other iZ6 A v 19 (by decide)
  · exact install_other iZ6 A v 20 (by decide)
  · exact install_other iZ6 A v 21 (by decide)
  · exact install_other iZ6 A v 22 (by decide)
  · exact install_other iZ6 A v 23 (by decide)
  · exact install_other iZ6 A v 24 (by decide)
  · exact install_other iZ6 A v 25 (by decide)
  · exact install_other iZ6 A v 26 (by decide)
  · exact install_other iZ6 A v 27 (by decide)
  · exact install_other iZ6 A v 28 (by decide)
  · exact install_other iZ6 A v 29 (by decide)
  · exact install_other iZ6 A v 30 (by decide)
  · exact install_other iZ6 A v 31 (by decide)
  · exact install_slot iZ6 iZ6_inj A v 3

theorem dockH_iZ6 (H : Fin 33 → ℕ) (v : Fin 4 → ℕ) :
    dockH iZ6 H v = ![v 0, v 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, v 2, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot iZ6 iZ6_inj H v 0
  · exact dockH_slot iZ6 iZ6_inj H v 1
  · exact dockH_other iZ6 H v 2 (by decide)
  · exact dockH_other iZ6 H v 3 (by decide)
  · exact dockH_other iZ6 H v 4 (by decide)
  · exact dockH_other iZ6 H v 5 (by decide)
  · exact dockH_other iZ6 H v 6 (by decide)
  · exact dockH_other iZ6 H v 7 (by decide)
  · exact dockH_other iZ6 H v 8 (by decide)
  · exact dockH_other iZ6 H v 9 (by decide)
  · exact dockH_other iZ6 H v 10 (by decide)
  · exact dockH_slot iZ6 iZ6_inj H v 2
  · exact dockH_other iZ6 H v 12 (by decide)
  · exact dockH_other iZ6 H v 13 (by decide)
  · exact dockH_other iZ6 H v 14 (by decide)
  · exact dockH_other iZ6 H v 15 (by decide)
  · exact dockH_other iZ6 H v 16 (by decide)
  · exact dockH_other iZ6 H v 17 (by decide)
  · exact dockH_other iZ6 H v 18 (by decide)
  · exact dockH_other iZ6 H v 19 (by decide)
  · exact dockH_other iZ6 H v 20 (by decide)
  · exact dockH_other iZ6 H v 21 (by decide)
  · exact dockH_other iZ6 H v 22 (by decide)
  · exact dockH_other iZ6 H v 23 (by decide)
  · exact dockH_other iZ6 H v 24 (by decide)
  · exact dockH_other iZ6 H v 25 (by decide)
  · exact dockH_other iZ6 H v 26 (by decide)
  · exact dockH_other iZ6 H v 27 (by decide)
  · exact dockH_other iZ6 H v 28 (by decide)
  · exact dockH_other iZ6 H v 29 (by decide)
  · exact dockH_other iZ6 H v 30 (by decide)
  · exact dockH_other iZ6 H v 31 (by decide)
  · exact dockH_slot iZ6 iZ6_inj H v 3

theorem iZ7_inj : Function.Injective iZ7 := by decide

theorem install_iZ7 (A : Fin 33 → List Bool) (v : Fin 4 → List Bool) :
    install iZ7 A v = ![v 0, v 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, v 2, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 3] := by
  funext i
  fin_cases i
  · exact install_slot iZ7 iZ7_inj A v 0
  · exact install_slot iZ7 iZ7_inj A v 1
  · exact install_other iZ7 A v 2 (by decide)
  · exact install_other iZ7 A v 3 (by decide)
  · exact install_other iZ7 A v 4 (by decide)
  · exact install_other iZ7 A v 5 (by decide)
  · exact install_other iZ7 A v 6 (by decide)
  · exact install_other iZ7 A v 7 (by decide)
  · exact install_other iZ7 A v 8 (by decide)
  · exact install_other iZ7 A v 9 (by decide)
  · exact install_other iZ7 A v 10 (by decide)
  · exact install_other iZ7 A v 11 (by decide)
  · exact install_slot iZ7 iZ7_inj A v 2
  · exact install_other iZ7 A v 13 (by decide)
  · exact install_other iZ7 A v 14 (by decide)
  · exact install_other iZ7 A v 15 (by decide)
  · exact install_other iZ7 A v 16 (by decide)
  · exact install_other iZ7 A v 17 (by decide)
  · exact install_other iZ7 A v 18 (by decide)
  · exact install_other iZ7 A v 19 (by decide)
  · exact install_other iZ7 A v 20 (by decide)
  · exact install_other iZ7 A v 21 (by decide)
  · exact install_other iZ7 A v 22 (by decide)
  · exact install_other iZ7 A v 23 (by decide)
  · exact install_other iZ7 A v 24 (by decide)
  · exact install_other iZ7 A v 25 (by decide)
  · exact install_other iZ7 A v 26 (by decide)
  · exact install_other iZ7 A v 27 (by decide)
  · exact install_other iZ7 A v 28 (by decide)
  · exact install_other iZ7 A v 29 (by decide)
  · exact install_other iZ7 A v 30 (by decide)
  · exact install_other iZ7 A v 31 (by decide)
  · exact install_slot iZ7 iZ7_inj A v 3

theorem dockH_iZ7 (H : Fin 33 → ℕ) (v : Fin 4 → ℕ) :
    dockH iZ7 H v = ![v 0, v 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, v 2, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot iZ7 iZ7_inj H v 0
  · exact dockH_slot iZ7 iZ7_inj H v 1
  · exact dockH_other iZ7 H v 2 (by decide)
  · exact dockH_other iZ7 H v 3 (by decide)
  · exact dockH_other iZ7 H v 4 (by decide)
  · exact dockH_other iZ7 H v 5 (by decide)
  · exact dockH_other iZ7 H v 6 (by decide)
  · exact dockH_other iZ7 H v 7 (by decide)
  · exact dockH_other iZ7 H v 8 (by decide)
  · exact dockH_other iZ7 H v 9 (by decide)
  · exact dockH_other iZ7 H v 10 (by decide)
  · exact dockH_other iZ7 H v 11 (by decide)
  · exact dockH_slot iZ7 iZ7_inj H v 2
  · exact dockH_other iZ7 H v 13 (by decide)
  · exact dockH_other iZ7 H v 14 (by decide)
  · exact dockH_other iZ7 H v 15 (by decide)
  · exact dockH_other iZ7 H v 16 (by decide)
  · exact dockH_other iZ7 H v 17 (by decide)
  · exact dockH_other iZ7 H v 18 (by decide)
  · exact dockH_other iZ7 H v 19 (by decide)
  · exact dockH_other iZ7 H v 20 (by decide)
  · exact dockH_other iZ7 H v 21 (by decide)
  · exact dockH_other iZ7 H v 22 (by decide)
  · exact dockH_other iZ7 H v 23 (by decide)
  · exact dockH_other iZ7 H v 24 (by decide)
  · exact dockH_other iZ7 H v 25 (by decide)
  · exact dockH_other iZ7 H v 26 (by decide)
  · exact dockH_other iZ7 H v 27 (by decide)
  · exact dockH_other iZ7 H v 28 (by decide)
  · exact dockH_other iZ7 H v 29 (by decide)
  · exact dockH_other iZ7 H v 30 (by decide)
  · exact dockH_other iZ7 H v 31 (by decide)
  · exact dockH_slot iZ7 iZ7_inj H v 3

theorem iZ8_inj : Function.Injective iZ8 := by decide

theorem install_iZ8 (A : Fin 33 → List Bool) (v : Fin 4 → List Bool) :
    install iZ8 A v = ![v 0, v 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, v 2, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 3] := by
  funext i
  fin_cases i
  · exact install_slot iZ8 iZ8_inj A v 0
  · exact install_slot iZ8 iZ8_inj A v 1
  · exact install_other iZ8 A v 2 (by decide)
  · exact install_other iZ8 A v 3 (by decide)
  · exact install_other iZ8 A v 4 (by decide)
  · exact install_other iZ8 A v 5 (by decide)
  · exact install_other iZ8 A v 6 (by decide)
  · exact install_other iZ8 A v 7 (by decide)
  · exact install_other iZ8 A v 8 (by decide)
  · exact install_other iZ8 A v 9 (by decide)
  · exact install_other iZ8 A v 10 (by decide)
  · exact install_other iZ8 A v 11 (by decide)
  · exact install_other iZ8 A v 12 (by decide)
  · exact install_slot iZ8 iZ8_inj A v 2
  · exact install_other iZ8 A v 14 (by decide)
  · exact install_other iZ8 A v 15 (by decide)
  · exact install_other iZ8 A v 16 (by decide)
  · exact install_other iZ8 A v 17 (by decide)
  · exact install_other iZ8 A v 18 (by decide)
  · exact install_other iZ8 A v 19 (by decide)
  · exact install_other iZ8 A v 20 (by decide)
  · exact install_other iZ8 A v 21 (by decide)
  · exact install_other iZ8 A v 22 (by decide)
  · exact install_other iZ8 A v 23 (by decide)
  · exact install_other iZ8 A v 24 (by decide)
  · exact install_other iZ8 A v 25 (by decide)
  · exact install_other iZ8 A v 26 (by decide)
  · exact install_other iZ8 A v 27 (by decide)
  · exact install_other iZ8 A v 28 (by decide)
  · exact install_other iZ8 A v 29 (by decide)
  · exact install_other iZ8 A v 30 (by decide)
  · exact install_other iZ8 A v 31 (by decide)
  · exact install_slot iZ8 iZ8_inj A v 3

theorem dockH_iZ8 (H : Fin 33 → ℕ) (v : Fin 4 → ℕ) :
    dockH iZ8 H v = ![v 0, v 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, v 2, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot iZ8 iZ8_inj H v 0
  · exact dockH_slot iZ8 iZ8_inj H v 1
  · exact dockH_other iZ8 H v 2 (by decide)
  · exact dockH_other iZ8 H v 3 (by decide)
  · exact dockH_other iZ8 H v 4 (by decide)
  · exact dockH_other iZ8 H v 5 (by decide)
  · exact dockH_other iZ8 H v 6 (by decide)
  · exact dockH_other iZ8 H v 7 (by decide)
  · exact dockH_other iZ8 H v 8 (by decide)
  · exact dockH_other iZ8 H v 9 (by decide)
  · exact dockH_other iZ8 H v 10 (by decide)
  · exact dockH_other iZ8 H v 11 (by decide)
  · exact dockH_other iZ8 H v 12 (by decide)
  · exact dockH_slot iZ8 iZ8_inj H v 2
  · exact dockH_other iZ8 H v 14 (by decide)
  · exact dockH_other iZ8 H v 15 (by decide)
  · exact dockH_other iZ8 H v 16 (by decide)
  · exact dockH_other iZ8 H v 17 (by decide)
  · exact dockH_other iZ8 H v 18 (by decide)
  · exact dockH_other iZ8 H v 19 (by decide)
  · exact dockH_other iZ8 H v 20 (by decide)
  · exact dockH_other iZ8 H v 21 (by decide)
  · exact dockH_other iZ8 H v 22 (by decide)
  · exact dockH_other iZ8 H v 23 (by decide)
  · exact dockH_other iZ8 H v 24 (by decide)
  · exact dockH_other iZ8 H v 25 (by decide)
  · exact dockH_other iZ8 H v 26 (by decide)
  · exact dockH_other iZ8 H v 27 (by decide)
  · exact dockH_other iZ8 H v 28 (by decide)
  · exact dockH_other iZ8 H v 29 (by decide)
  · exact dockH_other iZ8 H v 30 (by decide)
  · exact dockH_other iZ8 H v 31 (by decide)
  · exact dockH_slot iZ8 iZ8_inj H v 3

theorem iZ9_inj : Function.Injective iZ9 := by decide

theorem install_iZ9 (A : Fin 33 → List Bool) (v : Fin 4 → List Bool) :
    install iZ9 A v = ![v 0, v 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, v 2, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 3] := by
  funext i
  fin_cases i
  · exact install_slot iZ9 iZ9_inj A v 0
  · exact install_slot iZ9 iZ9_inj A v 1
  · exact install_other iZ9 A v 2 (by decide)
  · exact install_other iZ9 A v 3 (by decide)
  · exact install_other iZ9 A v 4 (by decide)
  · exact install_other iZ9 A v 5 (by decide)
  · exact install_other iZ9 A v 6 (by decide)
  · exact install_other iZ9 A v 7 (by decide)
  · exact install_other iZ9 A v 8 (by decide)
  · exact install_other iZ9 A v 9 (by decide)
  · exact install_other iZ9 A v 10 (by decide)
  · exact install_other iZ9 A v 11 (by decide)
  · exact install_other iZ9 A v 12 (by decide)
  · exact install_other iZ9 A v 13 (by decide)
  · exact install_slot iZ9 iZ9_inj A v 2
  · exact install_other iZ9 A v 15 (by decide)
  · exact install_other iZ9 A v 16 (by decide)
  · exact install_other iZ9 A v 17 (by decide)
  · exact install_other iZ9 A v 18 (by decide)
  · exact install_other iZ9 A v 19 (by decide)
  · exact install_other iZ9 A v 20 (by decide)
  · exact install_other iZ9 A v 21 (by decide)
  · exact install_other iZ9 A v 22 (by decide)
  · exact install_other iZ9 A v 23 (by decide)
  · exact install_other iZ9 A v 24 (by decide)
  · exact install_other iZ9 A v 25 (by decide)
  · exact install_other iZ9 A v 26 (by decide)
  · exact install_other iZ9 A v 27 (by decide)
  · exact install_other iZ9 A v 28 (by decide)
  · exact install_other iZ9 A v 29 (by decide)
  · exact install_other iZ9 A v 30 (by decide)
  · exact install_other iZ9 A v 31 (by decide)
  · exact install_slot iZ9 iZ9_inj A v 3

theorem dockH_iZ9 (H : Fin 33 → ℕ) (v : Fin 4 → ℕ) :
    dockH iZ9 H v = ![v 0, v 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, v 2, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot iZ9 iZ9_inj H v 0
  · exact dockH_slot iZ9 iZ9_inj H v 1
  · exact dockH_other iZ9 H v 2 (by decide)
  · exact dockH_other iZ9 H v 3 (by decide)
  · exact dockH_other iZ9 H v 4 (by decide)
  · exact dockH_other iZ9 H v 5 (by decide)
  · exact dockH_other iZ9 H v 6 (by decide)
  · exact dockH_other iZ9 H v 7 (by decide)
  · exact dockH_other iZ9 H v 8 (by decide)
  · exact dockH_other iZ9 H v 9 (by decide)
  · exact dockH_other iZ9 H v 10 (by decide)
  · exact dockH_other iZ9 H v 11 (by decide)
  · exact dockH_other iZ9 H v 12 (by decide)
  · exact dockH_other iZ9 H v 13 (by decide)
  · exact dockH_slot iZ9 iZ9_inj H v 2
  · exact dockH_other iZ9 H v 15 (by decide)
  · exact dockH_other iZ9 H v 16 (by decide)
  · exact dockH_other iZ9 H v 17 (by decide)
  · exact dockH_other iZ9 H v 18 (by decide)
  · exact dockH_other iZ9 H v 19 (by decide)
  · exact dockH_other iZ9 H v 20 (by decide)
  · exact dockH_other iZ9 H v 21 (by decide)
  · exact dockH_other iZ9 H v 22 (by decide)
  · exact dockH_other iZ9 H v 23 (by decide)
  · exact dockH_other iZ9 H v 24 (by decide)
  · exact dockH_other iZ9 H v 25 (by decide)
  · exact dockH_other iZ9 H v 26 (by decide)
  · exact dockH_other iZ9 H v 27 (by decide)
  · exact dockH_other iZ9 H v 28 (by decide)
  · exact dockH_other iZ9 H v 29 (by decide)
  · exact dockH_other iZ9 H v 30 (by decide)
  · exact dockH_other iZ9 H v 31 (by decide)
  · exact dockH_slot iZ9 iZ9_inj H v 3

theorem iE_inj : Function.Injective iE := by decide

theorem install_iE (A : Fin 33 → List Bool) (v : Fin 4 → List Bool) :
    install iE A v = ![v 0, v 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, v 2, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 3] := by
  funext i
  fin_cases i
  · exact install_slot iE iE_inj A v 0
  · exact install_slot iE iE_inj A v 1
  · exact install_other iE A v 2 (by decide)
  · exact install_other iE A v 3 (by decide)
  · exact install_other iE A v 4 (by decide)
  · exact install_other iE A v 5 (by decide)
  · exact install_other iE A v 6 (by decide)
  · exact install_other iE A v 7 (by decide)
  · exact install_other iE A v 8 (by decide)
  · exact install_other iE A v 9 (by decide)
  · exact install_other iE A v 10 (by decide)
  · exact install_other iE A v 11 (by decide)
  · exact install_other iE A v 12 (by decide)
  · exact install_other iE A v 13 (by decide)
  · exact install_other iE A v 14 (by decide)
  · exact install_slot iE iE_inj A v 2
  · exact install_other iE A v 16 (by decide)
  · exact install_other iE A v 17 (by decide)
  · exact install_other iE A v 18 (by decide)
  · exact install_other iE A v 19 (by decide)
  · exact install_other iE A v 20 (by decide)
  · exact install_other iE A v 21 (by decide)
  · exact install_other iE A v 22 (by decide)
  · exact install_other iE A v 23 (by decide)
  · exact install_other iE A v 24 (by decide)
  · exact install_other iE A v 25 (by decide)
  · exact install_other iE A v 26 (by decide)
  · exact install_other iE A v 27 (by decide)
  · exact install_other iE A v 28 (by decide)
  · exact install_other iE A v 29 (by decide)
  · exact install_other iE A v 30 (by decide)
  · exact install_other iE A v 31 (by decide)
  · exact install_slot iE iE_inj A v 3

theorem dockH_iE (H : Fin 33 → ℕ) (v : Fin 4 → ℕ) :
    dockH iE H v = ![v 0, v 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, v 2, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot iE iE_inj H v 0
  · exact dockH_slot iE iE_inj H v 1
  · exact dockH_other iE H v 2 (by decide)
  · exact dockH_other iE H v 3 (by decide)
  · exact dockH_other iE H v 4 (by decide)
  · exact dockH_other iE H v 5 (by decide)
  · exact dockH_other iE H v 6 (by decide)
  · exact dockH_other iE H v 7 (by decide)
  · exact dockH_other iE H v 8 (by decide)
  · exact dockH_other iE H v 9 (by decide)
  · exact dockH_other iE H v 10 (by decide)
  · exact dockH_other iE H v 11 (by decide)
  · exact dockH_other iE H v 12 (by decide)
  · exact dockH_other iE H v 13 (by decide)
  · exact dockH_other iE H v 14 (by decide)
  · exact dockH_slot iE iE_inj H v 2
  · exact dockH_other iE H v 16 (by decide)
  · exact dockH_other iE H v 17 (by decide)
  · exact dockH_other iE H v 18 (by decide)
  · exact dockH_other iE H v 19 (by decide)
  · exact dockH_other iE H v 20 (by decide)
  · exact dockH_other iE H v 21 (by decide)
  · exact dockH_other iE H v 22 (by decide)
  · exact dockH_other iE H v 23 (by decide)
  · exact dockH_other iE H v 24 (by decide)
  · exact dockH_other iE H v 25 (by decide)
  · exact dockH_other iE H v 26 (by decide)
  · exact dockH_other iE H v 27 (by decide)
  · exact dockH_other iE H v 28 (by decide)
  · exact dockH_other iE H v 29 (by decide)
  · exact dockH_other iE H v 30 (by decide)
  · exact dockH_other iE H v 31 (by decide)
  · exact dockH_slot iE iE_inj H v 3

theorem iL_inj : Function.Injective iL := by decide

theorem install_iL (A : Fin 33 → List Bool) (v : Fin 4 → List Bool) :
    install iL A v = ![v 0, v 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, v 2, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 3] := by
  funext i
  fin_cases i
  · exact install_slot iL iL_inj A v 0
  · exact install_slot iL iL_inj A v 1
  · exact install_other iL A v 2 (by decide)
  · exact install_other iL A v 3 (by decide)
  · exact install_other iL A v 4 (by decide)
  · exact install_other iL A v 5 (by decide)
  · exact install_other iL A v 6 (by decide)
  · exact install_other iL A v 7 (by decide)
  · exact install_other iL A v 8 (by decide)
  · exact install_other iL A v 9 (by decide)
  · exact install_other iL A v 10 (by decide)
  · exact install_other iL A v 11 (by decide)
  · exact install_other iL A v 12 (by decide)
  · exact install_other iL A v 13 (by decide)
  · exact install_other iL A v 14 (by decide)
  · exact install_other iL A v 15 (by decide)
  · exact install_slot iL iL_inj A v 2
  · exact install_other iL A v 17 (by decide)
  · exact install_other iL A v 18 (by decide)
  · exact install_other iL A v 19 (by decide)
  · exact install_other iL A v 20 (by decide)
  · exact install_other iL A v 21 (by decide)
  · exact install_other iL A v 22 (by decide)
  · exact install_other iL A v 23 (by decide)
  · exact install_other iL A v 24 (by decide)
  · exact install_other iL A v 25 (by decide)
  · exact install_other iL A v 26 (by decide)
  · exact install_other iL A v 27 (by decide)
  · exact install_other iL A v 28 (by decide)
  · exact install_other iL A v 29 (by decide)
  · exact install_other iL A v 30 (by decide)
  · exact install_other iL A v 31 (by decide)
  · exact install_slot iL iL_inj A v 3

theorem dockH_iL (H : Fin 33 → ℕ) (v : Fin 4 → ℕ) :
    dockH iL H v = ![v 0, v 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, v 2, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot iL iL_inj H v 0
  · exact dockH_slot iL iL_inj H v 1
  · exact dockH_other iL H v 2 (by decide)
  · exact dockH_other iL H v 3 (by decide)
  · exact dockH_other iL H v 4 (by decide)
  · exact dockH_other iL H v 5 (by decide)
  · exact dockH_other iL H v 6 (by decide)
  · exact dockH_other iL H v 7 (by decide)
  · exact dockH_other iL H v 8 (by decide)
  · exact dockH_other iL H v 9 (by decide)
  · exact dockH_other iL H v 10 (by decide)
  · exact dockH_other iL H v 11 (by decide)
  · exact dockH_other iL H v 12 (by decide)
  · exact dockH_other iL H v 13 (by decide)
  · exact dockH_other iL H v 14 (by decide)
  · exact dockH_other iL H v 15 (by decide)
  · exact dockH_slot iL iL_inj H v 2
  · exact dockH_other iL H v 17 (by decide)
  · exact dockH_other iL H v 18 (by decide)
  · exact dockH_other iL H v 19 (by decide)
  · exact dockH_other iL H v 20 (by decide)
  · exact dockH_other iL H v 21 (by decide)
  · exact dockH_other iL H v 22 (by decide)
  · exact dockH_other iL H v 23 (by decide)
  · exact dockH_other iL H v 24 (by decide)
  · exact dockH_other iL H v 25 (by decide)
  · exact dockH_other iL H v 26 (by decide)
  · exact dockH_other iL H v 27 (by decide)
  · exact dockH_other iL H v 28 (by decide)
  · exact dockH_other iL H v 29 (by decide)
  · exact dockH_other iL H v 30 (by decide)
  · exact dockH_other iL H v 31 (by decide)
  · exact dockH_slot iL iL_inj H v 3

theorem iV_inj : Function.Injective iV := by decide

theorem install_iV (A : Fin 33 → List Bool) (v : Fin 4 → List Bool) :
    install iV A v = ![v 0, v 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, v 2, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 3] := by
  funext i
  fin_cases i
  · exact install_slot iV iV_inj A v 0
  · exact install_slot iV iV_inj A v 1
  · exact install_other iV A v 2 (by decide)
  · exact install_other iV A v 3 (by decide)
  · exact install_other iV A v 4 (by decide)
  · exact install_other iV A v 5 (by decide)
  · exact install_other iV A v 6 (by decide)
  · exact install_other iV A v 7 (by decide)
  · exact install_other iV A v 8 (by decide)
  · exact install_other iV A v 9 (by decide)
  · exact install_other iV A v 10 (by decide)
  · exact install_other iV A v 11 (by decide)
  · exact install_other iV A v 12 (by decide)
  · exact install_other iV A v 13 (by decide)
  · exact install_other iV A v 14 (by decide)
  · exact install_other iV A v 15 (by decide)
  · exact install_other iV A v 16 (by decide)
  · exact install_slot iV iV_inj A v 2
  · exact install_other iV A v 18 (by decide)
  · exact install_other iV A v 19 (by decide)
  · exact install_other iV A v 20 (by decide)
  · exact install_other iV A v 21 (by decide)
  · exact install_other iV A v 22 (by decide)
  · exact install_other iV A v 23 (by decide)
  · exact install_other iV A v 24 (by decide)
  · exact install_other iV A v 25 (by decide)
  · exact install_other iV A v 26 (by decide)
  · exact install_other iV A v 27 (by decide)
  · exact install_other iV A v 28 (by decide)
  · exact install_other iV A v 29 (by decide)
  · exact install_other iV A v 30 (by decide)
  · exact install_other iV A v 31 (by decide)
  · exact install_slot iV iV_inj A v 3

theorem dockH_iV (H : Fin 33 → ℕ) (v : Fin 4 → ℕ) :
    dockH iV H v = ![v 0, v 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, v 2, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 3] := by
  funext i
  fin_cases i
  · exact dockH_slot iV iV_inj H v 0
  · exact dockH_slot iV iV_inj H v 1
  · exact dockH_other iV H v 2 (by decide)
  · exact dockH_other iV H v 3 (by decide)
  · exact dockH_other iV H v 4 (by decide)
  · exact dockH_other iV H v 5 (by decide)
  · exact dockH_other iV H v 6 (by decide)
  · exact dockH_other iV H v 7 (by decide)
  · exact dockH_other iV H v 8 (by decide)
  · exact dockH_other iV H v 9 (by decide)
  · exact dockH_other iV H v 10 (by decide)
  · exact dockH_other iV H v 11 (by decide)
  · exact dockH_other iV H v 12 (by decide)
  · exact dockH_other iV H v 13 (by decide)
  · exact dockH_other iV H v 14 (by decide)
  · exact dockH_other iV H v 15 (by decide)
  · exact dockH_other iV H v 16 (by decide)
  · exact dockH_slot iV iV_inj H v 2
  · exact dockH_other iV H v 18 (by decide)
  · exact dockH_other iV H v 19 (by decide)
  · exact dockH_other iV H v 20 (by decide)
  · exact dockH_other iV H v 21 (by decide)
  · exact dockH_other iV H v 22 (by decide)
  · exact dockH_other iV H v 23 (by decide)
  · exact dockH_other iV H v 24 (by decide)
  · exact dockH_other iV H v 25 (by decide)
  · exact dockH_other iV H v 26 (by decide)
  · exact dockH_other iV H v 27 (by decide)
  · exact dockH_other iV H v 28 (by decide)
  · exact dockH_other iV H v 29 (by decide)
  · exact dockH_other iV H v 30 (by decide)
  · exact dockH_other iV H v 31 (by decide)
  · exact dockH_slot iV iV_inj H v 3

theorem iJ_inj : Function.Injective iJ := by decide

theorem install_iJ (A : Fin 33 → List Bool) (v : Fin 3 → List Bool) :
    install iJ A v = ![A 0, A 1, v 0, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, v 1, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 2] := by
  funext i
  fin_cases i
  · exact install_other iJ A v 0 (by decide)
  · exact install_other iJ A v 1 (by decide)
  · exact install_slot iJ iJ_inj A v 0
  · exact install_other iJ A v 3 (by decide)
  · exact install_other iJ A v 4 (by decide)
  · exact install_other iJ A v 5 (by decide)
  · exact install_other iJ A v 6 (by decide)
  · exact install_other iJ A v 7 (by decide)
  · exact install_other iJ A v 8 (by decide)
  · exact install_other iJ A v 9 (by decide)
  · exact install_other iJ A v 10 (by decide)
  · exact install_other iJ A v 11 (by decide)
  · exact install_other iJ A v 12 (by decide)
  · exact install_other iJ A v 13 (by decide)
  · exact install_other iJ A v 14 (by decide)
  · exact install_other iJ A v 15 (by decide)
  · exact install_other iJ A v 16 (by decide)
  · exact install_other iJ A v 17 (by decide)
  · exact install_slot iJ iJ_inj A v 1
  · exact install_other iJ A v 19 (by decide)
  · exact install_other iJ A v 20 (by decide)
  · exact install_other iJ A v 21 (by decide)
  · exact install_other iJ A v 22 (by decide)
  · exact install_other iJ A v 23 (by decide)
  · exact install_other iJ A v 24 (by decide)
  · exact install_other iJ A v 25 (by decide)
  · exact install_other iJ A v 26 (by decide)
  · exact install_other iJ A v 27 (by decide)
  · exact install_other iJ A v 28 (by decide)
  · exact install_other iJ A v 29 (by decide)
  · exact install_other iJ A v 30 (by decide)
  · exact install_other iJ A v 31 (by decide)
  · exact install_slot iJ iJ_inj A v 2

theorem dockH_iJ (H : Fin 33 → ℕ) (v : Fin 3 → ℕ) :
    dockH iJ H v = ![H 0, H 1, v 0, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, v 1, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other iJ H v 0 (by decide)
  · exact dockH_other iJ H v 1 (by decide)
  · exact dockH_slot iJ iJ_inj H v 0
  · exact dockH_other iJ H v 3 (by decide)
  · exact dockH_other iJ H v 4 (by decide)
  · exact dockH_other iJ H v 5 (by decide)
  · exact dockH_other iJ H v 6 (by decide)
  · exact dockH_other iJ H v 7 (by decide)
  · exact dockH_other iJ H v 8 (by decide)
  · exact dockH_other iJ H v 9 (by decide)
  · exact dockH_other iJ H v 10 (by decide)
  · exact dockH_other iJ H v 11 (by decide)
  · exact dockH_other iJ H v 12 (by decide)
  · exact dockH_other iJ H v 13 (by decide)
  · exact dockH_other iJ H v 14 (by decide)
  · exact dockH_other iJ H v 15 (by decide)
  · exact dockH_other iJ H v 16 (by decide)
  · exact dockH_other iJ H v 17 (by decide)
  · exact dockH_slot iJ iJ_inj H v 1
  · exact dockH_other iJ H v 19 (by decide)
  · exact dockH_other iJ H v 20 (by decide)
  · exact dockH_other iJ H v 21 (by decide)
  · exact dockH_other iJ H v 22 (by decide)
  · exact dockH_other iJ H v 23 (by decide)
  · exact dockH_other iJ H v 24 (by decide)
  · exact dockH_other iJ H v 25 (by decide)
  · exact dockH_other iJ H v 26 (by decide)
  · exact dockH_other iJ H v 27 (by decide)
  · exact dockH_other iJ H v 28 (by decide)
  · exact dockH_other iJ H v 29 (by decide)
  · exact dockH_other iJ H v 30 (by decide)
  · exact dockH_other iJ H v 31 (by decide)
  · exact dockH_slot iJ iJ_inj H v 2

theorem iM_inj : Function.Injective iM := by decide

theorem install_iM (A : Fin 33 → List Bool) (v : Fin 3 → List Bool) :
    install iM A v = ![A 0, A 1, v 0, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, v 1, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 2] := by
  funext i
  fin_cases i
  · exact install_other iM A v 0 (by decide)
  · exact install_other iM A v 1 (by decide)
  · exact install_slot iM iM_inj A v 0
  · exact install_other iM A v 3 (by decide)
  · exact install_other iM A v 4 (by decide)
  · exact install_other iM A v 5 (by decide)
  · exact install_other iM A v 6 (by decide)
  · exact install_other iM A v 7 (by decide)
  · exact install_other iM A v 8 (by decide)
  · exact install_other iM A v 9 (by decide)
  · exact install_other iM A v 10 (by decide)
  · exact install_other iM A v 11 (by decide)
  · exact install_other iM A v 12 (by decide)
  · exact install_other iM A v 13 (by decide)
  · exact install_other iM A v 14 (by decide)
  · exact install_other iM A v 15 (by decide)
  · exact install_other iM A v 16 (by decide)
  · exact install_other iM A v 17 (by decide)
  · exact install_other iM A v 18 (by decide)
  · exact install_slot iM iM_inj A v 1
  · exact install_other iM A v 20 (by decide)
  · exact install_other iM A v 21 (by decide)
  · exact install_other iM A v 22 (by decide)
  · exact install_other iM A v 23 (by decide)
  · exact install_other iM A v 24 (by decide)
  · exact install_other iM A v 25 (by decide)
  · exact install_other iM A v 26 (by decide)
  · exact install_other iM A v 27 (by decide)
  · exact install_other iM A v 28 (by decide)
  · exact install_other iM A v 29 (by decide)
  · exact install_other iM A v 30 (by decide)
  · exact install_other iM A v 31 (by decide)
  · exact install_slot iM iM_inj A v 2

theorem dockH_iM (H : Fin 33 → ℕ) (v : Fin 3 → ℕ) :
    dockH iM H v = ![H 0, H 1, v 0, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, v 1, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other iM H v 0 (by decide)
  · exact dockH_other iM H v 1 (by decide)
  · exact dockH_slot iM iM_inj H v 0
  · exact dockH_other iM H v 3 (by decide)
  · exact dockH_other iM H v 4 (by decide)
  · exact dockH_other iM H v 5 (by decide)
  · exact dockH_other iM H v 6 (by decide)
  · exact dockH_other iM H v 7 (by decide)
  · exact dockH_other iM H v 8 (by decide)
  · exact dockH_other iM H v 9 (by decide)
  · exact dockH_other iM H v 10 (by decide)
  · exact dockH_other iM H v 11 (by decide)
  · exact dockH_other iM H v 12 (by decide)
  · exact dockH_other iM H v 13 (by decide)
  · exact dockH_other iM H v 14 (by decide)
  · exact dockH_other iM H v 15 (by decide)
  · exact dockH_other iM H v 16 (by decide)
  · exact dockH_other iM H v 17 (by decide)
  · exact dockH_other iM H v 18 (by decide)
  · exact dockH_slot iM iM_inj H v 1
  · exact dockH_other iM H v 20 (by decide)
  · exact dockH_other iM H v 21 (by decide)
  · exact dockH_other iM H v 22 (by decide)
  · exact dockH_other iM H v 23 (by decide)
  · exact dockH_other iM H v 24 (by decide)
  · exact dockH_other iM H v 25 (by decide)
  · exact dockH_other iM H v 26 (by decide)
  · exact dockH_other iM H v 27 (by decide)
  · exact dockH_other iM H v 28 (by decide)
  · exact dockH_other iM H v 29 (by decide)
  · exact dockH_other iM H v 30 (by decide)
  · exact dockH_other iM H v 31 (by decide)
  · exact dockH_slot iM iM_inj H v 2

theorem iP_inj : Function.Injective iP := by decide

theorem install_iP (A : Fin 33 → List Bool) (v : Fin 3 → List Bool) :
    install iP A v = ![A 0, A 1, A 2, v 0, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, v 1, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 2] := by
  funext i
  fin_cases i
  · exact install_other iP A v 0 (by decide)
  · exact install_other iP A v 1 (by decide)
  · exact install_other iP A v 2 (by decide)
  · exact install_slot iP iP_inj A v 0
  · exact install_other iP A v 4 (by decide)
  · exact install_other iP A v 5 (by decide)
  · exact install_other iP A v 6 (by decide)
  · exact install_other iP A v 7 (by decide)
  · exact install_other iP A v 8 (by decide)
  · exact install_other iP A v 9 (by decide)
  · exact install_other iP A v 10 (by decide)
  · exact install_other iP A v 11 (by decide)
  · exact install_other iP A v 12 (by decide)
  · exact install_other iP A v 13 (by decide)
  · exact install_other iP A v 14 (by decide)
  · exact install_other iP A v 15 (by decide)
  · exact install_other iP A v 16 (by decide)
  · exact install_other iP A v 17 (by decide)
  · exact install_other iP A v 18 (by decide)
  · exact install_other iP A v 19 (by decide)
  · exact install_slot iP iP_inj A v 1
  · exact install_other iP A v 21 (by decide)
  · exact install_other iP A v 22 (by decide)
  · exact install_other iP A v 23 (by decide)
  · exact install_other iP A v 24 (by decide)
  · exact install_other iP A v 25 (by decide)
  · exact install_other iP A v 26 (by decide)
  · exact install_other iP A v 27 (by decide)
  · exact install_other iP A v 28 (by decide)
  · exact install_other iP A v 29 (by decide)
  · exact install_other iP A v 30 (by decide)
  · exact install_other iP A v 31 (by decide)
  · exact install_slot iP iP_inj A v 2

theorem dockH_iP (H : Fin 33 → ℕ) (v : Fin 3 → ℕ) :
    dockH iP H v = ![H 0, H 1, H 2, v 0, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, v 1, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other iP H v 0 (by decide)
  · exact dockH_other iP H v 1 (by decide)
  · exact dockH_other iP H v 2 (by decide)
  · exact dockH_slot iP iP_inj H v 0
  · exact dockH_other iP H v 4 (by decide)
  · exact dockH_other iP H v 5 (by decide)
  · exact dockH_other iP H v 6 (by decide)
  · exact dockH_other iP H v 7 (by decide)
  · exact dockH_other iP H v 8 (by decide)
  · exact dockH_other iP H v 9 (by decide)
  · exact dockH_other iP H v 10 (by decide)
  · exact dockH_other iP H v 11 (by decide)
  · exact dockH_other iP H v 12 (by decide)
  · exact dockH_other iP H v 13 (by decide)
  · exact dockH_other iP H v 14 (by decide)
  · exact dockH_other iP H v 15 (by decide)
  · exact dockH_other iP H v 16 (by decide)
  · exact dockH_other iP H v 17 (by decide)
  · exact dockH_other iP H v 18 (by decide)
  · exact dockH_other iP H v 19 (by decide)
  · exact dockH_slot iP iP_inj H v 1
  · exact dockH_other iP H v 21 (by decide)
  · exact dockH_other iP H v 22 (by decide)
  · exact dockH_other iP H v 23 (by decide)
  · exact dockH_other iP H v 24 (by decide)
  · exact dockH_other iP H v 25 (by decide)
  · exact dockH_other iP H v 26 (by decide)
  · exact dockH_other iP H v 27 (by decide)
  · exact dockH_other iP H v 28 (by decide)
  · exact dockH_other iP H v 29 (by decide)
  · exact dockH_other iP H v 30 (by decide)
  · exact dockH_other iP H v 31 (by decide)
  · exact dockH_slot iP iP_inj H v 2

theorem iW_inj : Function.Injective iW := by decide

theorem install_iW (A : Fin 33 → List Bool) (v : Fin 3 → List Bool) :
    install iW A v = ![A 0, A 1, A 2, A 3, v 0, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, v 1, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 2] := by
  funext i
  fin_cases i
  · exact install_other iW A v 0 (by decide)
  · exact install_other iW A v 1 (by decide)
  · exact install_other iW A v 2 (by decide)
  · exact install_other iW A v 3 (by decide)
  · exact install_slot iW iW_inj A v 0
  · exact install_other iW A v 5 (by decide)
  · exact install_other iW A v 6 (by decide)
  · exact install_other iW A v 7 (by decide)
  · exact install_other iW A v 8 (by decide)
  · exact install_other iW A v 9 (by decide)
  · exact install_other iW A v 10 (by decide)
  · exact install_other iW A v 11 (by decide)
  · exact install_other iW A v 12 (by decide)
  · exact install_other iW A v 13 (by decide)
  · exact install_other iW A v 14 (by decide)
  · exact install_other iW A v 15 (by decide)
  · exact install_other iW A v 16 (by decide)
  · exact install_other iW A v 17 (by decide)
  · exact install_other iW A v 18 (by decide)
  · exact install_other iW A v 19 (by decide)
  · exact install_other iW A v 20 (by decide)
  · exact install_slot iW iW_inj A v 1
  · exact install_other iW A v 22 (by decide)
  · exact install_other iW A v 23 (by decide)
  · exact install_other iW A v 24 (by decide)
  · exact install_other iW A v 25 (by decide)
  · exact install_other iW A v 26 (by decide)
  · exact install_other iW A v 27 (by decide)
  · exact install_other iW A v 28 (by decide)
  · exact install_other iW A v 29 (by decide)
  · exact install_other iW A v 30 (by decide)
  · exact install_other iW A v 31 (by decide)
  · exact install_slot iW iW_inj A v 2

theorem dockH_iW (H : Fin 33 → ℕ) (v : Fin 3 → ℕ) :
    dockH iW H v = ![H 0, H 1, H 2, H 3, v 0, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, v 1, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other iW H v 0 (by decide)
  · exact dockH_other iW H v 1 (by decide)
  · exact dockH_other iW H v 2 (by decide)
  · exact dockH_other iW H v 3 (by decide)
  · exact dockH_slot iW iW_inj H v 0
  · exact dockH_other iW H v 5 (by decide)
  · exact dockH_other iW H v 6 (by decide)
  · exact dockH_other iW H v 7 (by decide)
  · exact dockH_other iW H v 8 (by decide)
  · exact dockH_other iW H v 9 (by decide)
  · exact dockH_other iW H v 10 (by decide)
  · exact dockH_other iW H v 11 (by decide)
  · exact dockH_other iW H v 12 (by decide)
  · exact dockH_other iW H v 13 (by decide)
  · exact dockH_other iW H v 14 (by decide)
  · exact dockH_other iW H v 15 (by decide)
  · exact dockH_other iW H v 16 (by decide)
  · exact dockH_other iW H v 17 (by decide)
  · exact dockH_other iW H v 18 (by decide)
  · exact dockH_other iW H v 19 (by decide)
  · exact dockH_other iW H v 20 (by decide)
  · exact dockH_slot iW iW_inj H v 1
  · exact dockH_other iW H v 22 (by decide)
  · exact dockH_other iW H v 23 (by decide)
  · exact dockH_other iW H v 24 (by decide)
  · exact dockH_other iW H v 25 (by decide)
  · exact dockH_other iW H v 26 (by decide)
  · exact dockH_other iW H v 27 (by decide)
  · exact dockH_other iW H v 28 (by decide)
  · exact dockH_other iW H v 29 (by decide)
  · exact dockH_other iW H v 30 (by decide)
  · exact dockH_other iW H v 31 (by decide)
  · exact dockH_slot iW iW_inj H v 2

theorem iS_inj : Function.Injective iS := by decide

theorem install_iS (A : Fin 33 → List Bool) (v : Fin 3 → List Bool) :
    install iS A v = ![A 0, A 1, A 2, A 3, v 0, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, v 1, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, v 2] := by
  funext i
  fin_cases i
  · exact install_other iS A v 0 (by decide)
  · exact install_other iS A v 1 (by decide)
  · exact install_other iS A v 2 (by decide)
  · exact install_other iS A v 3 (by decide)
  · exact install_slot iS iS_inj A v 0
  · exact install_other iS A v 5 (by decide)
  · exact install_other iS A v 6 (by decide)
  · exact install_other iS A v 7 (by decide)
  · exact install_other iS A v 8 (by decide)
  · exact install_other iS A v 9 (by decide)
  · exact install_other iS A v 10 (by decide)
  · exact install_other iS A v 11 (by decide)
  · exact install_other iS A v 12 (by decide)
  · exact install_other iS A v 13 (by decide)
  · exact install_other iS A v 14 (by decide)
  · exact install_other iS A v 15 (by decide)
  · exact install_other iS A v 16 (by decide)
  · exact install_other iS A v 17 (by decide)
  · exact install_other iS A v 18 (by decide)
  · exact install_other iS A v 19 (by decide)
  · exact install_other iS A v 20 (by decide)
  · exact install_other iS A v 21 (by decide)
  · exact install_slot iS iS_inj A v 1
  · exact install_other iS A v 23 (by decide)
  · exact install_other iS A v 24 (by decide)
  · exact install_other iS A v 25 (by decide)
  · exact install_other iS A v 26 (by decide)
  · exact install_other iS A v 27 (by decide)
  · exact install_other iS A v 28 (by decide)
  · exact install_other iS A v 29 (by decide)
  · exact install_other iS A v 30 (by decide)
  · exact install_other iS A v 31 (by decide)
  · exact install_slot iS iS_inj A v 2

theorem dockH_iS (H : Fin 33 → ℕ) (v : Fin 3 → ℕ) :
    dockH iS H v = ![H 0, H 1, H 2, H 3, v 0, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, v 1, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other iS H v 0 (by decide)
  · exact dockH_other iS H v 1 (by decide)
  · exact dockH_other iS H v 2 (by decide)
  · exact dockH_other iS H v 3 (by decide)
  · exact dockH_slot iS iS_inj H v 0
  · exact dockH_other iS H v 5 (by decide)
  · exact dockH_other iS H v 6 (by decide)
  · exact dockH_other iS H v 7 (by decide)
  · exact dockH_other iS H v 8 (by decide)
  · exact dockH_other iS H v 9 (by decide)
  · exact dockH_other iS H v 10 (by decide)
  · exact dockH_other iS H v 11 (by decide)
  · exact dockH_other iS H v 12 (by decide)
  · exact dockH_other iS H v 13 (by decide)
  · exact dockH_other iS H v 14 (by decide)
  · exact dockH_other iS H v 15 (by decide)
  · exact dockH_other iS H v 16 (by decide)
  · exact dockH_other iS H v 17 (by decide)
  · exact dockH_other iS H v 18 (by decide)
  · exact dockH_other iS H v 19 (by decide)
  · exact dockH_other iS H v 20 (by decide)
  · exact dockH_other iS H v 21 (by decide)
  · exact dockH_slot iS iS_inj H v 1
  · exact dockH_other iS H v 23 (by decide)
  · exact dockH_other iS H v 24 (by decide)
  · exact dockH_other iS H v 25 (by decide)
  · exact dockH_other iS H v 26 (by decide)
  · exact dockH_other iS H v 27 (by decide)
  · exact dockH_other iS H v 28 (by decide)
  · exact dockH_other iS H v 29 (by decide)
  · exact dockH_other iS H v 30 (by decide)
  · exact dockH_other iS H v 31 (by decide)
  · exact dockH_slot iS iS_inj H v 2

theorem iC_inj : Function.Injective iC := by decide

theorem install_iC (A : Fin 33 → List Bool) (v : Fin 10 → List Bool) :
    install iC A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] := by
  funext i
  fin_cases i
  · exact install_other iC A v 0 (by decide)
  · exact install_other iC A v 1 (by decide)
  · exact install_other iC A v 2 (by decide)
  · exact install_other iC A v 3 (by decide)
  · exact install_other iC A v 4 (by decide)
  · exact install_other iC A v 5 (by decide)
  · exact install_other iC A v 6 (by decide)
  · exact install_other iC A v 7 (by decide)
  · exact install_other iC A v 8 (by decide)
  · exact install_other iC A v 9 (by decide)
  · exact install_other iC A v 10 (by decide)
  · exact install_other iC A v 11 (by decide)
  · exact install_other iC A v 12 (by decide)
  · exact install_other iC A v 13 (by decide)
  · exact install_other iC A v 14 (by decide)
  · exact install_other iC A v 15 (by decide)
  · exact install_other iC A v 16 (by decide)
  · exact install_other iC A v 17 (by decide)
  · exact install_other iC A v 18 (by decide)
  · exact install_other iC A v 19 (by decide)
  · exact install_other iC A v 20 (by decide)
  · exact install_other iC A v 21 (by decide)
  · exact install_other iC A v 22 (by decide)
  · exact install_slot iC iC_inj A v 0
  · exact install_slot iC iC_inj A v 1
  · exact install_slot iC iC_inj A v 2
  · exact install_slot iC iC_inj A v 3
  · exact install_slot iC iC_inj A v 4
  · exact install_slot iC iC_inj A v 5
  · exact install_slot iC iC_inj A v 6
  · exact install_slot iC iC_inj A v 7
  · exact install_slot iC iC_inj A v 8
  · exact install_slot iC iC_inj A v 9

theorem dockH_iC (H : Fin 33 → ℕ) (v : Fin 10 → ℕ) :
    dockH iC H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] := by
  funext i
  fin_cases i
  · exact dockH_other iC H v 0 (by decide)
  · exact dockH_other iC H v 1 (by decide)
  · exact dockH_other iC H v 2 (by decide)
  · exact dockH_other iC H v 3 (by decide)
  · exact dockH_other iC H v 4 (by decide)
  · exact dockH_other iC H v 5 (by decide)
  · exact dockH_other iC H v 6 (by decide)
  · exact dockH_other iC H v 7 (by decide)
  · exact dockH_other iC H v 8 (by decide)
  · exact dockH_other iC H v 9 (by decide)
  · exact dockH_other iC H v 10 (by decide)
  · exact dockH_other iC H v 11 (by decide)
  · exact dockH_other iC H v 12 (by decide)
  · exact dockH_other iC H v 13 (by decide)
  · exact dockH_other iC H v 14 (by decide)
  · exact dockH_other iC H v 15 (by decide)
  · exact dockH_other iC H v 16 (by decide)
  · exact dockH_other iC H v 17 (by decide)
  · exact dockH_other iC H v 18 (by decide)
  · exact dockH_other iC H v 19 (by decide)
  · exact dockH_other iC H v 20 (by decide)
  · exact dockH_other iC H v 21 (by decide)
  · exact dockH_other iC H v 22 (by decide)
  · exact dockH_slot iC iC_inj H v 0
  · exact dockH_slot iC iC_inj H v 1
  · exact dockH_slot iC iC_inj H v 2
  · exact dockH_slot iC iC_inj H v 3
  · exact dockH_slot iC iC_inj H v 4
  · exact dockH_slot iC iC_inj H v 5
  · exact dockH_slot iC iC_inj H v 6
  · exact dockH_slot iC iC_inj H v 7
  · exact dockH_slot iC iC_inj H v 8
  · exact dockH_slot iC iC_inj H v 9


noncomputable def iZ0D := RecoveryFocus.machine iZ0 (w3RM [true, false] [true, false] [true, false, false])
noncomputable def iZ1D := RecoveryFocus.machine iZ1 (w3RM [true, false] [true, false] [true, false, false])
noncomputable def iZ2D := RecoveryFocus.machine iZ2 (w3RM [true, false] [true, false] [true, false, false])
noncomputable def iZ3D := RecoveryFocus.machine iZ3 (w3RM [true, false] [true, false] [true, false, false])
noncomputable def iZ4D := RecoveryFocus.machine iZ4 (w3RM [true, false] [true, false] [true, false, false])
noncomputable def iZ5D := RecoveryFocus.machine iZ5 (w3RM [true, false] [true, false] [true, false, false])
noncomputable def iZ6D := RecoveryFocus.machine iZ6 (w3RM [true, false] [true, false] [true, false, false])
noncomputable def iZ7D := RecoveryFocus.machine iZ7 (w3RM [true, false] [true, false] [true, false, false])
noncomputable def iZ8D := RecoveryFocus.machine iZ8 (w3RM [true, false] [true, false] [true, false, false])
noncomputable def iZ9D := RecoveryFocus.machine iZ9 (w3RM [true, false] [true, false] [true, false, false])
noncomputable def iED := RecoveryFocus.machine iE (w4RM [true, false] [true, true] [true, false] [false])
noncomputable def iLD := RecoveryFocus.machine iL (wLastRM)
noncomputable def iVD := RecoveryFocus.machine iV (w3RM [true, true] [true, false] [true, false, false])
noncomputable def iJD := RecoveryFocus.machine iJ (wRunM false)
noncomputable def iMD := RecoveryFocus.machine iM (wRunM true)
noncomputable def iPD := RecoveryFocus.machine iP (wRunM false)
noncomputable def iWD := RecoveryFocus.machine iW (w2RM [true, true] [])
noncomputable def iSD := RecoveryFocus.machine iS (w2RM ts4 [true, true, false, true, true, false, false])
noncomputable def iCD := RecoveryFocus.machine iC (cellsRM)

noncomputable def initM := Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (iZ0D) iZ1D) iZ2D) iZ3D) iZ4D) iZ5D) iZ6D) iZ7D) iZ8D) iZ9D) iED) iLD) iVD) iJD) iMD) iPD) iWD) iSD) iCD

/-- The cost of the constant writers. -/
def initCost (Q0 W m p1 w : ℕ) : ℕ :=
  (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2) + 1 + (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2) + 1 + (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2) + 1 + (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2) + 1 + (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2) + 1 + (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2) + 1 + (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2) + 1 + (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2) + 1 + (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2) + 1 + (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2) + 1 + (2 * w4Cost [true, false] [true, true] [true, false] [false] (Q0 + 1) W + 2) + 1 + (2 * wLastCost Q0 W + 2) + 1 + (2 * w3Cost [true, true] [true, false] [true, false, false] (Q0 + 1) W + 2) + 1 + (2 * wRunCost m + 2) + 1 + (2 * wRunCost m + 2) + 1 + (2 * wRunCost p1 + 2) + 1 + (2 * w2Cost [true, true] [] w + 2) + 1 + (2 * w2Cost ts4 [true, true, false, true, true, false, false] w + 2) + 1 + (2 * cellsCost + 2)


/-- **The constant tapes** (T2): from the unary parameters, the stages' registers, templates, counters, fields and
flags are written, every head back at cell 0. -/
theorem init_run (Q0 W m p1 w cap : ℕ) (hcap : initCost Q0 W m p1 w ≤ cap) :
    Step initM (initCost Q0 W m p1 w) ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), frame (List.replicate m true), frame (List.replicate p1 false), List.replicate (w + w) true, Kit.streamTape (List.replicate (2 * (w + w + 1)) [true]) [], [false], [false], [false], [false], [false], [false], [true], [true], [false], List.replicate cap false] := by
  have hc := hcap
  unfold initCost at hc
  have siZ0 := dockRun (w3_run [true, false] [true, false] [true, false, false] (Q0 + 1) W cap (by omega) (frame (Unions.zeroT (Q0 + 1) W)) (zero_word (Q0 + 1) W)) iZ0 iZ0_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iZ0, dockH_iZ0] at siZ0
  have tiZ0 : Step iZ0D (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siZ0.congr rfl rfl
  have siZ1 := dockRun (w3_run [true, false] [true, false] [true, false, false] (Q0 + 1) W cap (by omega) (frame (Unions.zeroT (Q0 + 1) W)) (zero_word (Q0 + 1) W)) iZ1 iZ1_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iZ1, dockH_iZ1] at siZ1
  have tiZ1 : Step iZ1D (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siZ1.congr rfl rfl
  have siZ2 := dockRun (w3_run [true, false] [true, false] [true, false, false] (Q0 + 1) W cap (by omega) (frame (Unions.zeroT (Q0 + 1) W)) (zero_word (Q0 + 1) W)) iZ2 iZ2_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iZ2, dockH_iZ2] at siZ2
  have tiZ2 : Step iZ2D (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siZ2.congr rfl rfl
  have siZ3 := dockRun (w3_run [true, false] [true, false] [true, false, false] (Q0 + 1) W cap (by omega) (frame (Unions.zeroT (Q0 + 1) W)) (zero_word (Q0 + 1) W)) iZ3 iZ3_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iZ3, dockH_iZ3] at siZ3
  have tiZ3 : Step iZ3D (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siZ3.congr rfl rfl
  have siZ4 := dockRun (w3_run [true, false] [true, false] [true, false, false] (Q0 + 1) W cap (by omega) (frame (Unions.zeroT (Q0 + 1) W)) (zero_word (Q0 + 1) W)) iZ4 iZ4_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iZ4, dockH_iZ4] at siZ4
  have tiZ4 : Step iZ4D (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siZ4.congr rfl rfl
  have siZ5 := dockRun (w3_run [true, false] [true, false] [true, false, false] (Q0 + 1) W cap (by omega) (frame (Unions.zeroT (Q0 + 1) W)) (zero_word (Q0 + 1) W)) iZ5 iZ5_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iZ5, dockH_iZ5] at siZ5
  have tiZ5 : Step iZ5D (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siZ5.congr rfl rfl
  have siZ6 := dockRun (w3_run [true, false] [true, false] [true, false, false] (Q0 + 1) W cap (by omega) (frame (Unions.zeroT (Q0 + 1) W)) (zero_word (Q0 + 1) W)) iZ6 iZ6_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iZ6, dockH_iZ6] at siZ6
  have tiZ6 : Step iZ6D (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siZ6.congr rfl rfl
  have siZ7 := dockRun (w3_run [true, false] [true, false] [true, false, false] (Q0 + 1) W cap (by omega) (frame (Unions.zeroT (Q0 + 1) W)) (zero_word (Q0 + 1) W)) iZ7 iZ7_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iZ7, dockH_iZ7] at siZ7
  have tiZ7 : Step iZ7D (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siZ7.congr rfl rfl
  have siZ8 := dockRun (w3_run [true, false] [true, false] [true, false, false] (Q0 + 1) W cap (by omega) (frame (Unions.zeroT (Q0 + 1) W)) (zero_word (Q0 + 1) W)) iZ8 iZ8_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iZ8, dockH_iZ8] at siZ8
  have tiZ8 : Step iZ8D (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siZ8.congr rfl rfl
  have siZ9 := dockRun (w3_run [true, false] [true, false] [true, false, false] (Q0 + 1) W cap (by omega) (frame (Unions.zeroT (Q0 + 1) W)) (zero_word (Q0 + 1) W)) iZ9 iZ9_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iZ9, dockH_iZ9] at siZ9
  have tiZ9 : Step iZ9D (2 * w3Cost [true, false] [true, false] [true, false, false] (Q0 + 1) W + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siZ9.congr rfl rfl
  have siE := dockRun (w4_run [true, false] [true, true] [true, false] [false] (Q0 + 1) W cap (by omega) (frame (Unions.ew (Q0 + 1) W (0, 0))) (z0_word (Q0 + 1) W)) iE iE_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iE, dockH_iE] at siE
  have tiE : Step iED (2 * w4Cost [true, false] [true, true] [true, false] [false] (Q0 + 1) W + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siE.congr rfl rfl
  have siL := dockRun (wLast_run Q0 W cap (by omega)) iL iL_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iL, dockH_iL] at siL
  have tiL : Step iLD (2 * wLastCost Q0 W + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siL.congr rfl rfl
  have siV := dockRun (w3_run [true, true] [true, false] [true, false, false] (Q0 + 1) W cap (by omega) (frame (Unions.levelT (Q0 + 1) W)) (level_word (Q0 + 1) W)) iV iV_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iV, dockH_iV] at siV
  have tiV : Step iVD (2 * w3Cost [true, true] [true, false] [true, false, false] (Q0 + 1) W + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siV.congr rfl rfl
  have siJ := dockRun (wRun_run false m cap (by omega)) iJ iJ_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iJ, dockH_iJ] at siJ
  have tiJ : Step iJD (2 * wRunCost m + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siJ.congr rfl rfl
  have siM := dockRun (wRun_run true m cap (by omega)) iM iM_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iM, dockH_iM] at siM
  have tiM : Step iMD (2 * wRunCost m + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), frame (List.replicate m true), [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siM.congr rfl rfl
  have siP := dockRun (wRun_run false p1 cap (by omega)) iP iP_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), frame (List.replicate m true), [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iP, dockH_iP] at siP
  have tiP : Step iPD (2 * wRunCost p1 + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), frame (List.replicate m true), [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), frame (List.replicate m true), frame (List.replicate p1 false), [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siP.congr rfl rfl
  have siW := dockRun (w2_run [true, true] [] w cap (by omega) (List.replicate (w + w) true) (raw2_word w)) iW iW_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), frame (List.replicate m true), frame (List.replicate p1 false), [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iW, dockH_iW] at siW
  have tiW : Step iWD (2 * w2Cost [true, true] [] w + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), frame (List.replicate m true), frame (List.replicate p1 false), [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), frame (List.replicate m true), frame (List.replicate p1 false), List.replicate (w + w) true, [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siW.congr rfl rfl
  have siS := dockRun (w2_run ts4 [true, true, false, true, true, false, false] w cap (by omega) (Kit.streamTape (List.replicate (2 * (w + w + 1)) [true]) []) (ts_word w)) iS iS_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), frame (List.replicate m true), frame (List.replicate p1 false), List.replicate (w + w) true, [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iS, dockH_iS] at siS
  have tiS : Step iSD (2 * w2Cost ts4 [true, true, false, true, true, false, false] w + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), frame (List.replicate m true), frame (List.replicate p1 false), List.replicate (w + w) true, [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), frame (List.replicate m true), frame (List.replicate p1 false), List.replicate (w + w) true, Kit.streamTape (List.replicate (2 * (w + w + 1)) [true]) [], [], [], [], [], [], [], [], [], [], List.replicate cap false] :=
    siS.congr rfl rfl
  have siC := dockRun (cells_run cap (by omega)) iC iC_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), frame (List.replicate m true), frame (List.replicate p1 false), List.replicate (w + w) true, Kit.streamTape (List.replicate (2 * (w + w + 1)) [true]) [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_iC, dockH_iC] at siC
  have tiC : Step iCD (2 * cellsCost + 2)
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), frame (List.replicate m true), frame (List.replicate p1 false), List.replicate (w + w) true, Kit.streamTape (List.replicate (2 * (w + w + 1)) [true]) [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![List.replicate (Q0 + 1) true, List.replicate W true, List.replicate m true, List.replicate p1 true, List.replicate w true, frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.zeroT (Q0 + 1) W), frame (Unions.ew (Q0 + 1) W (0, 0)), frame (Unions.lastT (Q0 + 1) W), frame (Unions.levelT (Q0 + 1) W), frame (List.replicate m false), frame (List.replicate m true), frame (List.replicate p1 false), List.replicate (w + w) true, Kit.streamTape (List.replicate (2 * (w + w + 1)) [true]) [], [false], [false], [false], [false], [false], [false], [true], [true], [false], List.replicate cap false] :=
    siC.congr rfl rfl
  exact ((((((((((((((((((tiZ0).seq tiZ1).seq tiZ2).seq tiZ3).seq tiZ4).seq tiZ5).seq tiZ6).seq tiZ7).seq tiZ8).seq tiZ9).seq tiE).seq tiL).seq tiV).seq tiJ).seq tiM).seq tiP).seq tiW).seq tiS).seq tiC

end NearCubicWires.WireExponent3_5.CompilerMachine.Top
