import Proof.SourceAssembly.SourceWiring
import Proof.Amplification.RecoveryScratchErase
import Proof.Amplification.RecoveryBoundedTapeCopy
import Proof.Amplification.RecoveryChildSelection
import Proof.Hierarchy.CompetitorDenominator
import Proof.CaseAnalysis.RowsCountBinary
import Proof.MachineModel.ClockScalarFields
import Proof.CaseAnalysis.RowsOriginalSwitch

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
namespace NearCubicWires.SourceConstruction.Prologue
noncomputable section

/-- The E6 machine: erase the copy, copy the query word, erase the cache word. -/
def restoreMachine {V : ℕ} (src dst drv log : Fin V) :=
  Composition.machine (Composition.machine
    (RecoveryFocus.machine (![dst, drv, log] : Fin (1+1+1) → Fin V) (RecoveryScratchErase.resetMachine 1))
    (RecoveryFocus.machine (![src, dst, drv, log] : Fin 4 → Fin V) RecoveryBoundedTapeCopy.machine))
    (RecoveryFocus.machine (![src, drv, log] : Fin (1+1+1) → Fin V) (RecoveryScratchErase.resetMachine 1))

/-! ### The F6 denominator pipeline on 66 tapes (`g`)

Tapes `g 0 .. g 58`: blank scratch (`replicate Rc false`). `g 59 = 1^e`, `g 60 = 1^p` (the unary counts),
`g 61 = 1^w`, `g 62 = 1^q` (residents, kept), `g 63 = enc 4`, `g 64, g 65` = the clear's driver `1^Rc`
and log `0^(Rc+2)` (kept). Seven stages: erase `enc 4`; `count_run e` (→ `g 4`); `count_run p` (→ `g 13`);
copy `1^w` (→ `g 19`); copy `1^q` (→ `g 22`); `ClockNormalize` (→ `g 24 = frame (binary w p)`); the engine. -/

def sE : Fin (1+1+1) → Fin 66 := ![63, 64, 65]
def sCe : Fin 10 → Fin 66 := ![59, 0, 1, 2, 3, 4, 5, 6, 7, 8]
def sCp : Fin 10 → Fin 66 := ![60, 9, 10, 11, 12, 13, 14, 15, 16, 17]
def sW : Fin 4 → Fin 66 := ![61, 18, 19, 20]
def sQ : Fin 4 → Fin 66 := ![62, 21, 22, 23]
def sN : Fin 5 → Fin 66 := ![19, 13, 24, 25, 26]
def sD : Fin 37 → Fin 66 := ![4, 24, 19, 22, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42,
  43, 44, 45, 46, 47, 48, 63, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]


/-- The F6 denominator machine on the 66-tape local universe. -/
def f6Machine :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine
    (RecoveryFocus.machine sE (RecoveryScratchErase.resetMachine 1))
    (RecoveryFocus.machine sCe CloseoutRowsCountBinary.machine))
    (RecoveryFocus.machine sCp CloseoutRowsCountBinary.machine))
    (RecoveryFocus.machine sW ClockUnarySum.machine))
    (RecoveryFocus.machine sQ ClockUnarySum.machine))
    (RecoveryFocus.machine sN ClockNormalize.machine))
    (RecoveryFocus.machine sD CompetitorDenominator.machine)

def f6Cost (Rc e p w q : ℕ) : ℕ :=
  (2*Rc+4) + 1 + CloseoutRowsCountBinary.budget e + 1 + CloseoutRowsCountBinary.budget p + 1 +
    (2*w+6) + 1 + (2*q+6) + 1 + (4*w+4) + 1 +
    CompetitorDenominator.budget (natBitLength e) w q

/-- Erase the destination, then copy the source onto it (driver `1^C`, log `0^K`, `C+1 ≤ K`). -/
def owMachine :=
  Composition.machine
    (RecoveryFocus.machine (![1, 2, 3] : Fin (1+1+1) → Fin 4) (RecoveryScratchErase.resetMachine 1))
    RecoveryBoundedTapeCopy.machine

def ow {V' : ℕ} (g : Fin 72 → Fin V') (src dst : Fin 72) : Fin 4 → Fin V' := ![g src, g dst, g 64, g 65]

def f6Full {V : ℕ} (g : Fin 72 → Fin V) :=
  Composition.machine (RecoveryFocus.machine (fun i : Fin 66 => g (Fin.castAdd 6 i)) f6Machine)
    (Composition.machine (Composition.machine
      (RecoveryFocus.machine (ow g 66 69) owMachine) (RecoveryFocus.machine (ow g 67 70) owMachine))
      (RecoveryFocus.machine (ow g 68 71) owMachine))

def f6FullCost (Rc e p w q : ℕ) : ℕ :=
  f6Cost Rc e p w q + 1 + ((((2*Rc+4) + 1 + (2*Rc+4)) + 1 + ((2*Rc+4) + 1 + (2*Rc+4))) + 1 +
    ((2*Rc+4) + 1 + (2*Rc+4)))

/-! ## F2: the per-call slope `M2_r`, selected by one bit read off `1^L`

AD's `effectiveDegree_eq`: the effective degree is `uniformDeg` when the child list is nonempty and `1`
when it is empty. The child list is empty iff `L = |exactListWord []| = |natWord 0| = 3`, and otherwise
`L ≥ 4`. So the bit is cell `3` of `lenTape = pad capLen 1^L`, and no new producer is needed. The stage moves
`lenTape`'s head to `3`, switches on the cell (`CloseoutRowsOriginalSwitch`), moves back, and copies the
chosen resident slope onto the per-call `cs 1`. -/

/-- One-step head moves on one ambient tape. -/
def rMove {V : ℕ} (x : Fin V) : Fin V → HeadMove := fun i => if i = x then .right else .stay
def lMove {V : ℕ} (x : Fin V) : Fin V → HeadMove := fun i => if i = x then .left else .stay
def move3 {V : ℕ} (d : Fin V → HeadMove) :=
  Composition.machine (Composition.machine (DecompositionCountPosition.move d)
    (DecompositionCountPosition.move d)) (DecompositionCountPosition.move d)

def slopeMachine {V : ℕ} (lenT big small dst s1 lg : Fin V) :=
  Composition.machine (move3 (rMove lenT)) (CloseoutRowsOriginalSwitch.machine
    (Composition.machine (move3 (lMove lenT))
      (RecoveryFocus.machine ![big, s1, dst, lg] ClockUnarySum.machine))
    (Composition.machine (move3 (lMove lenT))
      (RecoveryFocus.machine ![small, s1, dst, lg] ClockUnarySum.machine)) lenT)

end
end NearCubicWires.SourceConstruction.Prologue
end
