import Proof.SourceAssembly.SourceFactorSelCoefBin

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.CoefReduce
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairOrdinary.RadixSemantics RepairOrdinary.SignedSortKey
open NearCubicWires.SourceFactorSel.CoefPrim NearCubicWires.SourceFactorSel.CoefAcc NearCubicWires.SourceFactorSel.CoefBin
noncomputable section

/-! ## Docked primitives and frame lemmas -/

def fixedM {U : Nat} (d l : Fin U) (w : List Bool) :=
  RecoveryFocus.machine (![d, l] : Fin 2 → Fin U) (HierarchyFixedWord.machine w)

/-! ## (1) Divide: `1^N, 1^D₀, 1^K ↦ 1^(N/g), 1^(D₀K/g)`, `g = gcd N (D₀K)` -/

def dsl4 : Fin 16 → Fin 48 := ![0, 6, 7, 3, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
def dsl5 : Fin 16 → Fin 48 := ![5, 6, 20, 3, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]
def dsl6 : Fin 7 → Fin 48 := ![7, 20, 33, 34, 35, 36, 37]
def dsl7 : Fin 7 → Fin 48 := ![33, 38, 39, 40, 41, 42, 43]
def dsl8 : Fin 4 → Fin 48 := ![0, 40, 44, 45]
def dsl9 : Fin 4 → Fin 48 := ![5, 40, 46, 47]

/-- Local universe `Fin 48`: `0` `1^N` · `1` `1^D₀` · `2` `1^K` · `3` log · `4` `word K` · `5` `1^D` · `6` `1^W` ·
`7`/`20` `N`/`D` in framed binary · `33` `g` in framed binary · `40` `word g` · `44` `1^(N/g)` · `46` `1^(D/g)` · rest scratch. -/
def divideM := Composition.machine (Count.wordM false (2 : Fin 48) 4 3)
  (Composition.machine (Count.mulM (1 : Fin 48) 4 5 3)
  (Composition.machine (Count.sumM (0 : Fin 48) 5 6 3)
  (Composition.machine (RecoveryFocus.machine dsl4 tobinM)
  (Composition.machine (RecoveryFocus.machine dsl5 tobinM)
  (Composition.machine (RecoveryFocus.machine dsl6 gcdM)
  (Composition.machine (unaryM dsl7)
  (Composition.machine (RecoveryFocus.machine dsl8 MatrixBucketDivide.machine)
  (RecoveryFocus.machine dsl9 MatrixBucketDivide.machine))))))))

def divideCost (N D4 K : Nat) : Nat :=
  (2 * K + 8) + 1 + ((2 * (D4 * (2 * K + 3) + 2) + 2) + 1 + ((2 * (N + D4 * K) + 6) + 1 +
  (tobinCost N (N + D4 * K) + 1 + (tobinCost (D4 * K) (N + D4 * K) + 1 +
  (gcdCost (N + D4 * K) N (D4 * K) + 1 + (ub (binary (N + D4 * K) (Nat.gcd N (D4 * K))) + 1 +
  ((8 * N + 6) + 1 + (8 * (D4 * K) + 6))))))))

/-! ## (2) Sign split: `1^σ, 1^M ↦ 1^(M or 0)` on the positive / negative port by the parity of `σ` -/

/-- Local universe `Fin 14`: `0` `1^σ` · `1` `1^M` · `2` log · `3` `tape 2` · `4` `1^(σ/2)` · `5` scratch · `6` zero ·
`7` copy of `σ/2` · `8` `1^(2·(σ/2))` · `9` `word σ` · `10` the flag `[σ even]` · `11` zero · `12` positive · `13` negative. -/
def signM := Composition.machine (fixedM (3 : Fin 14) 2 (UnaryTemplate.tape 2))
  (Composition.machine (RecoveryFocus.machine (![0, 3, 4, 5] : Fin 4 → Fin 14) MatrixBucketDivide.machine)
  (Composition.machine (Count.sumM (4 : Fin 14) 6 7 2)
  (Composition.machine (Count.sumM (4 : Fin 14) 7 8 2)
  (Composition.machine (Count.wordM false (0 : Fin 14) 9 2)
  (Composition.machine (RecoveryFocus.machine (![9, 8, 10, 2] : Fin 4 → Fin 14) MatrixBucketDimensions.Compare.machine)
  (CloseoutRowsOriginalSwitch.machine (Count.sumM (1 : Fin 14) 11 12 2) (Count.sumM (1 : Fin 14) 11 13 2)
    (10 : Fin 14)))))))

def signCost (σ M : Nat) : Nat :=
  (2 * (UnaryTemplate.tape 2).length + 2) + 1 + ((8 * σ + 6) + 1 + ((2 * (σ / 2 + 0) + 6) + 1 +
  ((2 * (σ / 2 + (σ / 2 + 0)) + 6) + 1 + ((2 * σ + 8) + 1 + ((2 * min σ (σ / 2 + (σ / 2 + 0)) + 6) + 1 +
  ((2 * (M + 0) + 6) + 2))))))

/-! ## (3) Emit: `1^b, 1^p, 1^n, 1^d ↦ pad R (frame (binary (width b) ·))` -/

def esl5 : Fin 16 → Fin 49 := ![1, 9, 22, 4, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]
def esl6 : Fin 16 → Fin 49 := ![2, 9, 35, 4, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
def esl7 : Fin 16 → Fin 49 := ![3, 9, 48, 4, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]

/-- Local universe `Fin 49`: `0` `1^b` · `1`/`2`/`3` `1^p`, `1^n`, `1^d` · `4` log · `5` zero · `6` copy of `b` ·
`7` `1^(2b)` · `8` `1^2` · `9` `1^(width b)` · outputs `22`, `35`, `48` (blank `R`) · the three converters' scratch. -/
def emitM := Composition.machine (Count.sumM (0 : Fin 49) 5 6 4)
  (Composition.machine (Count.sumM (0 : Fin 49) 6 7 4)
  (Composition.machine (fixedM (8 : Fin 49) 4 [true, true])
  (Composition.machine (Count.sumM (7 : Fin 49) 8 9 4)
  (Composition.machine (RecoveryFocus.machine esl5 tobinM)
  (Composition.machine (RecoveryFocus.machine esl6 tobinM)
  (RecoveryFocus.machine esl7 tobinM))))))

def emitCost (b p n d : Nat) : Nat :=
  (2 * (b + 0) + 6) + 1 + ((2 * (b + (b + 0)) + 6) + 1 + ((2 * [true, true].length + 2) + 1 +
  ((2 * (b + (b + 0) + 2) + 6) + 1 + (tobinCost p (b + (b + 0) + 2) + 1 + (tobinCost n (b + (b + 0) + 2) + 1 +
  tobinCost d (b + (b + 0) + 2))))))

end
end NearCubicWires.SourceFactorSel.CoefReduce

