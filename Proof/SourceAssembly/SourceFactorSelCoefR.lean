import Proof.SourceAssembly.SourceFactorSelCoef

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.CoefR
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairOrdinary.RadixSemantics RepairOrdinary.SignedSortKey
open NearCubicWires.SourceFactorSel.CoefPrim NearCubicWires.SourceFactorSel.CoefAcc NearCubicWires.SourceFactorSel.CoefBin
open NearCubicWires.SourceFactorSel.CoefReduce NearCubicWires.SourceFactorSel.CoefValue NearCubicWires.SourceFactorSel.Coef
noncomputable section

/-! ## Value -/

def RN0 (rho : ℚ) : ℕ := 1 * rho.num.natAbs
def RD0 (rho : ℚ) : ℕ := 1 * rho.den
def RS0 (rho : ℚ) : ℕ := 0 + (decide (rho.num < 0)).toNat
def RN1 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RN0 rho * nA (f 0) (t 0)
def RN2 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RN1 rho f t * nA (f 1) (t 1)
def RN3 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RN2 rho f t * nA (f 2) (t 2)
def numR (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RN3 rho f t * nA (f 3) (t 3)
def RD1 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RD0 rho * dA (f 0) (t 0)
def RD2 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RD1 rho f t * dA (f 1) (t 1)
def RD3 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RD2 rho f t * dA (f 2) (t 2)
def denR (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RD3 rho f t * dA (f 3) (t 3)
def RS1 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RS0 rho + sA (f 0) (t 0)
def RS2 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RS1 rho f t + sA (f 1) (t 1)
def RS3 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RS2 rho f t + sA (f 2) (t 2)
def sgnR (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RS3 rho f t + sA (f 3) (t 3)

/-! ## The rho accumulator, docked -/

/-! ## The machine -/

def asl : Fin 30 → Fin 245 := ![8, 15, 16, 17, 18, 19, 20, 14, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34,
  35, 36, 37, 38, 39, 40, 41, 42]
def tsl0 : Fin 32 → Fin 245 := ![0, 18, 19, 20, 43, 44, 45, 14, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
  60, 61, 62, 63, 64, 65, 66, 67, 4, 68]
def tsl1 : Fin 32 → Fin 245 := ![1, 43, 44, 45, 69, 70, 71, 14, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85,
  86, 87, 88, 89, 90, 91, 92, 93, 5, 94]
def tsl2 : Fin 32 → Fin 245 := ![2, 69, 70, 71, 95, 96, 97, 14, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109,
  110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 6, 120]
def tsl3 : Fin 32 → Fin 245 := ![3, 95, 96, 97, 121, 122, 123, 14, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134,
  135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 7, 146]
def usl1 : Fin 48 → Fin 245 := ![121, 122, 9, 14, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160,
  161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184,
  185, 186, 187, 188, 189, 190]
def usl2 : Fin 14 → Fin 245 := ![123, 187, 14, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]
def usl3 : Fin 49 → Fin 245 := ![10, 200, 201, 189, 14, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214,
  215, 216, 217, 218, 11, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 12, 233, 234, 235, 236, 237, 238,
  239, 240, 241, 242, 243, 244, 13]

/-- **The coefficient stage on the cursor's record multiplier**: one fixed machine (`Fin 245`). -/
def coefRM := Composition.machine (Count.oneM (15 : Fin 245) 14)
  (Composition.machine (Count.oneM (16 : Fin 245) 14)
  (Composition.machine (RecoveryFocus.machine asl accM)
  (Composition.machine (RecoveryFocus.machine tsl0 accSwM)
  (Composition.machine (RecoveryFocus.machine tsl1 accSwM)
  (Composition.machine (RecoveryFocus.machine tsl2 accSwM)
  (Composition.machine (RecoveryFocus.machine tsl3 accSwM)
  (Composition.machine (RecoveryFocus.machine usl1 divideM)
  (Composition.machine (RecoveryFocus.machine usl2 signM)
  (RecoveryFocus.machine usl3 emitM)))))))))

def gcdR (K : ℕ) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := Nat.gcd (numR rho f t) (denR rho f t * K)
def posR (K : ℕ) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ :=
  if sgnR rho f t % 2 = 0 then numR rho f t / gcdR K rho f t else 0
def negR (K : ℕ) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ :=
  if sgnR rho f t % 2 = 0 then 0 else numR rho f t / gcdR K rho f t
def dnR (K : ℕ) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := denR rho f t * K / gcdR K rho f t

def coefRCost (cw c0 K b : ℕ) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ :=
  (2 * 1 + 2) + 1 + ((2 * 1 + 2) + 1 +
  (accCost (decide (rho.num < 0)) rho.num.natAbs rho.den c0 1 1 0 + 1 +
  (accSwCost (f 0) (sS (f 0) (t 0)) (nS (f 0) (t 0)) (dS (f 0) (t 0)) cw (RN0 rho) (RD0 rho) (RS0 rho) + 1 +
  (accSwCost (f 1) (sS (f 1) (t 1)) (nS (f 1) (t 1)) (dS (f 1) (t 1)) cw (RN1 rho f t) (RD1 rho f t) (RS1 rho f t) + 1 +
  (accSwCost (f 2) (sS (f 2) (t 2)) (nS (f 2) (t 2)) (dS (f 2) (t 2)) cw (RN2 rho f t) (RD2 rho f t) (RS2 rho f t) + 1 +
  (accSwCost (f 3) (sS (f 3) (t 3)) (nS (f 3) (t 3)) (dS (f 3) (t 3)) cw (RN3 rho f t) (RD3 rho f t) (RS3 rho f t) + 1 +
  (divideCost (numR rho f t) (denR rho f t) K + 1 +
  (signCost (sgnR rho f t) (numR rho f t / gcdR K rho f t) + 1 +
  emitCost b (posR K rho f t) (negR K rho f t) (dnR K rho f t)))))))))


/-! ## The run -/

end
end NearCubicWires.SourceFactorSel.CoefR

