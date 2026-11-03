import Proof.Packets.SourceParamsK

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget.Pow2
open NearCubicWires.SourceBudget NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
open NearCubicWires.SourceBudget.Params
noncomputable section

/-! ## 1. Rounding up to a power of two -/

/-! ## 2. The rounded caps, each `2^y` with `y` in closed form (`C` stays exact: see the header) -/

section params
variable (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)

/-- The exponent of `hF'`. -/
def yH (L q : ℕ) : ℕ :=
  Nat.clog 2 (hd0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L*
    (q+1)^hd0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L + 1) + q/4
/-- The exponent of `cC'`'s table part. -/
def yA (L q : ℕ) : ℕ :=
  Nat.clog 2 (cpTC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
    (q+1)^cpTE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) + 1) + (q - normalizedLiveCount q L)
/-- The exponent of `cC'`'s small part. -/
def yB (q : ℕ) : ℕ :=
  Nat.clog 2 (cpSC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
    (q+1)^cpSE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) + 1) + q/4
/-- The exponent of `rR'`. -/
def yR (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (q : ℕ) : ℕ :=
  Nat.clog 2 (((packets (decompositionOf s)).coefficient*rowsC (decompositionOf s) p.clauseDegree (tgt s p) + 1)*
    (q+1)^rowsE (decompositionOf s) p.clauseDegree (tgt s p) + 1) + q/4

/-- **`capsU`'s header fuel, rounded**. -/
def hFOf2 (L q : ℕ) : ℕ := 2^(yH selector s p L q)
/-- **`capsU`'s copy cap, rounded** (one power of two above the table part plus the small part). -/
def cCOf2 (L q : ℕ) : ℕ := 2^(max (yA selector s p L q) (yB selector s p q) + 1)
/-- **`capsU`'s raw reserve, rounded**. -/
def rROf2 (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (q : ℕ) : ℕ := 2^(yR selector s p packets q)

/-! ### Lower bounds (the old values) -/

/-! ### Upper bounds (the classes, at most `2×` / `4×`) -/

/-! ## 4. The caps fit at the rounded values -/

end params

/-! ## 5. `KF` at the rounded classes -/

end
end NearCubicWires.SourceBudget.Pow2

