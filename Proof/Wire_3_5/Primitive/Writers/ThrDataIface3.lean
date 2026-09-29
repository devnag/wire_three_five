import Proof.Wire_3_5.Primitive.Writers.ThrDataIface2
import Proof.Wire_3_5.Primitive.ThresholdWriter.Joins

/-! # The THR per-call data stage, v3 — the THR numbers once per call

Every THR and HASH unit needs numbers only W6 computes (binary arithmetic: the aux filter's `e = listE A B_* M K`
carries `M^{2t}`). Ruling (B) of: they enter ONCE, in the per-call data stage, and every unit reads them from the
loop's data tape `u` as plain WM (as `SymDec` reads the SYM counts). v3 is v2 (`ThrDataStage2`, whose projection
`toThrDataStage2` keeps the shells and the c4 gate) plus a second machine on the same tapes whose data word is
`dataWord (hashNums … ++ thrCounts Cs carriers)`: the numbers at fixed positions first (the carriers' count among them),
then the slice lengths.

* `thrNumList` (`ThrNumVals.get` as a list), **`hashNums`** (`|carriers|`, `capT`, then the fourteen THR numbers),
  `hashNums_length`;
* **`ThrDataStage3 alg Dexp capT`**: `ThrDataStage2` plus `M3` (its machine), `cost3` (polynomially bounded), `need`
  (W6's capacity need, polynomial in `n`), and `run3` (from the THR request with the call envelope's description bound
  `descriptionBits ≤ (n+1)^{26}`, W6's hypothesis, the v2 outputs with the data word `hashNums ++ thrCounts`).

Paper lines per number (gate 3): `|carriers|`, the named carriers (lem:primitive P3:3083-3086); `capT`, the THR filter's cap `B_T` (tr:B, P3:3425-3430); `|𝒢|`, `K = 8(|𝒢|+1)n^D`,
the prime cutoff, `|primes|`, `Σ p` (row:prime, P3:2573-2580: "a polynomial-size prime set sufficiently larger than
`n^{b+D}|𝒢|`"); `τ₀ = O(L)` (row:radix, P3:2597-2599); `M, A, B_*, J, t` (filt:majorant, P3:2121-2157); `e`, the aux
filter's error exponent (P3:2210-2211, `ε_aux = 2^{-D_aux L²}`; filt:soft P3:2220-2231); `ℓ₀`, the field modulus
(filt:majorant's `GF(2^{ℓ₀})`). Gate 2: every entry is a value `≤ poly(n)` (`e = Θ(D·L²)`, `capT ≤ C(F)(q+1)³`, `K`,
the cutoff and `Σ p` polynomial, `ℓ₀ = O(D·L)` and the modulus `< 2^{ℓ₀+1}`), so the unary data word is polynomial. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrData
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.Shared

/-- The fourteen THR numbers in register order. -/
def thrNumList (v : PrimThrW.Joins.ThrNumVals) : List ℕ := List.ofFn v.get

/-- **The numbers every THR/HASH unit reads, at fixed positions**: the carriers' count, the THR filter's cap, then the
call's THR numbers (W6's `thrNumVals`). -/
def hashNums (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp capT : ℕ) :
    List ℕ :=
  carriers.length :: capT :: thrNumList (PrimThrW.Joins.thrNumVals P Cs alg Dexp carriers.length capT)

theorem hashNums_length (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp capT : ℕ) :
    (hashNums P Cs carriers alg Dexp capT).length = 16 := by
  simp [hashNums, thrNumList]

end NearCubicWires.WireExponent3_5.PrimAsm.ThrData
