import Proof.Wire_3_5.FinalPass.ThrSz4
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5

/-! # The THR word-size lemma, part 2: the primes, stage 4's table, the numbers; the theorem

From the call's THR numbers (`valsOf`, each `≤ K_t·(n+1)^{D_t}`): **`w5_le`** (the primes' word), **`w6_le`** (stage
4's table: the majorant's `M, J, t, B_*` are the numbers' `M, J, t, B_*`, `thrNumVals_A`), **`nums_le`** (`a`, `|𝒢|`,
`τ₀`, `|occs|`), and **`thrSize_poly`**: `ThrNumsPoly l → ∃ D, ∀ F, ∃ C, ∀ …, thrSize (thrCallOf …) ≤ C·(n+1)^D`.
Paper quantity: the call's size, polynomial in `n` with the degree fixed before the gate (P3:3069-3072, 3176-3178,
P3:3114-3115: "All powers of `n` are fixed before a fixed `r`"). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrSz
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm

section Pieces2
variable (l : Literals) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
 {a' : ℕ} (ha' : a' ≤ 4)
 (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)

/-- The coefficient of stage 4's table. -/
def levK (K : ℕ) : ℕ := K + 2 + (K + 1) * (5 * (16 * K + 20 * (K * K + 2)) + 5 + K)

end Pieces2

end NearCubicWires.WireExponent3_5.FinalPass.ThrSz
