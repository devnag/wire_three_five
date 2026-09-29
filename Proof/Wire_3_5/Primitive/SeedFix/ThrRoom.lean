import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4

/-! # gate 2: the numbers machine's room, a function of the literals only

P3:2543-2558 (row:threshold-rows: `|𝒢| = |Sel|` from the decomposition algorithm's children) and P3:3114-3115 ("All
powers of `n` are fixed before a fixed `r`"): W6's numbers machine `numsW6 alg D` has `w6x alg = 10176 + 4·(Ta alg − 1)`
scratch tapes (`Ta alg` the algorithm's native machine's tapes) and `21` ports, independent of `D`:
* **`numsW6_x`**: `(numsW6 alg D).x = w6x alg`;
* **`thrStageRoom alg = w6x alg + 21 + 4096`**: the `x3` of `ThrDataStage4` producer (W6's scratch and ports, and
  `4096` tapes of the own register layouts: the cap `capT`, the count `V`, the unary ports), `numsW6_fits`;
* **`s5ThrRoom alg = w6x alg + 21 + 4096`**: the room the S5-THR half needs in the bank (`roomT`), `numsW6_fits_s5`;
* the literal-level forms `thrStageRoomL l`, `s5ThrRoomL l` at `litAlg l` (`gate0`'s algorithm, `gate0_litAlg`).

Paper quantities of the main types: the scratch tapes of the machine computing the THR numbers (`|𝒢|`, `K`, the
cutoff, the primes, `Σp`, `τ₀`, `M, A, B_*, J, t, e, ℓ₀`, the modulus), fixed by the literals. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Split

/-- W6's scratch tapes: the front end's layout `DS + 2 + DR`, its algorithm tapes, W6's own `273`, the reset tapes. -/
def w6x (alg : RepairRepresentation.DecompositionAlgorithm) : ℕ := 10176 + 4 * (PrimThrW.PayM.Ta alg - 1)

theorem numsW6_x (alg : RepairRepresentation.DecompositionAlgorithm) (D : ℕ) : (numsW6 alg D).x = w6x alg := by
  have e1 : (numsW6 alg D).x = T0 + (tf alg).x + 1 := rfl
  have e2 : (tf alg).x = PrimThrW.TF3Pay.TT alg + 1 := rfl
  have e3 : PrimThrW.TF3Pay.TT alg = 9901 + 4 * (PrimThrW.PayM.Ta alg - 1) := rfl
  have e4 : T0 = 273 := rfl
  unfold w6x
  omega

/-- **The `x3` of `ThrDataStage4` producer**: W6's scratch, its `21` ports, `4096` tapes of the own layouts. -/
def thrStageRoom (alg : RepairRepresentation.DecompositionAlgorithm) : ℕ := w6x alg + 21 + 4096

end NearCubicWires.WireExponent3_5.PrimT.W6
