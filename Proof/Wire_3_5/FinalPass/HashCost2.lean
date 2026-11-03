import Lean
import Proof.Wire_3_5.FinalPass.HashCost1
import Proof.Wire_3_5.FinalPass.HashOcc
import Proof.Wire_3_5.FinalPass.SymCost3
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.HashS
import Proof.Wire_3_5.FinalPass.HashSz1
import Proof.Wire_3_5.FinalPass.HashCost2Base


noncomputable section
set_option maxRecDepth 4096


/-! # The HASH child's cost, part 2: the exponents below the pad (the arithmetic)

P3:3098-3107 (the pad `2^ρ`, `ρ ≥ n − k + d_A L`; the load condition `max{Ψ_i, Ψ_aux} ≤ c₀(n−k)`) at a HASH call:
with `S = S_aux = k + L² + (k+L³)L²(k+L)` (`C_D·S = Ψ_aux ≤ ψ ≤ n`), every exponent of the HASH child's steps is
`O(S)` plus the capacity's `⌊n/16⌋ + d_C L²` plus `O(L)`: the fixed fields `e_F`, the charged occurrences
`e_O = C₁S`, the printed word `e_W`, the Hb size `e_S`. Under the floor `costCDH ≤ C_D` (fixed before `F`)
and `d_A ≥ dAH` (fixed before `F`), the conditions of `kch_pow` (at `d_A − 1`) and the HASH-specific
budgets (the Hb prep `2^{3e_C+38}`, the cells `2^{2e_C+2}`, the word `2^{e_W+13}`, the capacity floor
`2^{32}(hbS+1)^8 ≤ 2^{e_C}`) hold.

* `cF1`, `c0F`, `hashB`, `costCDH`, `dAH`; **`hcostH_exp`**.

Paper quantity of the main type: the HASH child's step exponents against the pad. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.SymFr

/-- The fixed fields' `X³` constant. -/
noncomputable def cF1 (l : Literals) (alg : RepairRepresentation.DecompositionAlgorithm) : ℕ := cDa alg + 2 * cT l + 40

/-- The sum of the `S` coefficients of the HASH child's exponents. -/
noncomputable def hashB (l : Literals) (alg : RepairRepresentation.DecompositionAlgorithm) (c : SymC) : ℕ :=
  11 * c.dC + 41 * (1 + 8 * cF1 l alg) + 11 * C1H l alg c + 4 * (2 + 8 * cW2 l) + (16 + 64 * cS l) + 64

/-- **The HASH child's load floor** (`costCDH ≤ C_D`, fixed before `F`). -/
noncomputable def costCDH (l : Literals) (alg : RepairRepresentation.DecompositionAlgorithm) (c : SymC) : ℕ :=
  64 * hashB l alg c

end NearCubicWires.WireExponent3_5.FinalPass.HashFr

end
