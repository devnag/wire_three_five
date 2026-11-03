import Proof.Wire_3_5.FinalPass.SymCost2Base
import Proof.Wire_3_5.FinalPass.SymCost3
import Proof.Wire_3_5.FinalPass.SymDegBase

/-! # The SYM child's cost, part 4: `hcost` at a SYM call (generic in the batch)

P3:3011-3016, 1905-1906, 3098-3100: one child of a SYM call's family (the enumeration unit, C6's assembler, the printer
child) runs within `K_ch(n) = 2^{n − k + d_A L − 4}` steps at every prefix (`symKch`, a function of `n` alone: the star
width `kOf n` does not read the call family, `kF`). From the generic `EnumCap.hcost_of` at
`q = 2^{e_C + e_X}` (the capacity `Cap = 2^{e_C}` and the call's numbers `≤ 2^{e_X}`), `𝒮' ≤ 2^{c_O U}` (`symOcc_le`),
`B_n = bnOf` and the fixed fields `≤ 2^{e_F}` (`symFix_le`), `qG + 1 ≤ 2^{e_C}` (`symQ_of`), and the arithmetic
`kch_pow`/`kch_exp` under the floors `symHC ≤ C_D`, `symDAc ≤ d_A`. Generic in the batch (`R ≤ 10`, the
`BatchFacts`, the degree bounds), so the SYM batch and the degenerate call's padded batch are instances.

* `kF`, `symKch`, `eXOf`, **`symHcost_of`**.

Paper quantity of the main type: one SYM child's step count against the pad. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.RepairRepresentation

/-- The call's numbers' exponent. -/
def eXOf (cD dQ dD dH eH dP eP cO eNc eQc U L : ℕ) : ℕ :=
  3 * efOf cD dQ dD dH eH dP eP U L + (eNc + 8 * eQc + 24 + cO) * U + 9

section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
