import Proof.Wire_3_5.UnionMachine.FrontSemC1CapBase

/-! # C6 front, the semantic core (18): the valid path's caps at a guess (P3:3669-3691)

**`pathCaps_of`**: `FrontSemPath.PathCaps` at a guess from its size envelope `GEnv g Λ K` (with `2·nv`, `2^{cb+2}`,
`3`, `r`, `c_r`, the atoms' and parities' description bits `≤ K`), the width `W = K_w(q+1)^{D_w}` above `PW K` and
C1's carrier preparation `CP·(K+2)^{51}`, the data bound above `BK K`, the fold's exponents (`foldCapsG`), and the
star hypotheses at `q`. `Vb := K`.

Paper quantity of the main type: every capacity the valid path's machines read at a guess. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPathCaps
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairRepresentation (natWord natListWord)
open NearCubicWires.BlockPlatform.UnaryCalc (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap1 (natWord_le natWord_bits)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap2 (BK PW pow2_bits bits_le pw_small)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldBound (eT)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemFold (eMt)

theorem pw_cube (K : ℕ) : 4 * (K * K * K) + 100 * (K * K) + 300 * K + 100 ≤ PW K := by
  unfold PW; ring_nf; omega

theorem pw_six (K : ℕ) : 200 * K ^ 6 + 20 * (K * K) + 50 * K + 100 ≤ PW K := by
  unfold PW; ring_nf; omega

section Guess

end Guess

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPathCaps
