import Lean
import Proof.Wire_3_5.FinalPass.S5TJoin2Base
import Proof.Wire_3_5.Primitive.SeedFix.TS4K
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.S5TChA
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.SeedFix.TS4N
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.FinalPass.S5TNum1Base


noncomputable section
set_option maxRecDepth 120000


/-! # S5-THR, part 35: the stage's costs below one power (P3:3105-3115)

Every piece of the THR stage's cost at arguments `≤ Z` (one bound for the request's sizes and numbers, `Z` a power of
the padded count base): a polynomially bounded piece of degree `≤ H` and coefficient `≤ Z` costs at most
`Z^{2H+1}` (**`pw_Z`**, **`pb_Z`**); the parse `≤ 6000·Z²` (**`parse_le`**); the first docks (the prep, W6)
`≤ Z^{2H+2}` (**`chainA_le`**); the next docks (the top front, the data stage) `≤ Z^{2H+2}` (**`chainB_le`**); the
tail `≤ 19062·Z⁵` (**`tail_le`**); the whole THR stage `≤ Z^{2H+3}` (**`stageThr_le`**).

Paper quantity of the main type: the front's running time as a power of the call's size, the powers fixed before
the gate (P3:3114-3115). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed
open NearCubicWires.SupplierPipeline

section Calc

end Calc

section Pieces

variable (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ)

/-- **The first docks' cost** (the prep, W6) at `n, W_p, (n+1)^{26}, cap_T ≤ Z`. -/
theorem chainA_le (l : Literals) (cr n a nc Wp Z H : ℕ) (hZ : 30 ≤ Z) (hH : 1 ≤ H) (ha : a ≤ 4) (hnc : nc ≤ 2) (hn : n ≤ Z)
    (hW : Wp ≤ Z) (h26 : (n + 1) ^ 26 ≤ Z) (hcap : PrimT.TS4.capTL l cr n ≤ Z) (hKp : PrimT.TS4.Kp l cr ≤ Z)
    (hDp : PrimT.TS4.Dp l ≤ H) (hC6 : (PrimT.W6.numsW6 alg Dexp).Cc ≤ Z) (hD6 : (PrimT.W6.numsW6 alg Dexp).Dc ≤ H) :
    chainACost alg Dexp l cr n a nc Wp ≤ Z ^ (2 * H + 2) := by
  unfold chainACost
  have hp := pw_Z (by omega) (PrimT.TS4.p0Stage_le l cr n Wp a nc ha hnc) (by omega) hKp hDp
  have h6 := pb_Z (by omega) ((PrimT.W6.numsW6 alg Dexp).cost_poly (n + (Wp + (n + 1) ^ 26) + PrimT.TS4.capTL l cr n))
    (by omega) hC6 hD6
  have hz : Z ^ 2 ≤ Z ^ (2 * H + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hz2 : 30 * Z ≤ Z ^ 2 := by nlinarith
  have hs : 30 * Z ^ (2 * H + 1) ≤ Z ^ (2 * H + 2) := mul_pow_le (by omega)
  omega

end Pieces

end NearCubicWires.WireExponent3_5.FinalPass.S5T

end
