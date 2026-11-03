import Lean
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.Primitive.Writers.Plan
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.FpInLenBase


noncomputable section
set_option maxRecDepth 4096


/-!
# The final pass reads at least `n` bits (root, for the S4 register capacity and the S5 `len_le`)

"The seeds a call fixes before its final pass" (P3:3165-3175) include `samp:printable`'s greedy sample, printed as
`Q` pairs of `kh`-bit halves, with `Q = 2^{⌊(5kh+3)/4⌋}·2^{13}·I·n^{2D}` (`Sampler.sampleCount`, P3:2994-3000). Every
call of the family is on-star (`PrimitiveInputs.Call` contains `StarAt`), so the final pass's input
`fpIn = req.word ++ seedWord` carries the whole sample, and `Q ≥ n` because `D ≥ 1` and `I ≥ 1`. Hence
`n ≤ |fpIn|`: every register bound polynomial in `n` is polynomial in `|fpIn|`, and the shared register capacity
`Kc·(|fpIn|+1)^Dc` of `SeedsWS2` / `S5Seam2` can hold `n`, the table lengths and the unary request.

Paper quantity of the main type: `n`, the call's input length, against the final pass's input word `fpIn`.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.FpInLen
open NearCubicWires NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Primitive

section Family
variable {l : Literals} {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}

/-- **`n ≤ |fpIn|`** at every request of every call family: the final pass's input word carries the printed sample. -/
theorem n_le_fpIn (r : PlanFP.FReq l F kclk coef A a ha) : r.1.n ≤ (PlanFP.fpIn l F kclk coef A a ha r).length := by
  unfold PlanFP.fpIn
  rw [List.length_append]
  exact le_trans (n_le_seedWord _ _ r.1 r.2.2.2.2.2.2.1) (Nat.le_add_left _ _)

end Family

end NearCubicWires.WireExponent3_5.FinalPass.FpInLen

end
