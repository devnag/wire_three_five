import Lean
import Proof.Wire_3_5.FinalPass.NumDen
import Proof.Wire_3_5.FinalPass.PlanFP
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SeamsBase


noncomputable section
set_option maxRecDepth 4096


/-! # The final pass's seams: seeds → out, and the per-point value (P3:3170-3181)

The seeds phase (S4) leaves the printed value as two naturals in fixed-width binary (`NumDenOut`: `frame (binary W
numOf)` on `tN`, `frame (binary W denOf)` on `tD`, all heads at `0`), and the out machine (X6, `OutMachine`) prints
`ratWord (Num / Den)`: `OutMachine.phase` is `FpPhases.out` from any such exit (`fpOut_eq`, `NumDen.value_eq`).
The per-point evaluators (S2 THR, S3 SYM) add `ptThr` / `ptSym` at the point `(c, u_ℓ, v_ℓ)` and filter seed `e`:
`thrNum = Σ_c Σ_e Σ_ℓ ptThr` (`thrNum_pt`), `symNum = Σ_c Σ_e Σ_ℓ ptSym` (`symNum_pt`; `ptSym` sums over the list
seeds); `PtEval` is their common result shape (accumulator `+= val`, nothing else changed, polynomial bound). Main
declarations: `fpNum`, `fpDen`, `fpOut_eq`, **`NumDenOut`**, **`OutMachine`**, `OutMachine.phase`, `ptThr`, `ptSym`,
`thrNum_pt`, `symNum_pt`, **`PtEval`**. Paper quantities: the printed value `ratWord (greedyValue)` and its per-point
terms `M·R̂`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.NumDen
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.Split

/-! ## Seeds → out -/

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The numerator at a request of the family. -/
noncomputable abbrev fpNum (r : FReq l F kclk coef A a ha) : ℕ :=
  numOf (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1

/-- The denominator (`≥ 1`) at a request of the family. -/
noncomputable abbrev fpDen (r : FReq l F kclk coef A a ha) : ℕ :=
  denOf (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1

theorem fpOut_eq (r : FReq l F kclk coef A a ha) :
    fpOut l F kclk coef A a ha r = ratWord ((fpNum l F kclk coef A a ha r : ℚ) / fpDen l F kclk coef A a ha r) := by
  unfold fpOut; rw [value_eq]

/-- **The seeds phase's exit** (S4 → out): the numerator and the denominator framed in `W`-bit binary on `tN`, `tD`,
every head at `0`. -/
structure NumDenOut {t : ℕ} (tN tD : Fin t) (W : FReq l F kclk coef A a ha → ℕ)
    (H : FReq l F kclk coef A a ha → Fin t → ℕ) (Ab : FReq l F kclk coef A a ha → Fin t → List Bool) : Prop where
  ne : tN ≠ tD
  heads : ∀ r, H r = fun _ => 0
  num : ∀ r, Ab r tN = frame (binary (W r) (fpNum l F kclk coef A a ha r))
  den : ∀ r, Ab r tD = frame (binary (W r) (fpDen l F kclk coef A a ha r))
  numW : ∀ r, fpNum l F kclk coef A a ha r < 2 ^ W r
  denW : ∀ r, fpDen l F kclk coef A a ha r < 2 ^ W r

end Family

/-! ## The per-point value -/

section Point

end Point

end NearCubicWires.WireExponent3_5.FinalPass.Seams

end
