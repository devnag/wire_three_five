import Lean
import Proof.Wire_3_5.FinalPass.SeamsBase
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SeamsPtBase


noncomputable section
set_option maxRecDepth 4096


/-! # The final pass's seams, part 2: the per-point evaluators, the front's exit, the cost residual

Consumer backward from `NumDenOut` (P3:3170-3181): `Num = Σ_c Σ_e Σ_ℓ M(e, x)·Σ R̂(x)` at `x = (c, u_ℓ, v_ℓ)`.
`R̂` does not depend on the filter seed `e` (`thrRhat`, `symRhatFast` take no seed) and the mask `M` is the SAME
function in both modes (`maskBits`), so the point value factors (`ptThr_mask`, `ptSym_mask`): the per-point
evaluators (S2 THR, S3 SYM) compute `Σ R̂` alone (`rsumThr`, `rsumSym`), and the seeds phase (S4) computes the mask
once per point and seed (stage 7 on the seed's table) and adds `M·Σ R̂` to its binary accumulator.

* **`PtIn`** / **`PtOut`**: the per-point evaluator's entry and exit at a generic layout. Streams: the point
  `frame (ofFn c)`, `frame (ofFn e_L(u))`, `frame (ofFn e_R(v))` (stage 2's `C, U, V`; the center stream is X3's
  `ctrW` output, `frame_eq_frameP`), the evaluator's call words (read-only), its scratch streams (reading blank:
  every cell `false`); all these heads at `0`. Registers: the accumulator and the scratch registers zero, the call
  numbers. Exit: the accumulator holds `v`, every head and every other register as at entry, every stream outside
  the scratch unchanged, the scratch reading blank again (loop-safe).
* **`PtEvalW`**: one evaluator per mode; it DECLARES its call words and numbers (the words the front must leave),
  with capacity and cost polynomial in `ptSize` (the point, the words, the numbers). S2 is
  `PtEvalW ThrCall … rsumThr`, S3 is `PtEvalW SymCall … rsumSym`.
* **`FrontOut`** (S5 → S4): the front's exit bank at a request: the declared words on their tapes, the numbers in
  `W`-bit binary (`frame (binary W v)`, C6's `NumOn` form), every other tape `false` of the declared length `bl`
  (S4's register tapes), every head at `0`.
* **`ptCount`**, **`seedCount`**, **`FitsRes`**, `fits_of` (S6): the phases' cost bounds against `c₅·finalClasses`,
  with the seeds phase's bound in the shape `|E|·tab + (|centers|·|E|·Q)·pt + ov` (`seedsShape`).

Paper quantities: the per-point sums `Σ_{g,p} R̂_{g,p}` and `Σ_{e'} R̂_{e'}`, the mask `M(e, x)`, the numbers of
seeds and of point evaluations, the budget `c₅·finalClasses`. -/

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

/-! ## The per-point sums and the mask factor -/

section Point

end Point

/-! ## The per-point evaluator's entry, exit and type -/

section Eval

end Eval

/-! ## S5 → S4: the front's exit -/

section Family
variable (l : Literals) (F : GateFree l) (E₅ : Envelope) (c₅ kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The front's exit bank** (S5 → S4) at a layout `wd` (words), `nm` (numbers): at every request, the words
`ws r k` on tape `wd k`, the numbers `vs r i` in `W r`-bit binary on tape `nm i`, every other tape `j` all `false`
of length `bl r j` (S4's register tapes), every head at `0`. The words and numbers are the ones S2, S3 and S4
declare (`PtEvalW.words`, `PtEvalW.nums`, S4's own). -/
structure FrontOut {t nw nn : ℕ} (wd : Fin nw → Fin t) (nm : Fin nn → Fin t)
    (ws : FReq l F kclk coef A a ha → Fin nw → List Bool) (vs : FReq l F kclk coef A a ha → Fin nn → ℕ)
    (W : FReq l F kclk coef A a ha → ℕ) (bl : FReq l F kclk coef A a ha → Fin t → ℕ)
    (H : FReq l F kclk coef A a ha → Fin t → ℕ)
    (Ab : FReq l F kclk coef A a ha → Fin t → List Bool) : Prop where
  inj : ∀ k i, wd k ≠ nm i
  wdInj : Function.Injective wd
  nmInj : Function.Injective nm
  heads : ∀ r, H r = fun _ => 0
  words : ∀ r k, Ab r (wd k) = ws r k
  nums : ∀ r i, Ab r (nm i) = frame (binary (W r) (vs r i))
  numW : ∀ r i, vs r i < 2 ^ W r
  blank : ∀ r j, (∀ k, j ≠ wd k) → (∀ i, j ≠ nm i) → Ab r j = List.replicate (bl r j) false

/-! ## S6: the cost residual -/

/-- **The number of filter seeds** at a request. -/
noncomputable def seedCount (r : FReq l F kclk coef A a ha) : ℕ :=
  Fintype.card (GapSeed ((callInputs l F kclk coef A a ha).filterParams r.1.mode r.1.n))

/-- The number of point evaluations at a request of the family. -/
noncomputable abbrev ptCount (r : FReq l F kclk coef A a ha) : ℕ :=
  ptCountOf (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1

/-- **S6, the cost residual** (C6b): the phases' cost bounds fit `c₅·finalClasses` at every request. -/
def FitsRes (fB sB oB : FReq l F kclk coef A a ha → ℕ) : Prop :=
  ∀ r, fB r + 1 + (sB r + 1 + oB r) ≤ fpBudget l F E₅ c₅ kclk coef A a ha r

/-- **`fpPlan`'s `fits` from the residual**: phases within `fB`, `sB`, `oB`, and `FitsRes`. -/
theorem fits_of (X : FpPhases l F kclk coef A a ha) (fB sB oB : FReq l F kclk coef A a ha → ℕ)
    (hf : ∀ r, X.front.cost r ≤ fB r) (hs : ∀ r, X.seeds.cost r ≤ sB r) (ho : ∀ r, X.out.cost r ≤ oB r)
    (h : FitsRes l F E₅ c₅ kclk coef A a ha fB sB oB) :
    ∀ r, X.cost l F kclk coef A a ha r ≤ fpBudget l F E₅ c₅ kclk coef A a ha r := by
  intro r
  have h1 := hf r
  have h2 := hs r
  have h3 := ho r
  have h4 := h r
  unfold FpPhases.cost
  omega

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams

end
