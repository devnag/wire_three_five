import Proof.Wire_3_5.FinalPass.SdI4
import Proof.Wire_3_5.FinalPass.FpInLenBase

/-! # S4 (the seeds phase), part 54: the tables writer at a star call of the family (P3:2036-2101, 3170-3178)

The tables writer `TabW.tabM` at the constants `K₀ = KX`, `E₀ = ZX` (the sizes' polynomial read at the writer's
dimension `2^m + 1 ≥ n + 2`, `m = mOf P`): **`writer_run`**, its run (`TabW.tab_writer` with `TabW.tab_hyps`) at every
star call of the family, within the budget `budOf` (the writer shell's cost). The sample count against the input
(`q_le_fpIn_sym/thr`: `Q ≤ |fpIn|`) and the writer's dimension against the sample (`two_m_le`: `2^m ≤ Q²·(n+2)²`).

Paper quantity of the main type: the seeds' filter tables (`tabWord`, P3:2036-2101) on the writer's output. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Split NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimT.WalkBank (WalkBankProducer)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup (FiltSetupSpec5)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)

/-- The writer's dimension is past `n + 2`. -/
theorem n2_le_m (P : StarParams) : P.n + 2 ≤ 2 ^ PrimAsm.NumsX.mOf P + 1 := by
  have h1 : P.n + 2 ≤ 2 ^ Nat.clog 2 (P.n + 2) := Nat.le_pow_clog (by norm_num) _
  have h2 : 2 ^ Nat.clog 2 (P.n + 2) ≤ 2 ^ PrimAsm.NumsX.mOf P :=
    Nat.pow_le_pow_right (by norm_num) (by unfold PrimAsm.NumsX.mOf; omega)
  omega

/-- The writer's dimension against the sample count (`2^{kh} ≤ Q`). -/
theorem two_m_le (P : StarParams) (Q : ℕ) (hQ : 2 ^ SeedFix.callKh P ≤ Q) :
    2 ^ PrimAsm.NumsX.mOf P ≤ Q * Q * ((P.n + 2) * (P.n + 2)) := by
  have h2 : 2 ^ Nat.clog 2 (P.n + 2) ≤ (P.n + 2) ^ 2 := PrimAsm.CallIndex.two_pow_clog_le (by omega)
  have e : 2 ^ PrimAsm.NumsX.mOf P = 2 ^ SeedFix.callKh P * 2 ^ SeedFix.callKh P * 2 ^ Nat.clog 2 (P.n + 2) := by
    unfold PrimAsm.NumsX.mOf SeedFix.callKh
    rw [← pow_add, ← pow_add]; ring_nf
  rw [e, ← sq (P.n + 2)]
  exact Nat.mul_le_mul (Nat.mul_le_mul hQ hQ) h2

section Family


end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd

