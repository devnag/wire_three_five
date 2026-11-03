import Proof.Wire_3_5.FinalPass.SdR2Base

/-! # S4 v2, part R10: the runs at SYM and THR calls at the v2 constants

S4 v1's `Sd` part 10 (`capNeed_ge`, `ptc_sym`, `ptc_thr`, `sym_run`, `thr_run`) re-instantiated in namespace `Sd.R`, where the width `Tf`, the sizes' polynomial `Xf`
(`ZX`, `KX`) and their lemmas are S4 v2's (parts R2, R3: `CallIndexR`'s exponents on `(l, fe)`, `c_r` in the
coefficients); the statements and proofs are v1's, so S4 v2's degrees depend on `(l, fe)` alone.

Paper quantity of the main type: as in v1 (P3:3044-3048, 3114-3115, 3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd.R
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Split NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR)
open NearCubicWires.WireExponent3_5.PrimT.WalkBank (WalkBankProducer)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup (FiltSetupSpec5)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2 symCallOf thrCallOf thrWords thrNums)

theorem capNeed_ge (X Fn : ℕ) : X + 100 ≤ capNeed X Fn ∧ 10000 * (X * X * X) + 100 ≤ capNeed X Fn := by
  unfold capNeed
  rcases Nat.eq_zero_or_pos X with h | h
  · subst h; omega
  · have h1 : X ≤ X * X := Nat.le_mul_of_pos_left X h
    have h2 : X * X ≤ X * X * X := Nat.le_mul_of_pos_right _ h
    omega

section Family

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd.R

