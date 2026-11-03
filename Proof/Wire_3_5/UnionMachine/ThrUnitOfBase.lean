import Proof.Wire_3_5.UnionMachine.ThrUnitMeas3Base

/-! # The producer statement v5, proved: `thrUnitOf5 l : ThrUnit.ThrUnitOf5 l`

From the walk bank `W`, the unit cells `xF F ≥ W.x`, the FILTER setup `FiltSetupSpec5 W`, its pipe bound
(`FiltPipeLe2`), the uniform decode fronts and RADIX setups (`RadSetupSpecB5`), the THR unit machines v4 in the
StageU order:

* the machine `ThrUnitRun.thrUnitM` (the decode ; RADIX 398 ; FILTER 399 ; the counter), the measure
  `2^{K_q·Ψ_T}` (`ThrMeas.Kq`: from `l`, `f_e`, the decode front's exponent bound, `D_f`, `D_t`), the need
  `needU (c·X)` and the budget `nUU (c·Y)` with the coefficient `c = C_n + C_b + 16K_t + 32 + K_f + 3` (after the gate);
* `need_le`, `nU_le` (explicit `K·(X+1)^D`, the exponents from the RADIX setup's and the FILTER setup's), `meas_le`
  (`K_m = K_q`, `D_m = 0`), **`ok`** (`ThrUnitRun.unit_ok` at `measC ≤ c·2^{K_q Ψ_T}`, `ThrMeas.measC_le`, the need and
  the budget monotone);
* **`thrUnitOf5 l`** (the family; floors `envMax` of the two families' and `C_D ≥ 1`; `K_t` from T's
  `ThrNumsPoly`, `K_f`, `D_f` from `FiltPipeLe2`).

Paper quantity of the main type: the THR tape's unit machines within the preprocessing class `2^{O(Ψ_T)}` (P3:3089-3108,
row:radix P3:2585-2623, row:matrix P3:1523-1526). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrUnitOf
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimT.WalkBank

/-! ## Monotone, polynomial -/

theorem unitOK_mono {cap x sU : ℕ} {U : Machine (PrimAsm.CellLoop.TT x) sU} {nU nU' : ℕ} {w u : List Bool}
    {emit : ℕ → List Bool} {j : ℕ} {out : List Bool} (h : PrimThrW.Shell.UnitOK cap x U nU w u emit j out)
    (hn : nU ≤ nU') : PrimThrW.Shell.UnitOK cap x U nU' w u emit j out := by
  obtain ⟨σE, mU, s, a1, a2, a3, a4, a5⟩ := h
  exact ⟨σE, mU, s, a1, a2, a3, a4, a5.trans hn⟩

theorem pw_le (c X d D : ℕ) (hd : d ≤ D) : (c * X + 1) ^ d ≤ (c + 1) ^ d * (X + 1) ^ D := by
  calc (c * X + 1) ^ d ≤ ((c + 1) * (X + 1)) ^ d := Nat.pow_le_pow_left (by nlinarith) d
    _ = (c + 1) ^ d * (X + 1) ^ d := mul_pow _ _ _
    _ ≤ (c + 1) ^ d * (X + 1) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hd)

section Gate



end Gate

/-! ## The unit machine at a gate -/

/-! ## The family -/

/-- `FiltPipeLe2`'s constants. -/
noncomputable def kfOf (hfp : BudgetIface.FiltPipeLe2) : ℕ := Classical.choose hfp
noncomputable def dfOf (hfp : BudgetIface.FiltPipeLe2) : ℕ := Classical.choose (Classical.choose_spec hfp)

theorem hKf_of (hfp : BudgetIface.FiltPipeLe2) : ∀ (P : GapParams) (e : GapSeed P) (L r4 G off : ℕ), 1 ≤ P.cap →
    FiltPipe.filtPipeBound P e L r4 G off (FiltSetup.rulerW P) (FiltSetup.rulerW P) ≤
      kfOf hfp * (P.len + P.cap + P.errExp + L + r4 + G + off + 2) ^ dfOf hfp * (L + 2) ^ (dfOf hfp * (P.errExp + 1)) :=
  Classical.choose_spec (Classical.choose_spec hfp)

theorem pow_mono2 {a b d e : ℕ} (hab : a ≤ b) (hde : d ≤ e) : (a + 1) ^ d ≤ (b + 1) ^ e :=
  (Nat.pow_le_pow_left (by omega) d).trans (Nat.pow_le_pow_right (by omega) hde)

/-- The family's coefficient (after the gate). -/
def C0 (Cd0 Cr0 Dr0 Kt Kf : ℕ) {W : WalkBankProducer} (F5 : FiltSetup.FiltSetupSpec5 W) : ℕ :=
  (Cd0 + (16 * Kt + 32) + Kf + 3) + Cr0 * (Cd0 + (16 * Kt + 32) + Kf + 3 + 1) ^ Dr0 +
      F5.Cn * (Cd0 + (16 * Kt + 32) + Kf + 3 + 1) ^ F5.Dn +
    (22 * (Cd0 + (16 * Kt + 32) + Kf + 3) + 23 + Cr0 * (Cd0 + (16 * Kt + 32) + Kf + 3 + 1) ^ Dr0 +
      Cr0 * (Cd0 + (16 * Kt + 32) + Kf + 3 + 1) ^ Dr0 + F5.Cb * (Cd0 + (16 * Kt + 32) + Kf + 3 + 1) ^ F5.Db)

end NearCubicWires.WireExponent3_5.UnionMachine.ThrUnitOf
