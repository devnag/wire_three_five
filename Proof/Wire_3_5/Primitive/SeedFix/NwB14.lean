import Lean
import Proof.Wire_3_5.Primitive.SeedFix.NwB13
import Proof.Wire_3_5.FinalPass.S5TNum3Base
import Proof.Wire_3_5.FinalPass.S5TJoin2Base
import Proof.Wire_3_5.Primitive.SeedFix.TS4KBase
import Proof.Wire_3_5.Primitive.SeedFix.FlipsSetup
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.SymNeed
import Proof.Wire_3_5.Primitive.SeedFix.NwBT
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ5
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.NwB14Base


noncomputable section
set_option maxRecDepth 4096


/-! # T3 NW phase (b), part 14: the constants of phase (b)'s term

From `NeedB l` (X6: every number phase (b)'s registers hold is at most `K_n(F)·X^{D_n(f_e)}`, `X = |fpIn| + 1`):
**`KbB`**, **`DbB`** (the capacity's coefficient and exponent: `64(U+1)²·(X+2)^{C_sp+3} ≤ K_b·X^{D_b}` with
`U = K_n X^{D_n} + X + c_F`, **`cap_le`**), and **`capNeed_mono`**.

Paper quantity of the main types: phase (b)'s capacity, polynomial in the input (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline

section Consts
variable (l : Literals) (hN : NeedB l)

/-- X6's capacity coefficient. -/
noncomputable def KnX : GateFree l → ℕ := Classical.choose hN
/-- X6's capacity exponent. -/
noncomputable def DnX : ℕ → ℕ := Classical.choose (Classical.choose_spec hN)

theorem atomsX (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hc : (callInputs l F kclk coef A a ha).Call ⟨n, .thr, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    AtomsB l F kclk coef A a ha hs Cs carriers
      (KnX l hN F * ((FinalPass.PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩).length + 1) ^ DnX l hN F.filterErrDeg)
      (FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨_, hc⟩) :=
  Classical.choose_spec (Classical.choose_spec hN) F kclk coef A a ha n a' ha' Cs carriers translation hc hs

/-- The gate's constants the programs meet (`f_e`, `c_r`, W6's `C_n`, the schedule's `J`). -/
noncomputable def cstB (F : GateFree l) : ℕ := F.filterErrDeg + F.cr + (ThrDecF.NW l).Cn + SymSizes.schedJ l + 1000

/-- **The capacity's coefficient.** -/
noncomputable def KbB (F : GateFree l) : ℕ := 64 * (KnX l hN F + cstB l F + 2) ^ 2 * 3 ^ (gateCsp l + 3)

/-- **The capacity's exponent.** -/
noncomputable def DbB (fe : ℕ) : ℕ := 2 * (DnX l hN fe + 1) + (gateCsp l + 3)

/-- **The capacity dominates** `64(U+1)²·(X+2)^{C_sp+3}`. -/
theorem cap_le (F : GateFree l) (X : ℕ) (hX : 1 ≤ X) :
    64 * ((KnX l hN F * X ^ DnX l hN F.filterErrDeg + X + cstB l F) + 1) ^ 2 * (X + 2) ^ (gateCsp l + 3) ≤
      KbB l hN F * X ^ DbB l hN F.filterErrDeg := by
  obtain ⟨K, hK⟩ : ∃ K, K = KnX l hN F := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = DnX l hN F.filterErrDeg := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = cstB l F := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = gateCsp l + 3 := ⟨_, rfl⟩
  have hXD : X ^ D ≤ X ^ (D + 1) := Nat.pow_le_pow_right hX (by omega)
  have hX1 : X ≤ X ^ (D + 1) := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ (D + 1) := Nat.pow_le_pow_right hX (by omega)
  have hP1 : 1 ≤ X ^ (D + 1) := Nat.one_le_pow _ _ (by omega)
  have hU : K * X ^ D + X + s + 1 ≤ (K + s + 2) * X ^ (D + 1) := by
    have a1 : K * X ^ D ≤ K * X ^ (D + 1) := Nat.mul_le_mul_left _ hXD
    have a2 : s + 1 ≤ (s + 1) * X ^ (D + 1) := Nat.le_mul_of_pos_right _ hP1
    have e : (K + s + 2) * X ^ (D + 1) = K * X ^ (D + 1) + X ^ (D + 1) + (s + 1) * X ^ (D + 1) := by ring
    omega
  have hU2 : (K * X ^ D + X + s + 1) ^ 2 ≤ (K + s + 2) ^ 2 * X ^ (2 * (D + 1)) := by
    calc (K * X ^ D + X + s + 1) ^ 2 ≤ ((K + s + 2) * X ^ (D + 1)) ^ 2 := Nat.pow_le_pow_left hU 2
      _ = (K + s + 2) ^ 2 * X ^ (2 * (D + 1)) := by rw [mul_pow, ← pow_mul, mul_comm (D + 1) 2]
  have hS : (X + 2) ^ E ≤ 3 ^ E * X ^ E := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have eDb : DbB l hN F.filterErrDeg = 2 * (D + 1) + E := by rw [hD, hE]; rfl
  have eKb : KbB l hN F = 64 * (K + s + 2) ^ 2 * 3 ^ E := by rw [hK, hs, hE]; rfl
  rw [eDb, eKb, ← hK, ← hD, ← hs, ← hE]
  calc 64 * (K * X ^ D + X + s + 1) ^ 2 * (X + 2) ^ E
      ≤ 64 * ((K + s + 2) ^ 2 * X ^ (2 * (D + 1))) * (3 ^ E * X ^ E) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hU2) hS
    _ = 64 * (K + s + 2) ^ 2 * 3 ^ E * X ^ (2 * (D + 1) + E) := by rw [pow_add]; ring

end Consts

section Run2
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec

end Run2

end NearCubicWires.WireExponent3_5.PrimT.NwB

end
