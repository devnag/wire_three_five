import Lean
import Proof.Wire_3_5.FinalPass.FreeGen5
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB
import Proof.Wire_3_5.Primitive.Writers.HashFam
import Proof.Wire_3_5.Primitive.Writers.CallIndexRBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SymSz1Base


noncomputable section
set_option maxRecDepth 4096


/-! # The SYM free numbers (root #145 (ii)), part 1: the star width against `c_r`

"`k = r·⌊log₂(n/r+1)⌋`" with "`r = 2(⌊log₂L⌋ + c_r)`" (P3:1188-1189) and the call's sizes `2^{O(k)}poly(n)`
(P3:3105-3115): at a SYM call, the ledger's `c_r` is at most `k/4`, so the sizes of the call are below `2^{e(k+L)}`
for exponents `e` of the literals and `fe` alone (the floors of #148, chosen before `F`, do not read `c_r`).

* `capK_le`, `cK`, **`symKI_le`** (`symKI c_r ≤ 2^{cK(c_r+1)}`);
* `k_le_L2`, `L_le_k`, **`cr_le_k`** (`4c_r ≤ k`), `kh_two`, `n2_le_L`, `pow_N_le`, **`symKI_kL`**.

Paper quantities of the main types: `c_r` and `symKI c_r` against the star width `k` and `L = ⌈log₂(n+2)⌉`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem k_le_L2 {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ((gate0 l F).budget kclk coef A a ha).kOf n ≤ Nat.clog 2 (n + 2) ^ 2 := hs.2.2.2.2

/-- **`4c_r ≤ k`**: `r = 2(⌊log₂L⌋ + c_r) ≥ 2c_r` and `⌊log₂(n/r+1)⌋ ≥ 2` (`4r ≤ n`). -/
theorem cr_le_k {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    4 * F.cr ≤ ((gate0 l F).budget kclk coef A a ha).kOf n := by
  have hr2 : 2 ≤ ((gate0 l F).budget kclk coef A a ha).rOf n := hs.2.1
  have hr4 : 4 * ((gate0 l F).budget kclk coef A a ha).rOf n ≤ n := hs.2.2.1
  have hk : ((gate0 l F).budget kclk coef A a ha).kOf n =
      ((gate0 l F).budget kclk coef A a ha).rOf n * Nat.log 2 (n / ((gate0 l F).budget kclk coef A a ha).rOf n + 1) :=
    rfl
  have hrr : ((gate0 l F).budget kclk coef A a ha).rOf n = 2 * (Nat.log 2 (Ledger.Lq n) + F.cr) := rfl
  obtain ⟨r, hrd⟩ : ∃ r, r = ((gate0 l F).budget kclk coef A a ha).rOf n := ⟨_, rfl⟩
  rw [← hrd] at hr2 hr4 hk hrr
  have hdiv : 4 ≤ n / r := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hlog : 2 ≤ Nat.log 2 (n / r + 1) := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  rw [hk]
  calc 4 * F.cr ≤ r * 2 := by omega
    _ ≤ r * Nat.log 2 (n / r + 1) := Nat.mul_le_mul_left _ hlog

theorem kh_two {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    2 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) = ((gate0 l F).budget kclk coef A a ha).kOf n :=
  HashFam.fam_two_kh l F kclk coef A a ha hs

end Call

/-- `symKI c_r ≤ 2^{cK(k+L)}` at an on-star length (`c_r + 1 ≤ k/4 + 1 ≤ k + L`). -/
theorem symKI_kL (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    CallIndexR.symKI F.cr ≤ 2 ^ (cK * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))) := by
  have h1 := cr_le_k l F kclk coef A a ha hs
  have h2 := one_le_L n
  exact (symKI_le F.cr).trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega)))

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

end
