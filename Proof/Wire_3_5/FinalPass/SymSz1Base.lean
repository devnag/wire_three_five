import Proof.Wire_3_5.FinalPass.FreeGen5
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB
import Proof.Wire_3_5.Primitive.Writers.HashFamBase
import Proof.Wire_3_5.Primitive.Writers.CallIndexRBase

/-! # The SYM free numbers (root #145 (ii)), part 1: the star width against `c_r`

"`k = r·⌊log₂(n/r+1)⌋`" with "`r = 2(⌊log₂L⌋ + c_r)`" (P3:1188-1189) and the call's sizes `2^{O(k)}poly(n)`
(P3:3105-3115): at a SYM call, the ledger's `c_r` is at most `k/4`, so the sizes of the call are below `2^{e(k+L)}`
for exponents `e` of the literals and `fe` alone (the floors of, chosen before `F`, do not read `c_r`).

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

/-- `capK c_r ≤ 2^{48(c_r+1)}`. -/
theorem capK_le (cr : ℕ) : CallIndexR.capK cr ≤ 2 ^ (48 * (cr + 1)) := by
  have h1 : cr < 2 ^ cr := Nat.lt_two_pow_self
  have h2 : 2 * cr + 2 ≤ 2 ^ (cr + 1) := by rw [pow_succ]; omega
  calc CallIndexR.capK cr = (2 * cr + 2) ^ 48 := rfl
    _ ≤ (2 ^ (cr + 1)) ^ 48 := Nat.pow_le_pow_left h2 48
    _ = 2 ^ (48 * (cr + 1)) := by rw [← pow_mul, Nat.mul_comm]

/-- The exponent of `symKI`. -/
def cK : ℕ := 306684

theorem symKI_eq (cr : ℕ) : CallIndexR.symKI cr =
    (8 * CallIndexR.capK cr) ^ 6000 * (2 ^ 36 * (16384 * CallIndexR.capK cr) ^ 4 * 2 ^ 400) := by
  unfold CallIndexR.symKI CallIndexR.gapK CallIndexR.flatK
  rw [CallIndexR.k6_eq, CallIndexR.k36_eq, CallIndexR.k4_eq]

theorem pow_mono_mul {x y : ℕ} (e : ℕ) (h : x ≤ 2 ^ y) : x ^ e ≤ 2 ^ (e * y) := by
  calc x ^ e ≤ (2 ^ y) ^ e := Nat.pow_le_pow_left h e
    _ = 2 ^ (e * y) := by rw [← pow_mul, Nat.mul_comm]

/-- **`symKI c_r ≤ 2^{cK(c_r+1)}`**. -/
theorem symKI_le (cr : ℕ) : CallIndexR.symKI cr ≤ 2 ^ (cK * (cr + 1)) := by
  have hc := capK_le cr
  obtain ⟨E, hE⟩ : ∃ E, E = 48 * (cr + 1) := ⟨_, rfl⟩
  rw [← hE] at hc
  obtain ⟨X, hX⟩ : ∃ X, X = CallIndexR.capK cr := ⟨_, rfl⟩
  rw [← hX] at hc
  have h8 : 8 * X ≤ 2 ^ (E + 3) := by rw [pow_add]; omega
  have h16 : 16384 * X ≤ 2 ^ (E + 14) := by rw [pow_add]; omega
  have g1 := pow_mono_mul 6000 h8
  have g2 := pow_mono_mul 4 h16
  rw [symKI_eq, ← hX]
  obtain ⟨A1, hA1⟩ : ∃ A, A = (8 * X) ^ 6000 := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A, A = (16384 * X) ^ 4 := ⟨_, rfl⟩
  rw [← hA1] at g1 ⊢
  rw [← hA2] at g2 ⊢
  have e2 : (2 : ℕ) ^ 36 * 2 ^ (4 * (E + 14)) * 2 ^ 400 = 2 ^ (36 + 4 * (E + 14) + 400) := by
    rw [pow_add, pow_add]
  calc A1 * (2 ^ 36 * A2 * 2 ^ 400) ≤ 2 ^ (6000 * (E + 3)) * (2 ^ 36 * 2 ^ (4 * (E + 14)) * 2 ^ 400) :=
        Nat.mul_le_mul g1 (Nat.mul_le_mul (Nat.mul_le_mul_left _ g2) le_rfl)
    _ = 2 ^ (6000 * (E + 3) + (36 + 4 * (E + 14) + 400)) := by rw [e2, ← pow_add]
    _ ≤ 2 ^ (cK * (cr + 1)) := Nat.pow_le_pow_right (by norm_num) (by unfold cK; omega)

section Call

end Call

theorem n2_le_L (n : ℕ) : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) := Nat.le_pow_clog (by norm_num) _

theorem one_le_L (n : ℕ) : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by norm_num) (by omega)

/-- `(n+2)^Z ≤ 2^{Z·L}`. -/
theorem pow_N_le (n Z : ℕ) : (n + 2) ^ Z ≤ 2 ^ (Z * Nat.clog 2 (n + 2)) := pow_mono_mul Z (n2_le_L n)

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

