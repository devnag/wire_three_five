import Proof.Wire_3_5.Primitive.Writers.SymNOnly

/-! # PA2 (SYM leaf), part 6: the length-only quantities at the gate, polynomially

At the gate `gate0 l F` (the setup's `ζ`, `C_δ`, the caps `gateCap l`, the multiplier `rowBr c_r`), every quantity the
SYM decode and dimension stage read from the length alone is `K·(n+2)^d` with `d` fixed by the literals `l` and
`K` after `F`:

* `schedJ` (`((1−ζ)^{16})^J ≤ 1/8`), **`rowBt_le`** (`t ≤ J(L+1) + 1`), **`sparse_le_gate`**
  (`≤ 2^{(3+32c_XJ)L + 6 + 32c_X(J+1)}`), `KLam`, **`lambda_le`** (`Λ̄ ≤ K_Λ(n+2)³`), **`tS_le_poly`**
  (`T ≤ K_T(n+2)^{Z+2}` at `D₂' = 26`, `K₀ = 6`).

Paper quantities of the main types: the schedule `t(q) = O(log L)` (P3:3742-3744), the sparse count and the mass
bound (P3:3400, 3690-3691, 3820-3821), the POP term `T`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymSizes
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.PrimAsm.SparseNum

section Gate

end Gate

/-- **The POP term at `D₂' = 26`, `K₀ = 6`, polynomially**: `T ≤ K_T(n+2)^{Z+2}` when `B_S ≤ capK(n+2)^Z`. -/
theorem tS_le_poly (capS capK Z n : ℕ) (hB : capS ≤ capK * (n + 2) ^ Z) :
    tSOf capS 26 6 (Nat.clog 2 (n + 2)) ≤
      32 * (196608 * (Nat.clog 2 capK + 23 + Z) * (capK + 1) + 1) * (n + 2) ^ (Z + 2) := by
  obtain ⟨L, hL⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hL]
  have hn2 : n + 2 ≤ 2 ^ L := by rw [hL]; exact Nat.le_pow_clog (by norm_num) _
  have hB2 : capS ≤ capK * 2 ^ (Z * L) := by
    calc capS ≤ capK * (n + 2) ^ Z := hB
      _ ≤ capK * (2 ^ L) ^ Z := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn2 _)
      _ = capK * 2 ^ (Z * L) := by rw [← pow_mul, mul_comm L]
  have h1 := tS_le capS capK Z L 26 6 hB2
  have hLn' : L ≤ n + 2 := by
    have := self_le_two_pow L
    rw [hL] at this ⊢
    exact PrimAsm.CallIndex.Lq_le_N n
  have hσ : Nat.sqrt capS + 1 ≤ (capK + 1) * (n + 2) ^ Z := by
    have a1 := Nat.sqrt_le_self capS
    have a2 : 1 ≤ (n + 2) ^ Z := Nat.one_le_pow _ _ (by omega)
    have e : (capK + 1) * (n + 2) ^ Z = capK * (n + 2) ^ Z + (n + 2) ^ Z := by ring
    omega
  have hlam : Nat.clog 2 capK + 23 + Z * L ≤ (Nat.clog 2 capK + 23 + Z) * (n + 2) := by
    have a1 : Z * L ≤ Z * (n + 2) := Nat.mul_le_mul_left _ hLn'
    have a2 : Nat.clog 2 capK + 23 ≤ (Nat.clog 2 capK + 23) * (n + 2) := Nat.le_mul_of_pos_right _ (by omega)
    have e : (Nat.clog 2 capK + 23 + Z) * (n + 2) = (Nat.clog 2 capK + 23) * (n + 2) + Z * (n + 2) := by ring
    omega
  have hD : L * 26 + 6 ≤ 32 * (n + 2) := by omega
  refine le_trans h1 ?_
  have a3 : 196608 * (Nat.clog 2 capK + 23 + Z * L) * (Nat.sqrt capS + 1) ≤
      196608 * ((Nat.clog 2 capK + 23 + Z) * (n + 2)) * ((capK + 1) * (n + 2) ^ Z) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hlam) hσ
  have a4 : (196608 * (Nat.clog 2 capK + 23 + Z * L) * (Nat.sqrt capS + 1) + 1) * (L * 26 + 6) ≤
      (196608 * ((Nat.clog 2 capK + 23 + Z) * (n + 2)) * ((capK + 1) * (n + 2) ^ Z) + 1) * (32 * (n + 2)) :=
    Nat.mul_le_mul (by omega) hD
  refine le_trans a4 ?_
  have a5 : 1 ≤ (n + 2) * (n + 2) ^ Z := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have e : (196608 * ((Nat.clog 2 capK + 23 + Z) * (n + 2)) * ((capK + 1) * (n + 2) ^ Z) + 1) * (32 * (n + 2)) =
      32 * (196608 * (Nat.clog 2 capK + 23 + Z) * (capK + 1)) * (n + 2) ^ (Z + 2) + 32 * (n + 2) := by ring
  have e2 : 32 * (196608 * (Nat.clog 2 capK + 23 + Z) * (capK + 1) + 1) * (n + 2) ^ (Z + 2) =
      32 * (196608 * (Nat.clog 2 capK + 23 + Z) * (capK + 1)) * (n + 2) ^ (Z + 2) + 32 * (n + 2) ^ (Z + 2) := by ring
  have a6 : n + 2 ≤ (n + 2) ^ (Z + 2) := by
    calc n + 2 = (n + 2) ^ 1 := (pow_one _).symm
      _ ≤ (n + 2) ^ (Z + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.SymSizes
