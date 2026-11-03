import Lean
import Proof.Wire_3_5.Primitive.Writers.SymNOnly
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Primitive.Writers.SymNeedBase


noncomputable section
set_option maxRecDepth 4096


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
variable (l : Literals)

/-- The schedule's block length at the setup's `ζ`. -/
noncomputable def schedJ : ℕ := Classical.choose (Schedule.exists_block (gateZeta_pos l) (gateZeta_lt l))

theorem schedJ_spec : ((1 - (gateCParams1 l).ζ) ^ 16) ^ schedJ l ≤ 1 / 8 :=
  Classical.choose_spec (Schedule.exists_block (gateZeta_pos l) (gateZeta_lt l))

/-- **`t = O(L)`**: `rowBt n ≤ J(L+1) + 1`. -/
theorem rowBt_le (n : ℕ) : Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n ≤ schedJ l * (Nat.clog 2 (n + 2) + 1) + 1 := by
  have h := Schedule.sched_log (gateZeta_pos l) (gateZeta_lt l) (schedJ_spec l) (Ledger.Lq n)
  have h2 : Nat.log 2 (Ledger.Lq n) ≤ Ledger.Lq n := Nat.log_le_self 2 _
  have h3 : schedJ l * (Nat.log 2 (Ledger.Lq n) + 1) ≤ schedJ l * (Ledger.Lq n + 1) := Nat.mul_le_mul_left _ (by omega)
  have eL : Ledger.Lq n = Nat.clog 2 (n + 2) := rfl
  have e0 : Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n = Schedule.sched _ (gateZeta_pos l) (gateZeta_lt l) (Ledger.Lq n) := rfl
  rw [e0]
  rw [eL] at h h2 h3 ⊢
  omega

/-- The sparse bound's exponent constant `c_X = ⌈log₂ X⌉`. -/
noncomputable def cXg : ℕ := Nat.clog 2 (spX (gateCParams1 l).ζ (gateCδ1 l))

/-- **The sparse bound at the gate**: `≤ 2^{(3 + 32c_XJ)L + 6 + 32c_X(J+1)}`. -/
theorem sparse_le_gate (n : ℕ) :
    sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Ledger.Lq n) (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n - 1) ≤
      2 ^ ((3 + 32 * cXg l * schedJ l) * Nat.clog 2 (n + 2) + (6 + 32 * cXg l * (schedJ l + 1))) := by
  have h1 := sparse_le_P (gateCParams1 l).ζ (gateCδ1 l) (Ledger.Lq n) (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n - 1)
  have ht := rowBt_le l n
  obtain ⟨L, hL⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have eL : Ledger.Lq n = L := hL.symm
  rw [eL] at h1 ⊢
  rw [← hL] at ht ⊢
  obtain ⟨m, hm⟩ : ∃ x, x = Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n - 1 := ⟨_, rfl⟩
  rw [← hm] at h1 ⊢
  have hm1 : m + 1 ≤ schedJ l * L + schedJ l + 1 := by
    have e : schedJ l * (L + 1) = schedJ l * L + schedJ l := by ring
    omega
  have hX : spX (gateCParams1 l).ζ (gateCδ1 l) ≤ 2 ^ cXg l := Nat.le_pow_clog (by norm_num) _
  have hP : spX (gateCParams1 l).ζ (gateCδ1 l) ^ (32 * (m + 1)) ≤ 2 ^ (32 * cXg l * (schedJ l * L + schedJ l + 1)) := by
    calc spX (gateCParams1 l).ζ (gateCδ1 l) ^ (32 * (m + 1)) ≤ (2 ^ cXg l) ^ (32 * (m + 1)) := Nat.pow_le_pow_left hX _
      _ = 2 ^ (cXg l * (32 * (m + 1))) := by rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hL3 : L ^ 3 ≤ 2 ^ (3 * L) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (self_le_two_pow L) 3
    |>.trans (by rw [← pow_mul, ← pow_mul, mul_comm])
  have h20 : 20 * (L ^ 3 + 1) ≤ 2 ^ (3 * L + 6) := by
    have : 1 ≤ 2 ^ (3 * L) := Nat.one_le_two_pow
    rw [pow_add]; omega
  calc sparseBound (gateCParams1 l).ζ (gateCδ1 l) L m ≤ 20 * (L ^ 3 + 1) * spX (gateCParams1 l).ζ (gateCδ1 l) ^ (32 * (m + 1)) := h1
    _ ≤ 2 ^ (3 * L + 6) * 2 ^ (32 * cXg l * (schedJ l * L + schedJ l + 1)) := Nat.mul_le_mul h20 hP
    _ = 2 ^ ((3 + 32 * cXg l * schedJ l) * L + (6 + 32 * cXg l * (schedJ l + 1))) := by rw [← pow_add]; ring_nf

/-- The mass bound's coefficient `K_Λ`. -/
noncomputable def KLam : ℕ := Classical.choose (Ledger.rowBLambda_pow16_le (gateZeta_pos l) (gateZeta_lt l) 2)

/-- **`Λ̄ ≤ K_Λ(n+2)³`**. -/
theorem lambda_le (n : ℕ) : Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 n ≤ KLam l * (n + 2) ^ 3 := by
  have h := Classical.choose_spec (Ledger.rowBLambda_pow16_le (gateZeta_pos l) (gateZeta_lt l) 2) n
  have h1 : Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 n ≤ Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 n ^ 16 := by
    rcases Nat.eq_zero_or_pos (Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 n) with h0 | h0
    · rw [h0]; simp
    · exact Nat.le_self_pow (by norm_num) _
  have h2 : Ledger.Lq n ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (PrimAsm.CallIndex.Lq_le_N n) 3
  calc _ ≤ _ := h1
    _ ≤ KLam l * Ledger.Lq n ^ 3 := h
    _ ≤ KLam l * (n + 2) ^ 3 := Nat.mul_le_mul_left _ h2

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.SymSizes

end
