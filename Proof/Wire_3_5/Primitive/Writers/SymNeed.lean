import Proof.Wire_3_5.Primitive.Writers.SymNOnly

/-! # SYM leaf, part 6: the length-only quantities at the gate, polynomially

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
