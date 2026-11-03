import Proof.Wire_3_5.Assembly.FreeBase
import Proof.Wire_3_5.UnionMachine.UnionCodecBase
import Proof.Wire_3_5.UnionMachine.UnionSchedule

/-! # The union's call-count forcing lemma (P3:3622, 3797-3798; FREEZE row 19)

Realizes, at the pinned setup `S₂` and the pinned oracle degree `G = 17·c_STV`, the count behind "There are polynomially
many calls when `Λ̄ = q^{O(1)}`" (P3:3622) and "the time for all polynomially many verification calls has the form
[...]" (P3:3797-3798): every guess the union machine can process (oracle of size at most `q^G`, the machine's first
check, P3:3669) schedules at most `q(N)^{gateCallDeg l G}` primitive calls, eventually in `N`, where `q(N)` is the
ledger's native width, the `q` of `tr:time`'s split `q(N)^{callDeg}·callBudget(q(N))`.

The count is the `length_schedule_le`, `#calls ≤ 24K(1 + 2K(s+1))⁴` with `K = c_a (size(H)+1)^{d_a}` the PCPP's
clause/variable bound on the substituted circuit `H`. Two facts force the exponent `gateCallDeg = 5σ_H d_a + 1`,
`σ_H = max(e_Q + 2^{oracleDepth G}, 3e_Q)`:
* the substituted circuit of an oracle within `q^G` has `size(H) + 1 ≤ K_s (q+1)^{σ_H}` (base's
  `compactSubstituted_size`, `request_size`, the PCP's query bound; `requestSize_le_of`), so `K ≤ K₀ (q+1)^{σ_H d_a}`;
* the grid size `s(q)` obeys `s⁸ ≤ C_sp L³` (`RowBParams.sp_le`), so `C (s+1)⁴ ≤ q` eventually for every constant `C`
  (`eventually_calls`); the `+1` of `gateCallDeg` absorbs it with all constants.

Paper quantity of the main type: **the number of scheduled primitive calls**, `(g.checkData tr).schedule.length`,
against **`q(N)^{unionCallDeg l}`** (the exponent of `GateFreeOK`). Main declarations: `unionCalls_le` (at
`unionSetupS2 l G` for every gate with `p₀ + 6 ≤ A_pad`) and **`setupF_calls_le`** (at `setupF l F`, every `F`), the
form C6's `tr:time` consumes with `Split.calls_absorb`: the calls are at most `q^{unionCallDeg}`, each within a
constant times `callBudget` plus `(q+1)^{c−1}` glue. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.UnionCallCount
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound oracleDepth)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open Filter

/-! ## Pure arithmetic -/

/-- The call count `24K(1+2K(s+1))⁴` against a polynomial bound `K ≤ K₀X` on the PCPP bound. -/
theorem count_arith (K K₀ X s : ℕ) (hK : K ≤ K₀ * X) (hX : 1 ≤ X) :
    24 * K * (1 + 2 * K * (s + 1)) ^ 4 ≤ 24 * K₀ * (1 + 2 * K₀) ^ 4 * X ^ 5 * (s + 1) ^ 4 := by
  have hXs : 1 ≤ X * (s + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h2 : 2 * K * (s + 1) ≤ 2 * K₀ * (X * (s + 1)) := by
    calc 2 * K * (s + 1) ≤ 2 * (K₀ * X) * (s + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hK)
      _ = 2 * K₀ * (X * (s + 1)) := by ring
  have h1 : 1 + 2 * K * (s + 1) ≤ (1 + 2 * K₀) * X * (s + 1) := by
    calc 1 + 2 * K * (s + 1) ≤ X * (s + 1) + 2 * K₀ * (X * (s + 1)) := Nat.add_le_add hXs h2
      _ = (1 + 2 * K₀) * X * (s + 1) := by ring
  calc 24 * K * (1 + 2 * K * (s + 1)) ^ 4 ≤ 24 * (K₀ * X) * ((1 + 2 * K₀) * X * (s + 1)) ^ 4 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hK) (Nat.pow_le_pow_left h1 4)
    _ = 24 * K₀ * (1 + 2 * K₀) ^ 4 * X ^ 5 * (s + 1) ^ 4 := by ring

/-- `(x+1)⁸ ≤ 256(C+1)L³` from `x⁸ ≤ C L³` and `L ≥ 1`. -/
theorem succ_pow8_le (x C L : ℕ) (hx : x ^ 8 ≤ C * L ^ 3) (hL : 1 ≤ L) :
    (x + 1) ^ 8 ≤ 256 * (C + 1) * L ^ 3 := by
  have hL3 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ hL
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · subst h0
    calc (0 + 1) ^ 8 = 1 := by norm_num
      _ ≤ 256 * (C + 1) * L ^ 3 := by nlinarith
  · calc (x + 1) ^ 8 ≤ (2 * x) ^ 8 := Nat.pow_le_pow_left (by omega) 8
      _ = 256 * x ^ 8 := by ring
      _ ≤ 256 * (C * L ^ 3) := Nat.mul_le_mul_left _ hx
      _ ≤ 256 * (C + 1) * L ^ 3 := by nlinarith

/-- **The grid factor is absorbed by one power of `q`**: for every constant `C` and exponent `m`, eventually
`C (q+1)^m (s(q)+1)⁴ ≤ q^{m+1}`, whenever `s(q)⁸ ≤ C_sp L(q)³`. -/
theorem eventually_calls (C m Csp : ℕ) (sp : ℕ → ℕ) (hsp : ∀ q, sp q ^ 8 ≤ Csp * Lq q ^ 3) :
    ∀ᶠ q : ℕ in atTop, C * (q + 1) ^ m * (sp q + 1) ^ 4 ≤ q ^ (m + 1) := by
  filter_upwards [eventually_mul_Lq_pow_le (C ^ 2 * 4 ^ m * (256 * (Csp + 1))) 3, eventually_ge_atTop 1] with q hq hq1
  have h8 := succ_pow8_le (sp q) Csp (Lq q) (hsp q) (Lq_pos q)
  have hsq : (C * 2 ^ m * (sp q + 1) ^ 4) ^ 2 ≤ q ^ 2 := by
    calc (C * 2 ^ m * (sp q + 1) ^ 4) ^ 2 = C ^ 2 * 4 ^ m * (sp q + 1) ^ 8 := by
          rw [show (4 : ℕ) ^ m = (2 ^ m) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]; ring
      _ ≤ C ^ 2 * 4 ^ m * (256 * (Csp + 1) * Lq q ^ 3) := Nat.mul_le_mul_left _ h8
      _ = C ^ 2 * 4 ^ m * (256 * (Csp + 1)) * Lq q ^ 3 := by ring
      _ ≤ q := hq
      _ ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have ha : C * 2 ^ m * (sp q + 1) ^ 4 ≤ q := (Nat.pow_le_pow_iff_left (by norm_num)).1 hsq
  have hq2 : (q + 1) ^ m ≤ 2 ^ m * q ^ m := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) m
  calc C * (q + 1) ^ m * (sp q + 1) ^ 4 ≤ C * (2 ^ m * q ^ m) * (sp q + 1) ^ 4 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq2)
    _ = (C * 2 ^ m * (sp q + 1) ^ 4) * q ^ m := by ring
    _ ≤ q * q ^ m := Nat.mul_le_mul_right _ ha
    _ = q ^ (m + 1) := by rw [pow_succ, mul_comm]

/-! ## The substituted request's size at `σ_H` -/

section Generic

end Generic

/-! ## At the pinned setup `S₂` -/

section Pinned

end Pinned

end NearCubicWires.WireExponent3_5.Transfer.UnionCallCount
