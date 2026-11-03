import Proof.Wire_3_5.Primitive.SeedFix.W6ZI
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5

/-! # W6 item 11: **`thrNumsPoly`**, the THR call's hash numbers are polynomial in `n`

P3:2552-2557 (`K = 8(|𝒢|+1)n^D`), P3:2552-2553 and P3:2573-2580 (the prime cutoff, the primes, `Σp`), P3:2121-2157 and
P3:2220-2231 (`M, A, B_*, J, t, e, ℓ₀`, the modulus), P3:3114-3115 ("All powers of `n` are fixed before a fixed `r`"):
at every THR call of `callInputs l F …` (`a' ≤ 4`, at most two carriers, `descriptionBits ≤ (n+1)^{26}`, the THR
filter cap `cap_T ≤ C_c(n+1)^{D_c}`), every entry of `ThrData.hashNums` is at most `K_t(n+1)^{D_t}`, with
`D_t = 147·(D_c+1)·Eth` (`Eth = 26·deg + 26` of the gate's decomposition algorithm, fixed by `l`) and
`K_t = (Cth·(C_c+1)^{Eth})^{147} + C_c + 2`:
* `base_le`: the call's base `N = thrN` is `≤ Cth·(C_c+1)^{Eth}·(n+1)^{(D_c+1)·Eth}` (W6's `thrN_le`);
* **`thrNumsPoly : ∀ l, BudgetIface.ThrNumsPoly l`** (the call's `D = 1`, so every THR number is `≤ N^{147}`, W6's
  `vb_get`).

Paper quantities of the main type: the THR numbers `hashNums` (`|carriers|`, `cap_T`, `|𝒢|`, `K`, the cutoff, `|primes|`,
`Σp`, `τ₀`, `M`, `A`, `B_*`, `J`, `t`, `e`, `ℓ₀`, the modulus), each polynomial in `n`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan

theorem base_le (alg : RepairRepresentation.DecompositionAlgorithm) (P : StarParams) (capT Cc Dc : ℕ)
    (hcap : capT ≤ Cc * (P.n + 1) ^ Dc) :
    thrN alg P capT ≤ Cth alg * (Cc + 1) ^ Eth alg * (P.n + 1) ^ ((Dc + 1) * Eth alg) := by
  have h1 := thrN_le alg P capT
  have hx : 1 ≤ P.n + 1 := by omega
  have a1 : P.n + 1 ≤ (P.n + 1) ^ (Dc + 1) := Nat.le_self_pow (by omega) _
  have a2 : (P.n + 1) ^ Dc ≤ (P.n + 1) ^ (Dc + 1) := Nat.pow_le_pow_right hx (by omega)
  have a3 := Nat.mul_le_mul_left Cc a2
  have hs : P.n + capT + 1 ≤ (Cc + 1) * (P.n + 1) ^ (Dc + 1) := by
    have e : (Cc + 1) * (P.n + 1) ^ (Dc + 1) = Cc * (P.n + 1) ^ (Dc + 1) + (P.n + 1) ^ (Dc + 1) := by ring
    omega
  have h2 : (P.n + capT + 1) ^ Eth alg ≤ (Cc + 1) ^ Eth alg * (P.n + 1) ^ ((Dc + 1) * Eth alg) := by
    calc (P.n + capT + 1) ^ Eth alg ≤ ((Cc + 1) * (P.n + 1) ^ (Dc + 1)) ^ Eth alg := Nat.pow_le_pow_left hs _
      _ = (Cc + 1) ^ Eth alg * (P.n + 1) ^ ((Dc + 1) * Eth alg) := by rw [mul_pow, ← pow_mul]
  calc thrN alg P capT ≤ Cth alg * (P.n + capT + 1) ^ Eth alg := h1
    _ ≤ Cth alg * ((Cc + 1) ^ Eth alg * (P.n + 1) ^ ((Dc + 1) * Eth alg)) := Nat.mul_le_mul_left _ h2
    _ = Cth alg * (Cc + 1) ^ Eth alg * (P.n + 1) ^ ((Dc + 1) * Eth alg) := by ring

end NearCubicWires.WireExponent3_5.PrimT.W6
