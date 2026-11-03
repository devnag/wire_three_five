import Lean
import Proof.Wire_3_5.Primitive.SeedFix.W6ZI
import Proof.Wire_3_5.Primitive.Writers.BudgetIface
import W3.Proof.Foundations.SourceRegistry
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Transfer.LiteralSources
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPolyBase


noncomputable section
set_option maxRecDepth 4096


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

/-- The gate's decomposition algorithm (fixed by the literals; `gate0`'s `alg`, definitionally). -/
noncomputable def litAlg (l : Literals) : RepairRepresentation.DecompositionAlgorithm :=
  Classical.choice l.eightSources.decomposition

/-- **W6 item 11: the THR call's hash numbers are polynomial in `n`** (BudgetIface's `ThrNumsPoly`). -/
theorem thrNumsPoly (l : Literals) : BudgetIface.ThrNumsPoly l := by
  intro Dc
  refine ⟨(Dc + 1) * Eth (litAlg l) * 147, fun Cc F => ⟨(Cth (litAlg l) * (Cc + 1) ^ Eth (litAlg l)) ^ 147 + Cc + 2, ?_⟩⟩
  intro kclk coef A a ha n hs a' Cs carriers capT ha' hcar hd hcap v hv
  have hD : (callInputs l F kclk coef A a ha).D = 1 := rfl
  have hx : 1 ≤ n + 1 := by omega
  have hDt : (n + 1) ^ Dc ≤ (n + 1) ^ ((Dc + 1) * Eth (litAlg l) * 147) := Nat.pow_le_pow_right hx (by
    have : 1 ≤ Eth (litAlg l) := by unfold Eth; omega
    nlinarith)
  have hX1 : 1 ≤ (n + 1) ^ ((Dc + 1) * Eth (litAlg l) * 147) := Nat.one_le_pow _ _ (by omega)
  have e : ((Cth (litAlg l) * (Cc + 1) ^ Eth (litAlg l)) ^ 147 + Cc + 2) * (n + 1) ^ ((Dc + 1) * Eth (litAlg l) * 147) =
      (Cth (litAlg l) * (Cc + 1) ^ Eth (litAlg l)) ^ 147 * (n + 1) ^ ((Dc + 1) * Eth (litAlg l) * 147) + Cc * (n + 1) ^ ((Dc + 1) * Eth (litAlg l) * 147) +
        2 * (n + 1) ^ ((Dc + 1) * Eth (litAlg l) * 147) := by ring
  have hcD := Nat.mul_le_mul_left Cc hDt
  have hB := base_le (litAlg l) ((callInputs l F kclk coef A a ha).starParams n hs) capT Cc Dc hcap
  have hBp : thrN (litAlg l) ((callInputs l F kclk coef A a ha).starParams n hs) capT ^ 147 ≤
      (Cth (litAlg l) * (Cc + 1) ^ Eth (litAlg l)) ^ 147 * (n + 1) ^ ((Dc + 1) * Eth (litAlg l) * 147) := by
    calc thrN (litAlg l) ((callInputs l F kclk coef A a ha).starParams n hs) capT ^ 147
        ≤ (Cth (litAlg l) * (Cc + 1) ^ Eth (litAlg l) * (n + 1) ^ ((Dc + 1) * Eth (litAlg l))) ^ 147 := Nat.pow_le_pow_left hB 147
      _ = (Cth (litAlg l) * (Cc + 1) ^ Eth (litAlg l)) ^ 147 * (n + 1) ^ ((Dc + 1) * Eth (litAlg l) * 147) := by rw [mul_pow, ← pow_mul]
  simp only [ThrData.hashNums, List.mem_cons] at hv
  rcases hv with hv | hv | hv
  · have h2 : v ≤ 2 := hv.trans_le hcar
    omega
  · subst hv; omega
  · unfold ThrData.thrNumList at hv
    rw [List.mem_ofFn] at hv
    obtain ⟨k, hk⟩ := hv
    have hg := vb_get (litAlg l) (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers.length capT ha' hd hcar k
    have hg2 : (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs (litAlg l) (callInputs l F kclk coef A a ha).D carriers.length capT).get k ≤
        thrN (litAlg l) ((callInputs l F kclk coef A a ha).starParams n hs) capT ^ 147 :=
      pw_mono (by have := thrN16 (litAlg l) ((callInputs l F kclk coef A a ha).starParams n hs) capT; omega) hg (by omega)
    have hg3 : v ≤ thrN (litAlg l) ((callInputs l F kclk coef A a ha).starParams n hs) capT ^ 147 := hk.symm.trans_le hg2
    omega

end NearCubicWires.WireExponent3_5.PrimT.W6

end
