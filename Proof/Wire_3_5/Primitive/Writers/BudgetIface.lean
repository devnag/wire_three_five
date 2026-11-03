import Lean
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.Plan
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.PlanBase


noncomputable section
set_option maxRecDepth 4096


/-! # PA2: the writers' two shared budget statements (types only)

Every batch writer's per-unit budget and data word must be bounded before its class link (HASH (d4), SYM, THR). Two
bounds are needed by all of them and exist nowhere (negative search). This file states them; the producers
prove them.

* **`FiltPipeLe`** (C6b proves it): the FILTER unit pipeline's cost `FiltPipe.filtPipeBound` at the setup's rulers
  `rulerW P` is at most `K_f·(len + cap + e + L + r4 + G + off + 2)^{D_f·(e+1)}`. The exponent is linear in the
  filter's error exponent `e` (`filtDeg (filterTable P e L) = 3·(128·walkLen) + 1`, `walkLen = 2⌊e/4⌋ + 1`: the
  FILTER row prints `(4L+1)^{filtDeg}` monomials, `filtCostC`); every other piece is polynomial in the parameters
  (`2^{fieldBits} ≤ 32·len`, the rulers `O(log (len·cap))`). Consumers: SYM's FILTER units
  (`I.filterParams .sym n`), THR's (`FiltDock5`), HASH's aux filter (`thrAux`, `e = thrCallE = Θ(L²)`).
* **`ThrNumsPoly l`** (T proves it, W6 item 11, on CallIndex's `thrEq_le`/`den_le`/`cut_le`): at every THR call of `callInputs l F …` (`a' ≤ 4`, at most two carriers, the
  call envelope's description bound `(n+1)^{26}`, the THR filter cap `capT ≤ C_c(n+1)^{D_c}`), every entry of
  `ThrData.hashNums` is at most `K_t(n+1)^{D_t}`, the exponent `D_t` depending on `l`, `D_c` only, the coefficient `K_t` on `C_c`, `F`. Consumers: ShellH's
  `hcu3` (the unary data word `hashNums ++ thrCounts` within the fill) and the HASH decode's `hcl` (each entry within
  the register capacity).

Paper quantities of the main types: the FILTER row's cost `(4L+1)^{filtDeg}` (the regular filter's walk, P3:2063-2101)
at the error exponent `e` (P3:2210-2211); the THR numbers of `ThrDataIface3` (gate 2: `K = 8(|𝒢|+1)n^D`, the prime
cutoff and `Σ p` (row:prime, P3:2573-2580), `M, A, B_*, J, t, e, ℓ₀` (filt:majorant, P3:2121-2157)) each polynomial
in `n`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.BudgetIface
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- **The THR numbers are polynomial at the caller's calls** (T, W6 item 11; #113 specialized at `callInputs`): for
every THR filter-cap exponent `D_c`, an exponent `D_t` (depending on `l`, `D_c` only: `|𝒢| ≤ (n+2)^{4·algX l}`,
`CallIndex.thrEq_le`), and for every coefficient `C_c` and gate `F` a coefficient `K_t`, bounding every entry of
`hashNums` at every THR call shape (StageU's order: the exponent before `F`). -/
def ThrNumsPoly (l : Literals) : Prop :=
  ∀ Dc : ℕ, ∃ Dt : ℕ, ∀ (Cc : ℕ) (F : GateFree l), ∃ Kt : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (capT : ℕ), a' ≤ 4 → carriers.length ≤ 2 →
    (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) → capT ≤ Cc * (n + 1) ^ Dc →
    ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D capT, v ≤ Kt * (n + 1) ^ Dt

end NearCubicWires.WireExponent3_5.PrimAsm.BudgetIface

end
