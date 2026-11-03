import Target
import WorkerArith.TermK
import Worker.Meaning

/-!
# W4prep (c): the hot part of the worker's fuel

The near-cubic-gates paper: "The polynomially many pair calls and their deterministic multiword arithmetic overhead take
`2^q q^{O(1)−μ_q} = o(T_clk(N))`." The worker makes `10 M` counter calls (`M = 2^{cl}` gadgets, ten terms each); an
admitted call spends at most `⌊2^q / q^{μ(q)}⌋` (J3 `Counter.fast`). The hot part of the fuel is
`hotOf tc N = (300 tc + 6000) · 10 M · ⌊2^q / q^{μ(q)}⌋` (the per-budget factor of `termCost`), and
`hot_bound`: for every fixed `σ`, `hotOf tc N · q^σ ≤ B · 2^q` eventually (`hot_split`).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith.W4Prep

open NearCubicWires NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.Close NearCubicGates.Close.Transfer
open NearCubicGates.Close.Worker (width gadgets)

noncomputable section

end

end NearCubicGates.Close.WorkerArith.W4Prep
