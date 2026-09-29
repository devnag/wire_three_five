import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellIface

/-! # THR, W5 v2: the THR shell dimensioned for the RADIX rows' `2^{O(L²)}` expansion (`ThrShellX2`)

P3:2621-2623 (row:radix): "The `2^{O(L²)}` internal digit tuples in `(row:radix)` are expansion preprocessing, not
exposed sampler states." A THR entry's RADIX row prints C2's `radRefC D digs p 2 s`, one term per digit tuple
`(t_d^±)_{d < τ₀} ∈ [0, M]^{2τ₀}` in the congruence class: `(M+1)^{2τ₀}/p` terms, `τ₀ = ⌈log₂ cutoff⌉ = Θ(L)` and
`M = |occs| = n^{Θ(1)}`, so `2^{Θ(L²)}` (C2's `radRow_run` cost `≤ (M+1)^{2τ₀}·128·(|record|+1)²`). One loop unit prints
it, so the unit's cost and residues must fit the scrub capacity `R = C(n'+1)^D`. ShellX (and the v1
`Shell.ThrShellRun`) take `n' = 2^{mOf P}`, `mOf P = 2·kh + L`, `kh = Θ(L·log L)`: `L² ≫ D·(2kh + L)` for every fixed
`D`, so no v1 shell fits a RADIX unit. v1 stays and correct for FILTER-only units (the HASH writer).

* **`mOfT KL P = mOf P + KL·L²`**: the THR dimension exponent (`KL` fixed per gate);
* **`ThrShellX2 S x U D C D2 C2 Dv Cv cr DL CL KL`**: a writer stage (ShellX's boot with the THR data stage `S` and a
  dimension stage writing the CapReader source of `2^{mOfT KL P}`, the scrub entry, the unit loop over ANY unit machine
  `U`), its cost (`cost_le`: polynomial in `|w| + n + cc + 2` and `2^m + 1`, plus the loop), and its run: v1's
  statement with `2^{mOfT KL P}` in place of `2^{mOf P}` (loop bound `b = CL(n'+1)^DL`, scrub `R = C(n'+1)^D`) and the
  fill `W = Dv·…` large enough for `m`.

Paper quantity of the main type: the THR writer's output tape `(List.range b).flatMap emit ++ [false]` at the
dimension `2^{mOf P + KL·L²}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.Shell2
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellLoop
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimThrW.Shell

/-- **The THR dimension exponent** `mOf P + KL·L²`, `L = ⌈log₂(n+2)⌉`. -/
def mOfT (KL : ℕ) (P : Shared.StarParams) : ℕ := NumsX.mOf P + KL * Nat.clog 2 (P.n + 2) ^ 2

end NearCubicWires.WireExponent3_5.PrimThrW.Shell2
