import Proof.Wire_3_5.Primitive.SeedFix.C4SymKA2
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB

/-! # C4.K SYM, the free numbers' contract, v2 (amendment, the findings)

"`alg:compiler`" (P3:1886-1906: the request's degree bound `d` over every monomial, the exact factor count `m` of every
term), "`ℓ ≥ max(k, ⌈log₂(Q+1)⌉)`" and `Q` (P3:2929-2941, 2994-3000). Changes from `SymEAt`/`SymFreeOk`
(kept):
* **`SymEAt2`**: the child requests carry `d := fr 3` (was `0`, below the batch's monomial degree); `m = fr 4` must be
  the terms' EXACT factor count (`Padded m V`; at a SYM call `8·(|carriers| + 2a·walkLen)`, since every entry has
  `|carriers|` FILTER rows of one factor and `2a` POP rows of `walkLen` factors), read from `x.nc`, `x.a`, `x.L`;
* **`FreeSmall Do x`**: every field of `x` at most `2^{Do(B+1)²}` (at every call); `ok_le` and `val_le` take it as a
  premise, for every `Ds` (a register above the capacity cannot be read; `m` reads `nc`, `a`);
* **`SymFreeOk2`**: `SymFreeOk` with these two changes (the program `Fp` per mode, since `m`'s count is the mode's).
Satisfiability: `d = h = κ·β²` above the batch's degree `O(β)` (`β = ⌈log₂(n+2)⌉`), `m = 8(nc + 2a·walkLen)`,
`pr ≥ h·Q'·d = O(β⁶)` within `c3_le` against `ψ ≥ C_D·L⁶` (the sizing).

Paper quantities of the main type: the free numbers `TWd, Cap, Q', h (= d), m, pr, ρ` of a SYM call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

/-- **Every field of the numbers is at most `2^{Do(B+1)²}`**, `B` the bit length of `n`. -/
def FreeSmall (Do : ℕ) (x : FreeIn) : Prop :=
  x.n ≤ 2 ^ (Do * (natBitLength x.n + 1) ^ 2) ∧ x.kh ≤ 2 ^ (Do * (natBitLength x.n + 1) ^ 2) ∧
  x.L ≤ 2 ^ (Do * (natBitLength x.n + 1) ^ 2) ∧ x.capS ≤ 2 ^ (Do * (natBitLength x.n + 1) ^ 2) ∧
  x.a ≤ 2 ^ (Do * (natBitLength x.n + 1) ^ 2) ∧ x.nc ≤ 2 ^ (Do * (natBitLength x.n + 1) ^ 2) ∧
  x.M ≤ 2 ^ (Do * (natBitLength x.n + 1) ^ 2) ∧ x.Q ≤ 2 ^ (Do * (natBitLength x.n + 1) ^ 2) ∧
  x.ell ≤ 2 ^ (Do * (natBitLength x.n + 1) ^ 2) ∧ x.nT ≤ 2 ^ (Do * (natBitLength x.n + 1) ^ 2) ∧
  x.w ≤ 2 ^ (Do * (natBitLength x.n + 1) ^ 2) ∧ x.dRow ≤ 2 ^ (Do * (natBitLength x.n + 1) ^ 2)

section Call

end Call

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
