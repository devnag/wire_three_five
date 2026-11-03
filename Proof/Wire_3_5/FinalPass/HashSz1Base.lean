import Proof.Wire_3_5.FinalPass.HashShape
import Proof.Wire_3_5.FinalPass.SymDegBase
import Proof.Wire_3_5.FinalPass.ThrSz1

/-! # The HASH call's sizes, part 1: the majorant's numbers, F-free

At a THR call of the gate (`L = ⌈log₂(n+2)⌉`, `a = algX l`, `Z = capZR l`), every number of the fixed hash's majorant
(P3:2221-2279, `list_params_bound`'s choice `J, t, e`, P3:2238-2251) is `2^{O(L)}` or `O(L)` with constants of the
literals only: the THR cap `≤ 2^{(48+Z)L}` (`2c_r + 2 ≤ n + 2`, so `capK(c_r) ≤ 2^{48L}`: no constant of `F`), `|𝒢|`,
the cutoff, `A`, `K = den`, `B_*`, `J ≤ c_J(L+1)`, `t ≤ c_t(L+1)`, `M ≤ 2^{28(L+1)}`. These fix the HASH free
numbers' constants before `F` (the recovery range `Q' = O(k + L³)`, P3:2291-2296).

* `capT_le`, `eq_le`, `cut_le'`, `primes_le`, **`A_le`**, **`den_le`**, **`Bs_le`**, **`J_le`**, **`t_le`**, **`M_le`**.

Paper quantities of the main types: the fixed hash's majorant parameters at a THR call. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.SymFr


theorem n1_le_L (n : ℕ) : n + 1 ≤ 2 ^ Nat.clog 2 (n + 2) := by have := n2_le_L n; omega

section Gate
variable (l : Literals) 

theorem primes_le (c : ℕ) : Fintype.card (SupplierPrime.PrimeIndex c) ≤ c + 1 := by
  rw [Fintype.card_coe]
  unfold SupplierPrime.primesUpTo
  exact (Finset.card_filter_le _ _).trans (by simp)

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
