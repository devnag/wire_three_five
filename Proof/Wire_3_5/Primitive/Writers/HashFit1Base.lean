import Proof.Wire_3_5.Primitive.Writers.HashCellK
import Proof.Wire_3_5.FinalPass.HashSBase
import Proof.Wire_3_5.FinalPass.HashPops
import Proof.Wire_3_5.FinalPass.ThrSz3
import Proof.Wire_3_5.Primitive.Writers.ThrCap2Base
import Proof.Wire_3_5.Primitive.Writers.HashLeafBase

/-! # HASH setup (C), fit part 1: the THR call's sizes in the unit `2^{(B+1)²}`

P3:3114-3115 ("All powers of `n` are fixed before a fixed `r`") and P3:3170-3181 (the seed phase's capacity
`2^{⌊n/8⌋ + C}`): every size the HASH cell's capacity facts (`CellFit`) read at a THR call is at most `2^{E·(B+1)²}`
(`B` the bit length of `n`), with `E` fixed by the literals and the gate: the request word and the capacity numbers
(`ThrCap.thr_sizes`), the call's sixteen numbers (the THR numbers' polynomial bound), the carriers' sizes, the pool and
the occurrences, the cutoff, the aux seeds `nE = 2^{seedBits}`, the populations' stream (`HashFr` sizes in the
unit `⌈log₂(n+2)⌉ + 1`, whose square is at most `4(B+1)²`), and each circuit's payload (`ThrSz.payOf_le`).

* `clog_le_b`, `clogsq_le`, `pwX`, `pwXsq`; **`CallSz`**, **`call_sizes`**.

Paper quantities of the main type: the THR call's sizes (P3:3114-3115). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashFit
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimT

theorem clog_le_b (n : ℕ) : Nat.clog 2 (n + 2) ≤ natBitLength n + 1 := Nat.clog_le_of_le_pow (C4Cap.n2_le n)

theorem clogsq_le (n : ℕ) : (Nat.clog 2 (n + 2) + 1) * (Nat.clog 2 (n + 2) + 1) ≤ 4 * C4Cap.bsq n := by
  have h := clog_le_b n
  have h2 : Nat.clog 2 (n + 2) + 1 ≤ 2 * (natBitLength n + 1) := by omega
  have e : C4Cap.bsq n = (natBitLength n + 1) * (natBitLength n + 1) := by unfold C4Cap.bsq; ring
  calc (Nat.clog 2 (n + 2) + 1) * (Nat.clog 2 (n + 2) + 1) ≤ (2 * (natBitLength n + 1)) * (2 * (natBitLength n + 1)) :=
        Nat.mul_le_mul h2 h2
    _ = 4 * C4Cap.bsq n := by rw [e]; ring

theorem pwX {X c n : ℕ} (h : X ≤ 2 ^ (c * Nat.clog 2 (n + 2))) : X ≤ 2 ^ (c * C4Cap.bsq n) :=
  le_trans h (Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_left _ (le_trans (clog_le_b n) (C4Cap.b1_le_bsq n))))

theorem pwX1 {X c n : ℕ} (h : X ≤ 2 ^ (c * (Nat.clog 2 (n + 2) + 1))) : X ≤ 2 ^ ((2 * c) * C4Cap.bsq n) := by
  refine le_trans h (Nat.pow_le_pow_right (by norm_num) ?_)
  have h1 := clog_le_b n
  have h2 := C4Cap.b1_le_bsq n
  have : Nat.clog 2 (n + 2) + 1 ≤ 2 * C4Cap.bsq n := by omega
  calc c * (Nat.clog 2 (n + 2) + 1) ≤ c * (2 * C4Cap.bsq n) := Nat.mul_le_mul_left _ this
    _ = 2 * c * C4Cap.bsq n := by ring

theorem pwXsq {X c n : ℕ} (h : X ≤ 2 ^ (c * ((Nat.clog 2 (n + 2) + 1) * (Nat.clog 2 (n + 2) + 1)))) :
    X ≤ 2 ^ ((4 * c) * C4Cap.bsq n) := by
  refine le_trans h (Nat.pow_le_pow_right (by norm_num) ?_)
  calc c * ((Nat.clog 2 (n + 2) + 1) * (Nat.clog 2 (n + 2) + 1)) ≤ c * (4 * C4Cap.bsq n) :=
        Nat.mul_le_mul_left _ (clogsq_le n)
    _ = 4 * c * C4Cap.bsq n := by ring

theorem pwP (d n : ℕ) : (n + 1) ^ d ≤ 2 ^ (d * C4Cap.bsq n) :=
  le_trans (Nat.pow_le_pow_left (Nat.le_succ _) d) (C4Cap.pow_pw d n)

section Call

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.HashFit
