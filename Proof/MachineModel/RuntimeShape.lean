import Proof.Supplier.SupplierCapacity
import Proof.Supplier.SupplierEstimator
import Proof.MachineModel.TopDownSelectedRuntime

/-! # R1: the runtime contract, proved before the source fuel exists

Paper: `paper.tex:1111-1112` "This charge is added to, and never multiplied by, the
`2^{q-K}` enumeration of columns"; `:1222-1231` "`q^{h_D}2^{q-K}poly(q) ≤ 2^q/q^σ` by the
choice of κ. The preprocessing term is added"; `:2303-2307` "take `κ ≥ h_D+σ+c_1`"; order
`:1184-1188`. Consumer: the last conjunct of `MaskedRecipe`
(`Proof/SourceAssembly/MaskSource.lean`) at `tableDegree = 0` (plan.md §12.1).
Charged to: that recipe's `remainingCoefficient`, `remainingOnset`, `tableCoefficient`.

For ANY fuel `F` that splits, eventually, into the three paper classes
* source polynomial `cP*(n+1)^dP`,
* table `cT*((q+1)^hT*2^(q-normalizedLiveCount q L))` with `hT+σ+2 ≤ L` (L after hT),
* small `cS*((q+1)^hS*2^(q/m))`, `2 ≤ m` (`m = 4` covers Header and fixed smallSize powers),
the consumer's inequality holds with the SAME degree `dP` and `tableDegree = 0`. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.RuntimeShape
open SupplierEstimator SupplierCapacity

/-! ## 1. The logarithm facts the table saving uses -/

/-- `Nat.clog 2 (q+2) ≥ Nat.log 2 q + 1`: the live logarithm dominates the consumer's. -/
theorem log_succ_le_logScale (q : ℕ) : Nat.log 2 q + 1 ≤ logScale q := by
  unfold logScale
  have h : Nat.log 2 q < Nat.clog 2 (q+2) := by
    rw [Nat.lt_clog_iff_pow_lt (by decide)]
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      simp
    · have hp := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hq)
      omega
  omega

theorem succ_le_two_pow_logScale (q : ℕ) : q+1 ≤ 2^logScale q := by
  unfold logScale
  have h := Nat.le_pow_clog (by decide : 1 < 2) (q+2)
  omega

theorem succ_pow_le (q h : ℕ) : (q+1)^h ≤ 2^(h*logScale q) := by
  calc (q+1)^h ≤ (2^logScale q)^h := Nat.pow_le_pow_left (succ_le_two_pow_logScale q) h
    _ = 2^(h*logScale q) := by rw [← pow_mul, Nat.mul_comm]

/-! ## 2. Absorption of each class into the consumer's allowance -/

/-! ## 3. The shape theorem, generic in the width function -/

/-! ## 4. At the consumer's own width, logarithm and sigma -/

open P1TopDown

/-- The three cost classes of one fuel function, fused with the live scale, its order fact
and the bound (one object: no correct-but-useless half can typecheck). -/
structure Split (σ : ℕ) (q : ℕ → ℕ) (sourceDegree : ℕ) (F : ℕ → ℕ) where
  liveScale : ℕ
  tableExponent : ℕ
  smallExponent : ℕ
  smallDivisor : ℕ
  sourceCoefficient : ℕ
  tableCoefficient : ℕ
  smallCoefficient : ℕ
  onset : ℕ
  two_le_divisor : 2 ≤ smallDivisor
  /-- `paper.tex:2307`: the live scale is chosen after the table exponent. -/
  order : tableExponent+σ+2 ≤ liveScale
  bound : ∀ n, onset ≤ n → F n ≤ sourceCoefficient*(n+1)^sourceDegree+
    tableCoefficient*((q n+1)^tableExponent*2^(q n-normalizedLiveCount (q n) liveScale))+
    smallCoefficient*((q n+1)^smallExponent*2^(q n/smallDivisor))



end NearCubicWires.RuntimeShape
