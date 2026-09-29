import Proof.Foundations.SupplierPrinter

set_option autoImplicit false

open Finset
open scoped BigOperators
open NearCubicWires.SupplierPrinter

namespace NearCubicWires.RepairSource.CloseoutFinal.C10PrinterMonomials

section Reduction

end Reduction

section Count

variable {Equation : Type} [DecidableEq Equation]

/-- `∑_{j≤d} B^j ≤ (B+1)^d`, by induction on `d`. -/
theorem sum_pow_le_succ_pow (B d : ℕ) :
    ∑ j ∈ Finset.range (d + 1), B ^ j ≤ (B + 1) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ]
      have hpow : B ^ (d + 1) ≤ (B + 1) ^ d * B := by
        rw [pow_succ]
        exact Nat.mul_le_mul_right B (Nat.pow_le_pow_left (Nat.le_succ B) d)
      calc (∑ j ∈ Finset.range (d + 1), B ^ j) + B ^ (d + 1)
          ≤ (B + 1) ^ d + (B + 1) ^ d * B := Nat.add_le_add ih hpow
        _ = (B + 1) ^ (d + 1) := by ring

/-- The paper's second inequality: `∑_{j=0}^d C(B,j) ≤ (B+1)^d` (paper.tex:2795–2800). -/
theorem sum_choose_le_succ_pow (B d : ℕ) :
    ∑ j ∈ Finset.range (d + 1), B.choose j ≤ (B + 1) ^ d :=
  calc ∑ j ∈ Finset.range (d + 1), B.choose j
      ≤ ∑ j ∈ Finset.range (d + 1), B ^ j :=
        Finset.sum_le_sum fun j _ => Nat.choose_le_pow B j
    _ ≤ (B + 1) ^ d := sum_pow_le_succ_pow B d

end Count

section Main

end Main


end NearCubicWires.RepairSource.CloseoutFinal.C10PrinterMonomials
