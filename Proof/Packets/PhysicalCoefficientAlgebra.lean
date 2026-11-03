import Std.Tactic

/-! Coefficient cancellation laws used by the ordinary parity scan.
This module imports no paper assumptions and introduces no execution model. -/
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PhysicalCoefficientAlgebra

variable {α : Type} [DecidableEq α]

def coefficient (needle : α) (rows : List α) (initial : Bool := false) : Bool :=
  rows.foldl (fun acc row => xor acc (decide (needle = row))) initial

@[simp] theorem coefficient_nil (needle : α) (initial : Bool) :
    coefficient needle [] initial = initial := rfl

@[simp] theorem coefficient_cons (needle row : α) (rows : List α) (initial : Bool) :
    coefficient needle (row::rows) initial =
      coefficient needle rows (xor initial (decide (needle = row))) := rfl


end PhysicalCoefficientAlgebra
