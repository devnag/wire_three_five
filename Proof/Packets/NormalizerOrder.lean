import Proof.Packets.PhysicalCoefficientAlgebra
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Induction

/-! Exact ordered parity normal form: retain the last occurrence of every
odd-multiplicity monomial, then reverse that list. This is the literal order
of the fixed compiler's erase-or-cons fold, not merely a permutation. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizerOrder
open PhysicalCoefficientAlgebra
variable {α : Type} [DecidableEq α]

def ordered (P : List α) : List α :=
  P.dedup.reverse.filter (fun a => coefficient a P)

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizerOrder
