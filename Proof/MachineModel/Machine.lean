import Proof.MachineModel.Encoding

/-! The shared incidence producer: one ordinary five-tape machine that reads an
ordered monomial stream (child indices as shifted unary blocks) and the source's
unary child-count template, and appends the row-major incidence table plus one
unary row count. Every scan, seek, return, copy and scratch reset is a paid
transition; the scratch row is returned to all-zero after every row.

Tapes: 0 stream, 1 `UnaryTemplate.tape B` (head rests at 1), 2 scratch row,
3 output table (head at its end), 4 unary row count (head at its end).
States: 0 start, 1 row, 2 seek, 3 return, 4 copy, 5 zero, 6 halt. -/
namespace NearCubicWires.ExtIncidence
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 5 7 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 6
  rule := fun q bits =>
    if q.val = 0 then some (if bits 0 then ⟨1, fun _ => none, ![.right, .stay, .stay, .stay, .stay]⟩
      else ⟨6, fun _ => none, ![.right, .stay, .stay, .stay, .stay]⟩)
    else if q.val = 1 then some (if bits 0 then ⟨2, fun _ => none, ![.right, .stay, .stay, .stay, .stay]⟩
      else ⟨4, fun _ => none, ![.right, .stay, .stay, .stay, .stay]⟩)
    else if q.val = 2 then some (if bits 0 then ⟨2, fun _ => none, ![.right, .right, .right, .stay, .stay]⟩
      else ⟨3, ![none, none, some true, none, none], ![.right, .stay, .stay, .stay, .stay]⟩)
    else if q.val = 3 then some (if bits 1 then ⟨3, fun _ => none, ![.stay, .left, .left, .stay, .stay]⟩
      else ⟨1, fun _ => none, ![.stay, .right, .stay, .stay, .stay]⟩)
    else if q.val = 4 then some (if bits 1 then
        ⟨4, ![none, none, none, some (bits 2), none], ![.stay, .right, .right, .right, .stay]⟩
      else ⟨5, fun _ => none, ![.stay, .left, .left, .stay, .stay]⟩)
    else if q.val = 5 then some (if bits 1 then
        ⟨5, ![none, none, some false, none, none], ![.stay, .left, .left, .stay, .stay]⟩
      else ⟨0, ![none, none, none, none, some true], ![.stay, .right, .stay, .stay, .right]⟩)
    else none

/-- Every configuration the producer visits. The output head is always at the
end of the output and the count head at the end of the unary count. -/
def cfg (q : Fin 7) (input : List Bool) (ih B th : ℕ) (scratch : List Bool) (sh : ℕ)
    (out : List Bool) (count : ℕ) : Configuration 5 7 :=
  ⟨q, ![ih, th, sh, out.length, count],
    ![input, UnaryTemplate.tape B, scratch, out, List.replicate count true]⟩

@[simp] theorem halted_six : machine.halted 6 = true := rfl

/-! ## One transition per rule branch. Input reads are stated by the scanned bit. -/

end NearCubicWires.ExtIncidence
