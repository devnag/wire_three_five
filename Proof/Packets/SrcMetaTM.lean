import Proof.PCP.ProjectionNormalizationField
import Proof.Packets.PacketsSetupWords

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.MetaTM
open NearCubicWires LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution ExtDecompositionBatch

/-! ## 1. The frame-body copier -/

/-- The data bit written for a source bit. -/
def dat (ones b : Bool) : Bool := if ones then true else b

/-- The appended body. -/
def body (ones : Bool) (bits : List Bool) : List Bool := bits.flatMap (fun b => [true, dat ones b])

/-- State 0 reads a marker (`true`: write `true`, go to 1; `false`: stop without writing); state 1 copies the data bit. -/
def bodyM (ones : Bool) : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q bits =>
    if q.val = 0 then
      (if bits 0 then some ⟨1, ![none, some true], fun _ => .right⟩ else some ⟨2, fun _ => none, fun _ => .stay⟩)
    else if q.val = 1 then some ⟨0, ![none, some (dat ones (bits 0))], fun _ => .right⟩ else none

theorem body_false (bits : List Bool) : body false bits ++ [false] = RepairOrdinary.frame bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [body, dat, List.flatMap_cons, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] at ih ⊢
    rw [RepairOrdinary.frame]
    simp only [List.cons.injEq, true_and]
    exact ih

theorem body_append (ones : Bool) (u v : List Bool) : body ones (u ++ v) = body ones u ++ body ones v := by
  simp [body, List.flatMap_append]

theorem body_length (ones : Bool) (bits : List Bool) : (body ones bits).length = 2*bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [body, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

/-! ## 2. `1^b ↦ frame (0^b)` -/

/-- Tape 0 `1^b`, tape 1 the output `frame (0^b)`. -/
def zerosM : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q x =>
    if q.val = 0 then some (if x 0 then ⟨1, ![none, some true], ![.stay, .right]⟩
      else ⟨2, ![none, some false], ![.stay, .stay]⟩)
    else if q.val = 1 then some ⟨0, ![none, some false], ![.right, .right]⟩
    else none

end NearCubicWires.SourceStart.MetaTM

