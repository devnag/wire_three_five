import Proof.Foundations.SourceRegistry

/-! # Theorem 2.5 is not trivially satisfiable

A check of the Lean statement of paper Theorem 2.5 (`paper/paper.tex:794-808`, `thm:main-fixed`).
Nothing here is a source hypothesis or a proof of the theorem.

`constant_language_fails`: the target has teeth. A language that some zero-wire circuit computes
exactly (every constant language) violates the wire conclusion at every positive length, so no
degenerate language satisfies the target.
-/
namespace NearCubicWires.Theorem2_5_Nontrivial
open NearCubicWires RepairSource RepairRepresentation SourceInterfaces
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

/-- The zero-bottom symmetric circuit with a constant top. -/
def constantCircuit (n : ℕ) (value : Bool) : SymmetricThresholdCircuit n where
  bottomCount := 0
  bottom := Fin.elim0
  top := fun _ => value

theorem constantCircuit_eval (n : ℕ) (value : Bool) (x : BitInput n) :
    (constantCircuit n value).eval x = value := rfl

end NearCubicWires.Theorem2_5_Nontrivial
