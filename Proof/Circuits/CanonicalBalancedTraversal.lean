import Proof.Foundations.CanonicalBinaryProgram

/-!
# Exact interpreter semantics for balanced public sequences

`CanonicalBalanced` is the sole public variable-length sequence ABI.  This
module gives its fixed depth-first controller a compositional interpreter
semantics.  The semantic tree below is a proof view of the canonical code, not
another accepted encoding: executable interfaces still receive only
`encodeBalancedList`.
-/

namespace NearCubicWires.CanonicalBinaryProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.PolynomialClock

/-- Proof-only syntax matching the three constructors of
`encodeBalancedList`. -/
inductive BalancedTraversalTree where
  | empty
  | leaf (atom : ℕ)
  | branch (left right : BalancedTraversalTree)
  deriving DecidableEq, Repr

namespace BalancedTraversalTree

def code : BalancedTraversalTree → ℕ
  | .empty => 0
  | .leaf atom => Nat.pair 1 atom
  | .branch left right =>
      Nat.pair 2 (Nat.pair left.code right.code)

def atoms : BalancedTraversalTree → List ℕ
  | .empty => []
  | .leaf atom => [atom]
  | .branch left right => left.atoms ++ right.atoms

def nodeCount : BalancedTraversalTree → ℕ
  | .empty => 1
  | .leaf _ => 1
  | .branch left right => 1 + left.nodeCount + right.nodeCount

end BalancedTraversalTree

/-! ## Total structural view of arbitrary raw codes -/

namespace RawBalancedTraversalTree

end RawBalancedTraversalTree

namespace RawBalancedTraversalTree

end RawBalancedTraversalTree

/-- Canonical midpoint tree used only to reason about the public code. -/
def balancedTraversalTree : List ℕ → BalancedTraversalTree
  | [] => .empty
  | [atom] => .leaf atom
  | first :: second :: rest =>
      let values := first :: second :: rest
      let leftLength := (values.length + 1) / 2
      .branch
        (balancedTraversalTree (values.take leftLength))
        (balancedTraversalTree (values.drop leftLength))
termination_by values => values.length
decreasing_by
  all_goals
    simp_wf
    have : ((rest.length + 2 + 1) / 2) ≤ rest.length + 1 := by omega
    simp
    omega

theorem balancedTraversalTree_code (values : List ℕ) :
    (balancedTraversalTree values).code = encodeBalancedList values := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values with
  | h length ih =>
      cases values with
      | nil =>
          simp [balancedTraversalTree, BalancedTraversalTree.code,
            encodeBalancedList]
      | cons first rest =>
          cases rest with
          | nil =>
              simp [balancedTraversalTree, BalancedTraversalTree.code,
                encodeBalancedList]
          | cons second rest =>
              let values := first :: second :: rest
              let leftLength := (values.length + 1) / 2
              let left := values.take leftLength
              let right := values.drop leftLength
              have hlengthValues : values.length = length := by
                simpa [values] using hlength
              have htwo : 2 ≤ values.length := by simp [values]
              have hleftPositive : 0 < leftLength := by
                dsimp [leftLength]
                omega
              have hleftLtValues : leftLength < values.length := by
                dsimp [leftLength]
                omega
              have hleftLengthEq : left.length = leftLength := by
                simp [left, hleftLtValues.le]
              have hrightLengthEq :
                  right.length = values.length - leftLength := by
                simp [right]
              have hleftLt : left.length < length := by
                rw [hleftLengthEq, ← hlengthValues]
                exact hleftLtValues
              have hrightLt : right.length < length := by
                rw [hrightLengthEq, ← hlengthValues]
                omega
              have ihLeft := ih left.length hleftLt left rfl
              have ihRight := ih right.length hrightLt right rfl
              simp only [balancedTraversalTree, encodeBalancedList,
                BalancedTraversalTree.code]
              change
                Nat.pair 2
                      (Nat.pair
                        (balancedTraversalTree left).code
                        (balancedTraversalTree right).code) =
                    Nat.pair 2
                      (Nat.pair
                        (encodeBalancedList left)
                        (encodeBalancedList right))
              exact congrArg (Nat.pair 2)
                (congrArg₂ Nat.pair ihLeft ihRight)

theorem balancedTraversalTree_atoms (values : List ℕ) :
    (balancedTraversalTree values).atoms = values := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values with
  | h length ih =>
      cases values with
      | nil =>
          simp [balancedTraversalTree, BalancedTraversalTree.atoms]
      | cons first rest =>
          cases rest with
          | nil =>
              simp [balancedTraversalTree, BalancedTraversalTree.atoms]
          | cons second rest =>
              let values := first :: second :: rest
              let leftLength := (values.length + 1) / 2
              let left := values.take leftLength
              let right := values.drop leftLength
              have hlengthValues : values.length = length := by
                simpa [values] using hlength
              have htwo : 2 ≤ values.length := by simp [values]
              have hleftPositive : 0 < leftLength := by
                dsimp [leftLength]
                omega
              have hleftLtValues : leftLength < values.length := by
                dsimp [leftLength]
                omega
              have hleftLengthEq : left.length = leftLength := by
                simp [left, hleftLtValues.le]
              have hrightLengthEq :
                  right.length = values.length - leftLength := by
                simp [right]
              have hleftLt : left.length < length := by
                rw [hleftLengthEq, ← hlengthValues]
                exact hleftLtValues
              have hrightLt : right.length < length := by
                rw [hrightLengthEq, ← hlengthValues]
                omega
              have ihLeft := ih left.length hleftLt left rfl
              have ihRight := ih right.length hrightLt right rfl
              simp only [balancedTraversalTree,
                BalancedTraversalTree.atoms]
              change
                (balancedTraversalTree left).atoms ++
                    (balancedTraversalTree right).atoms =
                  values
              rw [ihLeft, ihRight]
              simp [left, right]

/-! ## Reusable stateful fold traversal -/

/-! ## One-pass natural summation -/

end NearCubicWires.CanonicalBinaryProgram
