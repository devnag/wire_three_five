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

/-- Proof syntax for the controller's behavior on every natural.  Raw tags
are retained so the final equality guard can detect every normalization. -/
inductive RawBalancedTraversalTree where
  | empty
  | leaf (tag atom : ℕ)
  | branch (tag : ℕ)
      (left right : RawBalancedTraversalTree)
  deriving DecidableEq, Repr

namespace RawBalancedTraversalTree

def rawCode : RawBalancedTraversalTree → ℕ
  | .empty => 0
  | .leaf tag atom => Nat.pair tag atom
  | .branch tag left right =>
      Nat.pair tag (Nat.pair left.rawCode right.rawCode)

def normalized : RawBalancedTraversalTree → BalancedTraversalTree
  | .empty => .empty
  | .leaf _tag atom => .leaf atom
  | .branch _tag left right =>
      .branch left.normalized right.normalized

def atoms (tree : RawBalancedTraversalTree) : List ℕ :=
  tree.normalized.atoms

/-- Exactly the raw shapes selected by the fixed controller. -/
def Valid : RawBalancedTraversalTree → Prop
  | .empty => True
  | .leaf tag atom =>
      Nat.pair tag atom ≠ 0 ∧ (Nat.unpair tag).1 = 0
  | .branch tag left right =>
      (Nat.unpair tag).1 ≠ 0 ∧ left.Valid ∧ right.Valid

end RawBalancedTraversalTree

/-- Total parser for the controller's actual raw-tag classification.  This is
a proof view only; executable code remains the fixed register controller. -/
def rawBalancedTraversalTree (code : ℕ) : RawBalancedTraversalTree :=
  if _hzero : code = 0 then
    .empty
  else
    let outer := Nat.unpair code
    if _hleaf : (Nat.unpair outer.1).1 = 0 then
      .leaf outer.1 outer.2
    else
      let branches := Nat.unpair outer.2
      .branch outer.1
        (rawBalancedTraversalTree branches.1)
        (rawBalancedTraversalTree branches.2)
termination_by code
decreasing_by
  all_goals
    have htagPositive : 0 < outer.1 := by
      by_contra hnotPositive
      have htagZero : outer.1 = 0 := Nat.eq_zero_of_not_pos hnotPositive
      exact _hleaf (by simp [htagZero])
    have hpayloadLt : outer.2 < code := by
      have hsum : outer.1 + outer.2 ≤ code := by
        simpa only [outer] using Nat.unpair_add_le code
      omega
  · exact (Nat.unpair_left_le outer.2).trans_lt hpayloadLt
  · exact (Nat.unpair_right_le outer.2).trans_lt hpayloadLt

namespace RawBalancedTraversalTree

/-- Canonical structural trees embed with exact public tags. -/
def ofBalanced : BalancedTraversalTree → RawBalancedTraversalTree
  | .empty => .empty
  | .leaf atom => .leaf 1 atom
  | .branch left right =>
      .branch 2 (ofBalanced left) (ofBalanced right)

@[simp] theorem rawCode_ofBalanced (tree : BalancedTraversalTree) :
    (ofBalanced tree).rawCode = tree.code := by
  induction tree with
  | empty => rfl
  | leaf atom => rfl
  | branch left right inductionLeft inductionRight =>
      simp [ofBalanced, rawCode, BalancedTraversalTree.code,
        inductionLeft, inductionRight]

@[simp] theorem normalized_ofBalanced (tree : BalancedTraversalTree) :
    (ofBalanced tree).normalized = tree := by
  induction tree with
  | empty => rfl
  | leaf atom => rfl
  | branch left right inductionLeft inductionRight =>
      simp [ofBalanced, normalized, inductionLeft, inductionRight]

theorem valid_ofBalanced (tree : BalancedTraversalTree) :
    (ofBalanced tree).Valid := by
  induction tree with
  | empty =>
      trivial
  | leaf atom =>
      refine ⟨?_, by norm_num [Nat.unpair]⟩
      have := Nat.left_le_pair 1 atom
      omega
  | branch left right inductionLeft inductionRight =>
      exact ⟨by norm_num [Nat.unpair],
        inductionLeft, inductionRight⟩

end RawBalancedTraversalTree

theorem rawBalancedTraversalTree_of_valid
    (tree : RawBalancedTraversalTree) (hvalid : tree.Valid) :
    rawBalancedTraversalTree tree.rawCode = tree := by
  induction tree with
  | empty =>
      simp [rawBalancedTraversalTree,
        RawBalancedTraversalTree.rawCode]
  | leaf tag atom =>
      rcases hvalid with ⟨hnonzero, htagClass⟩
      simp [rawBalancedTraversalTree,
        RawBalancedTraversalTree.rawCode, hnonzero, htagClass]
  | branch tag left right inductionLeft inductionRight =>
      rcases hvalid with
        ⟨htagClass, hleftValid, hrightValid⟩
      have hnonzero :
          Nat.pair tag (Nat.pair left.rawCode right.rawCode) ≠ 0 := by
        intro hzero
        have htagZero : tag = 0 := by
          have := Nat.left_le_pair tag
            (Nat.pair left.rawCode right.rawCode)
          omega
        exact htagClass (by simp [htagZero])
      simp [rawBalancedTraversalTree,
        RawBalancedTraversalTree.rawCode, hnonzero, htagClass,
        inductionLeft hleftValid, inductionRight hrightValid]

theorem rawBalancedTraversalTree_normalized_code
    (tree : BalancedTraversalTree) :
    (rawBalancedTraversalTree tree.code).normalized = tree := by
  rw [← RawBalancedTraversalTree.rawCode_ofBalanced tree,
    rawBalancedTraversalTree_of_valid
      (RawBalancedTraversalTree.ofBalanced tree)
      (RawBalancedTraversalTree.valid_ofBalanced tree)]
  exact RawBalancedTraversalTree.normalized_ofBalanced tree

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
