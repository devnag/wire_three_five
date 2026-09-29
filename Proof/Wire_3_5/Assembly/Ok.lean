import Proof.Wire_3_5.Assembly.Free
import Proof.Wire_3_5.UnionMachine.UnionAtomsOk

/-! # The split with the union's atom test

"The weak machine guesses one size-`q^G` general oracle, a class tag, and one sparse grid sum for each distinct PCPP
variable. It rejects malformed descriptions, oversized atoms, and coefficients outside the fixed grid" (P3:3669-3671).
The union leaf's completeness is then at the accepting guesses that pass the atom test (`CompleteForEventuallyOk`),
which is where the paper uses it: at the guess Case 2 constructs (P3:3711-3729, `exists_unionAccepts_ok`).

The same split as `Split.lean` / `SplitFree.lean` with that one field changed:
* **`UnionLeafAt2`** (`UnionLeafAt` with `complete : CompleteForEventuallyOk`), `UnionLeafAt.toOk`;
* **`UnionLeaf2`**, **`RecoveryLeaf2`**, `parts_of_leaves2`, `literals_parts_of_leaves2`;
* the free-constant forms **`UnionLeafF2`**, **`RecoveryLeafF2`**, `parts_of_leavesF2`,
  **`literals_parts_of_leavesF2 : (∀ l, PrimitiveLeafF l) → (∀ l, UnionLeafF2 l) → (∀ l, RecoveryLeafF2 l) →
  Literals → Parts`** (leaf P unchanged).

Paper quantity of the main types: `Parts` (the paper's union construction, primitive and recovery at one gate). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Split
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.CLW20Theorem113 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Ledger NearCubicWires.WireExponent3_5.Transfer NearCubicWires.ExecutableInterfaces

/-- **The union construction with the atom test's completeness** at a pinned setup: past an onset
chosen after the primitive and the language, every accepting guess of the setup whose atoms pass the atom test
(P3:3670) makes the built machine accept. `tr:soundness` and `tr:time` are the `UnionConstruction` fields. -/
structure UnionLeafAt2 {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
    (S : ∀ L : Language, InNTIME (fun n => n ^ (kclk + 2)) L → UnionSetup I) extends UnionConstruction I where
  complete : ∀ (P : FusedPrimitive I) (L : Language) (hL : InNTIME (fun n => n ^ (kclk + 2)) L),
    CompleteForEventuallyOk (S L hL) P (build P L)

/-- A union leaf without the atom test is one with it. -/
def UnionLeafAt.toOk {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}
    {S : ∀ L : Language, InNTIME (fun n => n ^ (kclk + 2)) L → UnionSetup I} (U : UnionLeafAt I S) :
    UnionLeafAt2 I S :=
  { U.toUnionConstruction with complete := fun P L hL => (U.complete P L hL).ok }

section Gate
variable (G : Gate) (S : G.Setup)

/-- **Leaf U with the atom test** (B8 + C6 + C7): the clock and the source work, and the union construction with the
atom test's completeness for every primitive coefficient. -/
def UnionLeaf2 :=
  Σ kclk : ℕ, Σ A : ℕ, Σ a : ℕ, Σ' ha : a ≤ kclk + 1,
    ∀ coef : ℕ, UnionLeafAt2 (G.inputs kclk coef A a ha) (S kclk coef A a ha)

/-- **Leaf R** (D1 + D2) for every union leaf with the atom test at the pinned setup and every primitive. -/
def RecoveryLeaf2 :=
  ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (U : UnionLeafAt2 (G.inputs kclk coef A a ha) (S kclk coef A a ha))
    (P : FusedPrimitive (G.inputs kclk coef A a ha)), Recovery U.toUnionConstruction P

/-- **The split** from the three leaves (the union's with the atom test). -/
noncomputable def parts_of_leaves2 (p : PrimitiveLeaf G) (u : UnionLeaf2 G S) (r : RecoveryLeaf2 G S) : Parts :=
  { kclk := u.1
    envelope := G.E
    budget := G.budget u.1 p.1 u.2.1 u.2.2.1 u.2.2.2.1
    inputs := G.inputs u.1 p.1 u.2.1 u.2.2.1 u.2.2.2.1
    union := (u.2.2.2.2 p.1).toUnionConstruction
    primitive := p.2 u.1 u.2.1 u.2.2.1 u.2.2.2.1
    recovery := r u.1 p.1 u.2.1 u.2.2.1 u.2.2.2.1 (u.2.2.2.2 p.1) (p.2 u.1 u.2.1 u.2.2.1 u.2.2.2.1) }

end Gate

section Free
variable (l : Literals)

/-- **Leaf U with the atom test and the free constants**: for every choice meeting the relations, leaf U at the gate
and pinned setup. -/
def UnionLeafF2 := ∀ F : GateFree l, GateFreeOK l F → UnionLeaf2 (gate0 l F) (setupF l F)

/-- **Leaf R with the free constants**, for the union leaves with the atom test. -/
def RecoveryLeafF2 := ∀ F : GateFree l, GateFreeOK l F → RecoveryLeaf2 (gate0 l F) (setupF l F)

/-- **The split** from the three leaves with the free constants (leaf P unchanged). -/
noncomputable def parts_of_leavesF2 (p : PrimitiveLeafF l) (u : UnionLeafF2 l) (r : RecoveryLeafF2 l) : Parts :=
  parts_of_leaves2 (gate0 l p.1) (setupF l p.1) p.2.2 (u p.1 p.2.1) (r p.1 p.2.1)

end Free

/-- **The split in the shape of the reduce at `parts`** (`literals_parts_of_leavesF` with the atom test). -/
noncomputable def literals_parts_of_leavesF2 (p : ∀ l, PrimitiveLeafF l) (u : ∀ l, UnionLeafF2 l)
    (r : ∀ l, RecoveryLeafF2 l) : Literals → Parts :=
  fun l => parts_of_leavesF2 l (p l) (u l) (r l)

end NearCubicWires.WireExponent3_5.Split
