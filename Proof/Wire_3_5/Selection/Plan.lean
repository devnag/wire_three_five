import Proof.Wire_3_5.UnionMachine.Plan

/-! # C1, coset selection: the enclosing term of `C1Impl` (P3:1324-1362, 3071-3072, 3673)

Paper: star:selection, "A product-code coset with `E_x Σ_X p_X R_X(x) ≤ C_0 r^{3/2}/n^{3/2} Σ_X p_X W_X` is findable
deterministically in `2^{n/2+O(k)} poly(n)` time" (P3:1328-1335), by computing each candidate's objective exactly
("Enumerate its `2^k` error rows. For each gate and row, the four threshold predicates have integer scores of the form
`a_j(z_L)+b_j(z_R)` [...] For each of the sixteen corner patterns, count pairs satisfying its four weak inequalities
[...] Select a minimum objective", P3:1337-1360); the union machine "selects the common star translation" (P3:3673).

The residual C1 owes leaf U (C6's plan) is `C1Impl = ∀ d, C1At d`: at every input-size degree
`d`, an envelope `E₁ d`, a coefficient `c₁ d` and `Implements (c1sized d (E₁ d) (c₁ d))` (the C1 contract at the union's
encodings `selWord`/`cosetWord`, with `|selWord R| ≤ (n+1)^d`). One machine serves every `d`: its run does not read `d`;
only the class bound does (the input's size enters the polynomial factor). **`c1Impl_of`** is the enclosing term: from
a machine run (**`C1Run`**: on every request meeting C1's base precondition, from the word function's entry bank to a
bank with every head at cell `0` whose output tape holds `cosetWord (selArgmin R)`) and a class bound for every `d`
(**`C1Within`**), it yields `C1Impl`. The paper quantities are the selected coset (the first minimizer of the exact
objective) and the selection time `2^{n/2+O(k)}·poly(n)`. Main declarations: `C1Run`, `C1Within`, **`c1At_of`**,
**`c1Impl_of`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Plan
open NearCubicWires NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch

/-- C1's base precondition (the star parameters' conditions and the weights' distribution), i.e. `c1inst`'s. -/
def BasePre (R : SelectionReq) : Prop :=
  R.r % 2 = 0 ∧ 2 ≤ R.r ∧ 4 * R.r ≤ R.n ∧ (R.pops.map Prod.snd).sum = 1 ∧ ∀ X ∈ R.pops, 0 ≤ X.2

/-- **The run residual**: one machine, on every request meeting C1's base precondition, runs from the word function's
entry bank to a bank with every head at cell `0` whose output tape `o` holds the selected coset's word. -/
def C1Run {t s : ℕ} (M : Machine t s) (o : Fin t) (cost : SelectionReq → ℕ) : Prop :=
  ∀ R : SelectionReq, BasePre R → ∃ A : Fin t → List Bool,
    Step M (cost R) (fun _ => 0) (fun i => if i.val = 0 then frame (selWord R) else []) (fun _ => 0) A ∧
      A o = cosetWord (selArgmin R)

/-- **The class residual**: at input-size degree `d`, the cost is within the selection class of the envelope `E₁`
at the coefficient `c₁` (arguments `q = n`, `k = r·s`, `Ψ = 0`). -/
def C1Within (d : ℕ) (E₁ : Envelope) (c₁ : ℕ) (cost : SelectionReq → ℕ) : Prop :=
  ∀ R : SelectionReq, (c1sized d E₁ c₁).pre R → Within E₁ .selection c₁ R.n R.k 0 (cost R)

theorem basePre_of (d : ℕ) (E₁ : Envelope) (c₁ : ℕ) (R : SelectionReq) (h : (c1sized d E₁ c₁).pre R) : BasePre R :=
  h.1

/-- **C1 at one input-size degree** from its two residuals. -/
noncomputable def c1At_of (d : ℕ) (E₁ : Envelope) (c₁ : ℕ) {t s : ℕ} (M : Machine t s) (ht : 2 ≤ t) (o : Fin t)
    (ho : o.val ≠ 0) (cost : SelectionReq → ℕ) (run : C1Run M o cost) (within : C1Within d E₁ c₁ cost) : C1At d :=
  ⟨E₁, c₁, ClassBlocks.implements
    { tapeCount := t
      stateCount := s
      twoTapes := ht
      machine := M
      outputTape := o
      outputFresh := ho
      cost := fun r => cost r.1
      exitA := fun r => Classical.choose (run r.1 (basePre_of d E₁ c₁ r.1 r.2))
      step := fun r => (Classical.choose_spec (run r.1 (basePre_of d E₁ c₁ r.1 r.2))).1
      exitOut := fun r => (Classical.choose_spec (run r.1 (basePre_of d E₁ c₁ r.1 r.2))).2
      within := fun r => within r.1 r.2 }⟩

/-- **The enclosing term of `C1Impl`**: one machine and its run, an envelope and coefficient per input-size degree,
and the class bound at each. -/
noncomputable def c1Impl_of {t s : ℕ} (M : Machine t s) (ht : 2 ≤ t) (o : Fin t) (ho : o.val ≠ 0)
    (cost : SelectionReq → ℕ) (run : C1Run M o cost) (E₁ : ℕ → Envelope) (c₁ : ℕ → ℕ)
    (within : ∀ d, C1Within d (E₁ d) (c₁ d) cost) : C1Impl :=
  fun d => c1At_of d (E₁ d) (c₁ d) M ht o ho cost run (within d)


end NearCubicWires.WireExponent3_5.SelectionMachine.Plan
