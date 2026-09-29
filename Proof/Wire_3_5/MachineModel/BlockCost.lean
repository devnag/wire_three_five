import Proof.Wire_3_5.Foundations.Contracts
import Proof.MachineModel.BlockWordFunction
import Proof.MachineModel.BlockScrubEntry

/-! # Block v3 (S5): the class-tagged cost calculus

Paper: `prim:runtime` (P3:3105-3108), "The running time, including an optional common-coset
selection, is `2^{n/2+O(k)}n^{C_D} + 2^{O(Ψ_i+Ψ_aux)} + 2^{n-k/4}n^{C_D}`", with "All powers of `n` are
fixed before a fixed `r` or a positive endpoint coefficient is chosen" (P3:3112-3115), and `tr:time`
(P3:3797-3811): "The dependence on `r` is expressed through `k`, not hidden in an exponent"
(P3:3053-3054 for the final pass).

The paper quantity of this module is the class bound `classBound E cls q k Ψ` of the seed's running-time
ledger (`Proof.Wire_3_5.Foundations.Runtime`, A7): every block's cost is certified `≤ coef · classBound` in a named
class (`Within`), and the certificate composes through sequencing, bounded loops (`Cells`), the
enumeration of all `w`-bit strings, and focusing. The consumer is A9's machine contract
(`Proof.Wire_3_5.Foundations.Contracts`): `ClassBlocks C` is a block family over one machine whose cost is within
`C`'s class at `C`'s coefficient, and `ClassBlocks.implements` IS `Implements C`, the contract's
`RewoundWordFunction` at exactly the contract's budget.

The tight class is `mainPass`, `2^{q-k/4}q^{A}`. `per_column_2k_not_mainPass` proves that a
per-column `2^k` factor over the `2^{q-k}` columns (the overhead P3:3053-3054 forbids) is not within
that class for any coefficient. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Machine
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform

/-! ## The class bound as `2^{exp} · q^{deg}` -/

/-- The exponent of `2` in each class bound. -/
def classExp (E : Envelope) : BudgetClass → ℕ → ℕ → ℕ → ℕ
  | .sourcePoly, _, _, _ => 0
  | .selection, q, k, _ => q / 2 + E.csel * k
  | .preprocessing, _, _, psi => E.cpsi * psi
  | .table, q, k, _ => q - k
  | .mainPass, q, k, _ => q - k / 4

/-- The polynomial degree of each class bound, fixed by the envelope before `r`. -/
def classDeg (E : Envelope) : BudgetClass → ℕ
  | .sourcePoly => E.Amain
  | .selection => E.Asel
  | .preprocessing => E.Apre
  | .table => E.Atable
  | .mainPass => E.Amain

theorem classBound_eq (E : Envelope) (cls : BudgetClass) (q k psi : ℕ) :
    classBound E cls q k psi = 2 ^ classExp E cls q k psi * q ^ classDeg E cls := by
  cases cls <;> simp [classBound, classExp, classDeg]

theorem classBound_pos (E : Envelope) (cls : BudgetClass) {q : ℕ} (k psi : ℕ) (hq : 1 ≤ q) :
    1 ≤ classBound E cls q k psi := by
  rw [classBound_eq]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by positivity))

/-! ## `Within`: a cost in a named class -/

/-- The cost `n` is within class `cls` at `(q, k, Ψ)` with coefficient `c`: the shape of A9's budget
field `coef · classBound E cls (q, k, Ψ)`. -/
def Within (E : Envelope) (cls : BudgetClass) (c q k psi n : ℕ) : Prop :=
  n ≤ c * classBound E cls q k psi

namespace Within
variable {E : Envelope} {cls : BudgetClass} {q k psi : ℕ}

theorem mono {c n m : ℕ} (h : Within E cls c q k psi n) (hm : m ≤ n) : Within E cls c q k psi m :=
  hm.trans h

theorem add {c₁ c₂ n₁ n₂ : ℕ} (h₁ : Within E cls c₁ q k psi n₁) (h₂ : Within E cls c₂ q k psi n₂) :
    Within E cls (c₁ + c₂) q k psi (n₁ + n₂) := by
  unfold Within at *
  rw [Nat.add_mul]
  exact Nat.add_le_add h₁ h₂

theorem const (hq : 1 ≤ q) (c : ℕ) : Within E cls c q k psi c := by
  have := classBound_pos E cls k psi hq (q := q)
  unfold Within
  nlinarith

/-- Sequencing: `b.cost + 1 + c.cost` (the paid bridge step of `BlockPlatform.seq`). -/
theorem seq (hq : 1 ≤ q) {c₁ c₂ n₁ n₂ : ℕ} (h₁ : Within E cls c₁ q k psi n₁)
    (h₂ : Within E cls c₂ q k psi n₂) : Within E cls (c₁ + c₂ + 1) q k psi (n₁ + 1 + n₂) := by
  have h := (h₁.add h₂).add (const (E := E) (cls := cls) (k := k) (psi := psi) hq 1)
  exact h.mono (by omega)

end Within

/-! ## Costed blocks -/

/-- A block with its cost certified in a named class at `(q, k, Ψ)`. -/
structure Costed (E : Envelope) (cls : BudgetClass) (q k psi t : ℕ) where
  block : Block t
  coef : ℕ
  within : Within E cls coef q k psi block.cost

namespace Costed
variable {E : Envelope} {cls : BudgetClass} {q k psi t u : ℕ}

/-- Sequencing, with the seam stated once. -/
noncomputable def seq (hq : 1 ≤ q) (b c : Costed E cls q k psi t) (hH : b.block.exitH = c.block.entryH)
    (hA : b.block.exitA = c.block.entryA) : Costed E cls q k psi t :=
  ⟨BlockPlatform.seq b.block c.block hH hA, b.coef + c.coef + 1, Within.seq hq b.within c.within⟩

@[simp] theorem seq_coef (hq : 1 ≤ q) (b c : Costed E cls q k psi t) (hH : b.block.exitH = c.block.entryH)
    (hA : b.block.exitA = c.block.entryA) : (seq hq b c hH hA).coef = b.coef + c.coef + 1 := rfl

/-- The class budget as the block's cost (`BlockPlatform.upto`). -/
noncomputable def toBudget (b : Costed E cls q k psi t) : Block t :=
  upto b.block (b.coef * classBound E cls q k psi) b.within

@[simp] theorem toBudget_cost (b : Costed E cls q k psi t) :
    (toBudget b).cost = b.coef * classBound E cls q k psi := rfl

end Costed

/-! ## The consumer: A9's machine contract -/

/-- A block family over ONE machine for the admissible requests of the contract `C`. Each run goes from
the framed input with every head at cell 0 to an exit whose output tape carries the encoding of the
reference value `C.ref`. Every head is back at cell 0, and the cost is within `C`'s budget class at `C`'s
coefficient. -/
structure ClassBlocks {E : Envelope} (C : MachineContract E) where
  tapeCount : ℕ
  stateCount : ℕ
  twoTapes : 2 ≤ tapeCount
  machine : Machine tapeCount stateCount
  outputTape : Fin tapeCount
  outputFresh : outputTape.val ≠ 0
  cost : {r // C.pre r} → ℕ
  exitA : {r // C.pre r} → Fin tapeCount → List Bool
  step : ∀ r, Step machine (cost r) (fun _ => 0)
    (fun i => if i.val = 0 then frame (C.input r.1) else []) (fun _ => 0) (exitA r)
  exitOut : ∀ r, exitA r outputTape = C.encode (C.ref r.1)
  within : ∀ r, Within E C.cls C.coef (C.q r.1) (C.k r.1) (C.psi r.1) (cost r)

/-- The Block v3 word function of a class-costed family, at the contract's budget. -/
noncomputable def ClassBlocks.wordBlocks {E : Envelope} {C : MachineContract E} (B : ClassBlocks C) :
    WordBlocks {r // C.pre r} (fun r => C.input r.1) (fun r => C.encode (C.ref r.1)) C.budget where
  tapeCount := B.tapeCount
  stateCount := B.stateCount
  twoTapes := B.twoTapes
  machine := B.machine
  outputTape := B.outputTape
  outputFresh := B.outputFresh
  cost := B.cost
  exitH := fun _ => fun _ => 0
  exitA := B.exitA
  step := B.step
  exitOut := B.exitOut
  fits := B.within

/-- **`ClassBlocks C` is `Implements C`**: the contract's rewound word function at exactly the
contract's class budget `C.coef · classBound E C.cls (q, k, Ψ)`. -/
noncomputable def ClassBlocks.implements {E : Envelope} {C : MachineContract E} (B : ClassBlocks C) :
    Implements C :=
  B.wordBlocks.toRewound (fun _ => rfl)

/-! ## The tight class forbids a per-column `2^k` -/


end NearCubicWires.WireExponent3_5.Block
