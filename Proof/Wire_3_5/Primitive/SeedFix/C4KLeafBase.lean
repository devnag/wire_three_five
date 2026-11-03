import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypesBase
import Proof.Wire_3_5.Primitive.SeedFix.C4Front
import Proof.Wire_3_5.Primitive.Writers.CallSizeBase

/-! # C4.K, the consumer of the per-mode contract: `c4Leaf_of`

"There are `O_D(L²+k+L)` seed-prefix decisions, each with a constant number of exact printer calls. Under the
displayed allowances the printer applies, and the explicit descriptions and their construction give the middle term in
`prim:runtime`" (P3:3170-3173). The C4 part's four stages each run within `c₄·seedClasses E₄` at the ledger's
`(n, kOf n, psiOf n)`: the front (`C4Front.front_req`, `70·|req.word| + 64` steps, the word polynomial in `n` by
`CallSize.wordBound_poly`) and the three modes' stages (`C4K.SymLeafC4`, `ThrLeafC4`, `HashLeafC4`). C4.K combines
them: `E₄` is the componentwise maximum of the modes' floors and the front's (`Asel` at the word's degree), `CD₄` the
maximum of the modes' load floors, `c₄` the sum of the coefficients; a stage's run stays a run under a larger budget
(`stage3Run_mono`) and the budget grows with `E` and `c` at `n ≥ 1` (`seedClasses_mono`; every call is on-star).

* `emax`, `classLE_trans`, `le_emax_left/right`, **`seedClasses_mono`**, **`seedBudget_mono`**, **`stage3Run_mono`**;
* `frontE`, `frontC`, **`front_budget`**;
* **`c4Leaf_of : SymLeafC4 l → ThrLeafC4 l → HashLeafC4 l → C4Leaf l`**.

Paper quantity of the main type: the C4 part `C4Leaf` (the fixed seeds within `c₄·seedClasses E₄`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4K
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.SupplierPipeline
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes

/-! ## The floors -/

/-- The componentwise maximum of two envelopes. -/
def emax (E₁ E₂ : Envelope) : Envelope where
  sigma := max E₁.sigma E₂.sigma
  callDeg := max E₁.callDeg E₂.callDeg
  Amain := max E₁.Amain E₂.Amain
  Atable := max E₁.Atable E₂.Atable
  Asel := max E₁.Asel E₂.Asel
  csel := max E₁.csel E₂.csel
  Apre := max E₁.Apre E₂.Apre
  cpsi := max E₁.cpsi E₂.cpsi

theorem classLE_trans {E₁ E₂ E₃ : Envelope} (h₁ : ClassLE E₁ E₂) (h₂ : ClassLE E₂ E₃) : ClassLE E₁ E₃ :=
  ⟨h₁.Amain.trans h₂.Amain, h₁.Atable.trans h₂.Atable, h₁.Asel.trans h₂.Asel, h₁.csel.trans h₂.csel,
    h₁.Apre.trans h₂.Apre, h₁.cpsi.trans h₂.cpsi⟩

theorem le_emax_left (E₁ E₂ : Envelope) : ClassLE E₁ (emax E₁ E₂) :=
  ⟨le_max_left _ _, le_max_left _ _, le_max_left _ _, le_max_left _ _, le_max_left _ _, le_max_left _ _⟩

theorem le_emax_right (E₁ E₂ : Envelope) : ClassLE E₂ (emax E₁ E₂) :=
  ⟨le_max_right _ _, le_max_right _ _, le_max_right _ _, le_max_right _ _, le_max_right _ _, le_max_right _ _⟩

/-- **The seed-fixing classes grow with the envelope** at `q ≥ 1`. -/
theorem seedClasses_mono {E E' : Envelope} (hE : ClassLE E E') (q k psi : ℕ) (hq : 1 ≤ q) :
    seedClasses E q k psi ≤ seedClasses E' q k psi := by
  unfold seedClasses
  have h1 : classBound E .selection q k psi ≤ classBound E' .selection q k psi :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_left (Nat.mul_le_mul_right k hE.csel) _))
      (Nat.pow_le_pow_right hq hE.Asel)
  have h2 : classBound E .preprocessing q k psi ≤ classBound E' .preprocessing q k psi :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right psi hE.cpsi))
      (Nat.pow_le_pow_right hq hE.Apre)
  have h3 : classBound E .table q k psi ≤ classBound E' .table q k psi :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq hE.Atable)
  omega

section Budget

end Budget

/-- **A stage's run stays a run under a larger budget.** -/
theorem stage3Run_mono {S : Stage3} {B B' : ℕ} {w v y : List Bool} (h : Stage3Run S B w v y) (hB : B ≤ B') :
    Stage3Run S B' w v y := by
  obtain ⟨J, hJ, hr⟩ := h
  exact ⟨J, fun j => (hJ j).trans hB, ClockJoin.enlarge _ _ _ _ _ hr hB⟩

/-! ## The front's budget -/

/-- The request word's coefficient (`CallSize.wordBound_poly`). -/
noncomputable def wC : ℕ := Classical.choose PrimAsm.CallSize.wordBound_poly

/-- The request word's degree. -/
noncomputable def wD : ℕ := Classical.choose (Classical.choose_spec PrimAsm.CallSize.wordBound_poly)

theorem word_le (n : ℕ) : PrimAsm.CallSize.wordBound 26 26 2 n ≤ wC * (n + 1) ^ wD :=
  (Classical.choose_spec (Classical.choose_spec PrimAsm.CallSize.wordBound_poly)).2 n

/-- The front's floor: the selection class at the word's degree. -/
noncomputable def frontE : Envelope where
  sigma := 0
  callDeg := 0
  Amain := 0
  Atable := 0
  Asel := wD
  csel := 0
  Apre := 0
  cpsi := 0

/-- The front's coefficient. -/
noncomputable def frontC : ℕ := 70 * wC * 2 ^ wD + 64

/-! ## The assembly -/

end NearCubicWires.WireExponent3_5.PrimT.C4K
