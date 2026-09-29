import Proof.Wire_3_5.FinalPass.SeamsProg2

/-! # Uniform stage constants in `FinalPassLeaf`'s order of choice (class)

`fpPlan` (`FinalPassLeaf`) chooses, after the endpoint exponent `fe`, the floors `E₅`, `CD₅`; then for every
admissible `F` the coefficient `c₅`; then the machine at every clock and source work (P3:3114-3115: the load constant
and the envelope are fixed before `r`). A stage's cost bound `C·2^{D·ψ}·(|fpIn|+1)^D` (or `C·(n+1)^D`) fits
`c₅·finalClasses E₅` only if its exponent `D` is chosen with `E₅` (so it may depend on `(l, fe)` only) and its
coefficient `C` with `c₅` (on `(l, fe, F)` only). **`StageU`** states that, generically in the stage family:

`∀ fe, Σ D₀ E₀ CD₀, ∀ F, F.filterErrDeg = fe → ClassLE E₀ F.E → CD₀ ≤ F.CD → Σ C₀, ∀ kclk coef A a ha,
{x // deg x ≤ D₀ ∧ cf x ≤ C₀}`.

`StageU.pair` puts two families side by side (exponents `max`, coefficients `+`, floors `envMax`/`max`), so S2, S3,
S4, S5-THR, S5-core and the output machine target one wrapper (build once). Dock (gate 1): `seedsDeg`/`seedsCf` for `SeedsProg2`,
**`SeedsProg2.cost_le_uni`** (the seeds phase's cost at the uniform constants), and `StageU.at` (the instance and
its bounds at `fpPlan`'s binders). Paper quantities: the phases' constants in `prim:runtime` (P3:3105-3115). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.Split

section Uni
variable (l : Literals)

/-- **Uniform constants of a stage family**, in `FinalPassLeaf`'s order of choice. -/
def StageU (S : (F : GateFree l) → (kclk coef A a : ℕ) → a ≤ kclk + 1 → Type)
    (deg : ∀ {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}, S F kclk coef A a ha → ℕ)
    (cf : ∀ {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}, S F kclk coef A a ha → ℕ) : Type :=
  ∀ fe : ℕ, Σ D₀ : ℕ, Σ E₀ : Envelope, Σ CD₀ : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ClassLE E₀ F.E →
    CD₀ ≤ F.CD → Σ C₀ : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      { x : S F kclk coef A a ha // deg x ≤ D₀ ∧ cf x ≤ C₀ }

variable {l}

/-- **Two uniform families side by side**: exponents `max`, coefficients `+`, floors `envMax` / `max`. -/
def StageU.pair {S₁ S₂ : (F : GateFree l) → (kclk coef A a : ℕ) → a ≤ kclk + 1 → Type}
    {deg₁ : ∀ {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}, S₁ F kclk coef A a ha → ℕ}
    {cf₁ : ∀ {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}, S₁ F kclk coef A a ha → ℕ}
    {deg₂ : ∀ {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}, S₂ F kclk coef A a ha → ℕ}
    {cf₂ : ∀ {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}, S₂ F kclk coef A a ha → ℕ}
    (U₁ : StageU l S₁ deg₁ cf₁) (U₂ : StageU l S₂ deg₂ cf₂) :
    StageU l (fun F kclk coef A a ha => S₁ F kclk coef A a ha × S₂ F kclk coef A a ha)
      (fun x => max (deg₁ x.1) (deg₂ x.2)) (fun x => cf₁ x.1 + cf₂ x.2) :=
  fun fe =>
    let V₁ := U₁ fe
    let V₂ := U₂ fe
    ⟨max V₁.1 V₂.1, envMax V₁.2.1 V₂.2.1, max V₁.2.2.1 V₂.2.2.1, fun F hF hE hCD =>
      let W₁ := V₁.2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE) (le_trans (le_max_left _ _) hCD)
      let W₂ := V₂.2.2.2 F hF (classLE_trans (classLE_envMax_right _ _) hE) (le_trans (le_max_right _ _) hCD)
      ⟨W₁.1 + W₂.1, fun kclk coef A a ha =>
        ⟨((W₁.2 kclk coef A a ha).1, (W₂.2 kclk coef A a ha).1),
          max_le_max (W₁.2 kclk coef A a ha).2.1 (W₂.2 kclk coef A a ha).2.1,
          Nat.add_le_add (W₁.2 kclk coef A a ha).2.2 (W₂.2 kclk coef A a ha).2.2⟩⟩⟩

end Uni

/-! ## Dock: the seeds phase at uniform constants -/

section Family

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams
