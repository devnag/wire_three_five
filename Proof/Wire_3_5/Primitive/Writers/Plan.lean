import Proof.Wire_3_5.Assembly.Free
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixSampler
import Proof.Wire_3_5.FinalPass.SampleRef

/-! # Leaf P's enclosing application and its four residuals (PA)

Realizes `lem:primitive` (P3:3066-3116) at the gate: "there is a deterministic algorithm estimating
`E_{e,x}[M(e,x)∏_{i=1}^a C_i(x)]` to absolute error at most `n^{−D}`", in the running time `prim:runtime`
(P3:3105-3115), "`2^{n/2+O(k)}n^{C_D} + 2^{O(Ψ_i+Ψ_aux)} + 2^{n−k/4}n^{C_D}`". The algorithm of the proof is: fix the
seeds, then run the final pass: "There are `O_D(L²+k+L)` seed-prefix decisions, each with a constant number of exact
printer calls. Under the displayed allowances the printer applies, and the explicit descriptions and their construction
give the middle term in (prim:runtime). The final pass evaluates `2^{3k/4}n^{O_D(1)}` reported lookups at each column,
giving the last term" (P3:3170-3175). The order of choice is the paper's: "All powers of `n` are fixed before a fixed `r`
or a positive endpoint coefficient is chosen" (P3:3114-3115), and "The original threshold normalization, fixed class
mode, polynomial tuple count, numerical errors, and every description-size envelope are fixed first [...] increasing
the star-block parameter later changes the explicit exponential factors through `k`, not these frozen polynomial
exponents" (P3:3185-3190).

Paper quantities of the main types:
* `seedWord I alg req`: the call's fixed seeds, `samp:printable`'s sample (P3:2977-3055) in the final pass's format, and
  for THR `filt:soft`'s fixed hash (P3:2238-2251);
* `SeedFixAt`: seed fixing, `req.word ↦ seedWord`, within the classes selection + preprocessing + 2·table (`seedFix_classes`);
* `FinalPassAt`: the final pass, `req.word ++ seedWord ↦ ratWord (greedyValue)`, the printed estimate of `prim:truth`,
  within preprocessing + main pass (P3:3170-3175);
* `ThrEndpoint`: `|𝒢|·ξ ≤ n^{−D}/8`, the endpoint hypothesis of `thr_call_error` (census G7');
* `ComposeLeaf`: the per-call program at `callBudget` from the two machines (`prim:runtime`).

Main declarations: the residuals `SeedFixLeaf`, `FinalPassLeaf` (C4+C5), `EndpointLeaf`, `ComposeLeaf` (PA);
the free constants `leafFree`; the enclosing application **`leafP : … → ∀ l, PrimitiveLeafF l`**, with value
`SeedFix.greedyValue` and error `SeedFix.greedyValue_error`; `rowB_of_residuals`; and the index independence
`call_indep`, `greedyValue_indep`, `seedWord_indep` (the residuals' machines need not read `kclk, coef, A, a`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Transfer

/-- Componentwise order on the class exponents of two envelopes (`callDeg` and `sigma` are not class exponents). -/
structure ClassLE (E₁ E : Envelope) : Prop where
  Amain : E₁.Amain ≤ E.Amain
  Atable : E₁.Atable ≤ E.Atable
  Asel : E₁.Asel ≤ E.Asel
  csel : E₁.csel ≤ E.csel
  Apre : E₁.Apre ≤ E.Apre
  cpsi : E₁.cpsi ≤ E.cpsi

/-! ## The fixed seeds of a call -/

section Seeds
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- **The seeds a call fixes before its final pass** (P3:3165-3175): `samp:printable`'s greedy sample of both class modes
in the final pass's format (`sampleWord`, per pair the framed `kh`-bit halves), and for THR, after it, the framed bits of
`filt:soft`'s fixed hash. Empty off the star hypotheses (no call there). -/
def seedWord (I : PrimitiveInputs B) (alg : RepairRepresentation.DecompositionAlgorithm) : PrimRequest → List Bool
  | ⟨n, .sym, _, _, Cs, carriers, translation⟩ =>
      if hs : I.StarAt n then
        FinalPass.Sample.sampleWord (SeedFix.callKh (I.starParams n hs))
          (List.ofFn fun j => (((SeedFix.symCallSample I hs Cs carriers translation).S j).1.val,
            ((SeedFix.symCallSample I hs Cs carriers translation).S j).2.val))
      else []
  | ⟨n, .thr, _, _, Cs, carriers, translation⟩ =>
      if hs : I.StarAt n then
        FinalPass.Sample.sampleWord (SeedFix.callKh (I.starParams n hs))
            (List.ofFn fun j => (((SeedFix.thrCallSample alg I hs Cs carriers translation).S j).1.val,
              ((SeedFix.thrCallSample alg I hs Cs carriers translation).S j).2.val)) ++
          frame (List.ofFn (FinalPass.thrHashBits (I.starParams n hs)
            ((I.starParams n hs).translationOfCodes translation) Cs carriers (I.filterParams .thr n) alg
            (thrCallDen alg I hs Cs) (thrCallE alg I hs Cs carriers) (thrCallT alg I hs Cs carriers)
            (thrCallJ alg I hs Cs carriers)))
      else []

end Seeds

/-! ## The residual types -/

section Residuals
variable (l : Literals)

/-- The caller's inputs of `lem:primitive` at the gate (P3:3068-3084). -/
noncomputable abbrev callInputs (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    PrimitiveInputs ((gate0 l F).budget kclk coef A a ha) :=
  (gate0 l F).inputs kclk coef A a ha

/-- Seed fixing's classes (`seedFix_classes`): selection + preprocessing + 2·table. -/
def seedClasses (E₄ : Envelope) (q k psi : ℕ) : ℕ :=
  classBound E₄ .selection q k psi + classBound E₄ .preprocessing q k psi + 2 * classBound E₄ .table q k psi

/-- The final pass's classes: its explicit descriptions (the middle term, P3:3170-3173) + the main pass. -/
def finalClasses (E₅ : Envelope) (q k psi : ℕ) : ℕ :=
  classBound E₅ .preprocessing q k psi + classBound E₅ .mainPass q k psi

/-- **Seed fixing at one call family**: `req.word ↦ seedWord`, within `c₄·seedClasses E₄` at the ledger's
`(n, kOf n, psiOf n)`. -/
abbrev SeedFixAt (F : GateFree l) (E₄ : Envelope) (c₄ kclk coef A a : ℕ) (ha : a ≤ kclk + 1) : Type :=
  RewoundWordFunction {req : PrimRequest // (callInputs l F kclk coef A a ha).Call req}
    (fun r => r.1.word) (fun r => seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1)
    (fun r => c₄ * seedClasses E₄ r.1.n (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
      (((gate0 l F).budget kclk coef A a ha).psiOf r.1.n))

/-- **The final pass at one call family**: `req.word ++ seedWord ↦ ratWord (greedyValue)`, within `c₅·finalClasses E₅`. -/
abbrev FinalPassAt (F : GateFree l) (E₅ : Envelope) (c₅ kclk coef A a : ℕ) (ha : a ≤ kclk + 1) : Type :=
  RewoundWordFunction {req : PrimRequest // (callInputs l F kclk coef A a ha).Call req}
    (fun r => r.1.word ++ seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1)
    (fun r => ratWord (SeedFix.greedyValue (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1))
    (fun r => c₅ * finalClasses E₅ r.1.n (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
      (((gate0 l F).budget kclk coef A a ha).psiOf r.1.n))

/-- **Residual C4** (C4+C5): after the endpoint exponent `fe`, the floors `E₄`, `CD₄` (powers of `n`, fixed before
`r`, P3:3114-3115, 3185-3190); then, for every choice of the free constants above the floors, a coefficient and the
machine at every clock and source work. -/
def SeedFixLeaf : Type :=
  ∀ fe : ℕ, Σ E₄ : Envelope, Σ CD₄ : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ClassLE E₄ F.E → CD₄ ≤ F.CD →
    Σ c₄ : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), SeedFixAt l F E₄ c₄ kclk coef A a ha

/-- **Residual C5** (C4+C5), in the same order of choice. -/
def FinalPassLeaf : Type :=
  ∀ fe : ℕ, Σ E₅ : Envelope, Σ CD₅ : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ClassLE E₅ F.E → CD₅ ≤ F.CD →
    Σ c₅ : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FinalPassAt l F E₅ c₅ kclk coef A a ha

/-- `thr_call_error`'s endpoint hypothesis (census G7'): `|𝒢|·ξ ≤ n^{−D}/8` at every THR call. -/
def ThrEndpoint {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
    (alg : RepairRepresentation.DecompositionAlgorithm) : Prop :=
  ∀ {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ), I.Call (thrReq n a ha Cs carriers translation) → ∀ hs : I.StarAt n,
      (Fintype.card (ThrEq (I.starParams n hs) Cs alg) : ℝ) * (1 / 2 ^ (I.filterParams .thr n).errExp) ≤
        (n : ℝ) ^ (-(I.D : ℝ)) / 8

/-- **Residual PA.g7**: an endpoint exponent (fixed after the decomposition algorithm, before the envelope) meeting G7'
at every call. -/
def EndpointLeaf : Type :=
  Σ fe : ℕ, (1 + 2 ≤ fe) ×' ∀ F : GateFree l, F.filterErrDeg = fe →
    ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), ThrEndpoint (callInputs l F kclk coef A a ha) (gate0 l F).alg

/-- **Residual PA.compose**: the glue floor `Eg`, a coefficient rule, and the per-call program at `callBudget` from the
two machines (`prim:runtime`, P3:3105-3115). -/
def ComposeLeaf : Type :=
  Σ Eg : Envelope, Σ cg : ℕ → ℕ → ℕ, ∀ (F : GateFree l) (E₄ E₅ : Envelope) (c₄ c₅ : ℕ),
    ClassLE E₄ F.E → ClassLE E₅ F.E → ClassLE Eg F.E →
    ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), cg c₄ c₅ ≤ coef →
      SeedFixAt l F E₄ c₄ kclk coef A a ha → FinalPassAt l F E₅ c₅ kclk coef A a ha →
      RepairSource.OrdinaryWordFunction {req : PrimRequest // (callInputs l F kclk coef A a ha).Call req}
        (fun r => r.1.word)
        (fun r => ratWord (SeedFix.greedyValue (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1))
        (fun r => ((gate0 l F).budget kclk coef A a ha).callBudget r.1.n)

/-! ### Index independence: the residuals' requests, value and seeds do not read `kclk, coef, A, a` -/

end Residuals

/-! ## The free constants -/

/-- Componentwise maximum of two envelopes. -/
def envMax (E₁ E₂ : Envelope) : Envelope :=
  ⟨max E₁.sigma E₂.sigma, max E₁.callDeg E₂.callDeg, max E₁.Amain E₂.Amain, max E₁.Atable E₂.Atable,
    max E₁.Asel E₂.Asel, max E₁.csel E₂.csel, max E₁.Apre E₂.Apre, max E₁.cpsi E₂.cpsi⟩

theorem classLE_envMax_left (E₁ E₂ : Envelope) : ClassLE E₁ (envMax E₁ E₂) :=
  ⟨le_max_left _ _, le_max_left _ _, le_max_left _ _, le_max_left _ _, le_max_left _ _, le_max_left _ _⟩

theorem classLE_envMax_right (E₁ E₂ : Envelope) : ClassLE E₂ (envMax E₁ E₂) :=
  ⟨le_max_right _ _, le_max_right _ _, le_max_right _ _, le_max_right _ _, le_max_right _ _, le_max_right _ _⟩

theorem classLE_trans {E₁ E₂ E₃ : Envelope} (h₁ : ClassLE E₁ E₂) (h₂ : ClassLE E₂ E₃) : ClassLE E₁ E₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2, h₁.3.trans h₂.3, h₁.4.trans h₂.4, h₁.5.trans h₂.5, h₁.6.trans h₂.6⟩

variable (l : Literals)

/-- The given class exponents with `σ = A_pad + 1` (P3:3644) and `callDeg = unionCallDeg + c` (`GateFreeOK`). -/
noncomputable def envAt (E' : Envelope) : Envelope :=
  { E' with sigma := gateApad l + 1, callDeg := unionCallDeg l + callDegMargin }

theorem classLE_envAt (E' : Envelope) : ClassLE E' (envAt l E') :=
  ⟨le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, le_refl _⟩

/-- The free constants from an endpoint exponent, class exponents and `C_D`; `c_r = 1` (every `c_r ≥ 1` works). -/
noncomputable def freeOf (fe : ℕ) (hfe : 1 + 2 ≤ fe) (E' : Envelope) (CD : ℕ) : GateFree l where
  E := envAt l E'
  hσ := le_refl _
  CD := CD
  cr := 1
  cr_pos := le_refl _
  filterErrDeg := fe
  hG7 := hfe

theorem freeOf_ok (fe : ℕ) (hfe : 1 + 2 ≤ fe) (E' : Envelope) (CD : ℕ) : GateFreeOK l (freeOf l fe hfe E' CD) :=
  ⟨le_refl _⟩

/-! ## The enclosing application -/

section Assembly
variable (g7 : ∀ l, EndpointLeaf l) (cmp : ∀ l, ComposeLeaf l) (s4 : ∀ l, SeedFixLeaf l) (s5 : ∀ l, FinalPassLeaf l)

/-- The class exponents: the maximum of the two machines' floors and the glue floor (census G8). -/
def leafEnv : Envelope := envMax (envMax (s4 l (g7 l).1).1 (s5 l (g7 l).1).1) (cmp l).1

/-- **The free constants of leaf P** (P3:3114-3115, 3185-3190): the endpoint exponent first (after the decomposition
algorithm), then the envelope and `C_D` from the floors, `c_r = 1`. -/
noncomputable def leafFree : GateFree l :=
  freeOf l (g7 l).1 (g7 l).2.1 (leafEnv l g7 cmp s4 s5) (max (s4 l (g7 l).1).2.1 (s5 l (g7 l).1).2.1)

theorem leafFree_h4 : ClassLE (s4 l (g7 l).1).1 (leafFree l g7 cmp s4 s5).E :=
  classLE_trans (classLE_trans (classLE_envMax_left _ _) (classLE_envMax_left _ _)) (classLE_envAt l _)

theorem leafFree_h5 : ClassLE (s5 l (g7 l).1).1 (leafFree l g7 cmp s4 s5).E :=
  classLE_trans (classLE_trans (classLE_envMax_right _ _) (classLE_envMax_left _ _)) (classLE_envAt l _)

theorem leafFree_hg : ClassLE (cmp l).1 (leafFree l g7 cmp s4 s5).E :=
  classLE_trans (classLE_envMax_right _ _) (classLE_envAt l _)

/-- Seed fixing's coefficient and machines at the chosen constants. -/
noncomputable def leafM4 :=
  (s4 l (g7 l).1).2.2 (leafFree l g7 cmp s4 s5) rfl (leafFree_h4 l g7 cmp s4 s5) (le_max_left _ _)

/-- The final pass's coefficient and machines at the chosen constants. -/
noncomputable def leafM5 :=
  (s5 l (g7 l).1).2.2 (leafFree l g7 cmp s4 s5) rfl (leafFree_h5 l g7 cmp s4 s5) (le_max_right _ _)

/-- The primitive's coefficient (census G2). -/
noncomputable def leafCoef : ℕ := (cmp l).2.1 (leafM4 l g7 cmp s4 s5).1 (leafM5 l g7 cmp s4 s5).1

/-- **`lem:primitive` at the gate**, for every clock and source work: the value `greedyValue`, the composed program, the
error `greedyValue_error`. -/
noncomputable def leafFused (kclk A a : ℕ) (ha : a ≤ kclk + 1) :
    FusedPrimitive (callInputs l (leafFree l g7 cmp s4 s5) kclk (leafCoef l g7 cmp s4 s5) A a ha) where
  value := SeedFix.greedyValue _ (gate0 l (leafFree l g7 cmp s4 s5)).alg
  estimator := (cmp l).2.2 (leafFree l g7 cmp s4 s5) _ _ _ _ (leafFree_h4 l g7 cmp s4 s5) (leafFree_h5 l g7 cmp s4 s5)
    (leafFree_hg l g7 cmp s4 s5) kclk (leafCoef l g7 cmp s4 s5) A a ha (le_refl _)
    ((leafM4 l g7 cmp s4 s5).2 kclk (leafCoef l g7 cmp s4 s5) A a ha)
    ((leafM5 l g7 cmp s4 s5).2 kclk (leafCoef l g7 cmp s4 s5) A a ha)
  error := SeedFix.greedyValue_error l.eightSources.expander l.eightSources.prime _ _
    (gate0 l (leafFree l g7 cmp s4 s5)).hG7
    ((g7 l).2.2 (leafFree l g7 cmp s4 s5) rfl kclk (leafCoef l g7 cmp s4 s5) A a ha)

end Assembly

/-- **Leaf P's enclosing application**: the producer of the nested reduce at `primitive`, from the four residuals. -/
noncomputable def leafP (g7 : ∀ l, EndpointLeaf l) (cmp : ∀ l, ComposeLeaf l) (s4 : ∀ l, SeedFixLeaf l)
    (s5 : ∀ l, FinalPassLeaf l) : ∀ l, PrimitiveLeafF l := fun l =>
  ⟨leafFree l g7 cmp s4 s5, freeOf_ok l _ _ _ _, ⟨leafCoef l g7 cmp s4 s5, leafFused l g7 cmp s4 s5⟩⟩

end NearCubicWires.WireExponent3_5.PrimAsm.Plan
