import Proof.Wire_3_5.Assembly.FreeBase
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

/-- Seed fixing's classes (`seedFix_classes`): selection + preprocessing + 2·table. -/
def seedClasses (E₄ : Envelope) (q k psi : ℕ) : ℕ :=
  classBound E₄ .selection q k psi + classBound E₄ .preprocessing q k psi + 2 * classBound E₄ .table q k psi

/-- The final pass's classes: its explicit descriptions (the middle term, P3:3170-3173) + the main pass. -/
def finalClasses (E₅ : Envelope) (q k psi : ℕ) : ℕ :=
  classBound E₅ .preprocessing q k psi + classBound E₅ .mainPass q k psi

/-- `thr_call_error`'s endpoint hypothesis (census G7'): `|𝒢|·ξ ≤ n^{−D}/8` at every THR call. -/
def ThrEndpoint {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
    (alg : RepairRepresentation.DecompositionAlgorithm) : Prop :=
  ∀ {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ), I.Call (thrReq n a ha Cs carriers translation) → ∀ hs : I.StarAt n,
      (Fintype.card (ThrEq (I.starParams n hs) Cs alg) : ℝ) * (1 / 2 ^ (I.filterParams .thr n).errExp) ≤
        (n : ℝ) ^ (-(I.D : ℝ)) / 8

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

/-! ## The enclosing application -/

section Assembly

end Assembly

end NearCubicWires.WireExponent3_5.PrimAsm.Plan
