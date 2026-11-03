import Statement_Wire_3_5
import Proof.Wire_3_5.Foundations.Runtime
import Bindings.CLW20_Theorem1_13
import Proof.CaseAnalysis.Assembly
import Proof.Circuits.PolynomialOrdinaryClock
import Proof.Foundations.SupplierPipeline
import Proof.Wire_3_5.Foundations.Carrier
import Proof.Wire_3_5.Foundations.GapFilter

/-! # The transfer skeleton: row B from the literals and one fused `Parts`

Realizes the transfer of `tr:appendix` (P3:3232-3957) consumer backward from `rowB`:
* the last step (P3:3813-3853): an `E^NP` certificate plus per-class hardness at every fixed multiplier give
  `WireExponent3_5` (`wireExponent3_5_of_parts`; the onset is the maximum of the two class onsets);
* the refuter step (P3:3699-3702): "By Lemma tr:soundness this machine is one-sided. Once its clock is `o(T(N))`,
  the refuter consequently returns a rejected hierarchy yes-instance at every sufficiently large `N`"
  (`refuter_rejected_yes`, from the CLW20 Theorem 1.13 literal), at the clock of P3:3633, "Choose a polynomial
  hierarchy clock `T(N)=N^{C_clk}`";
* `lem:primitive` (P3:3066-3116) as `FusedPrimitive I`, indexed by the caller's inputs `I : PrimitiveInputs B`
  (P3:3068-3084): its estimate of the masked mean `E_{e,x}[M(e,x) ∏ C_i(x)]` (`prim:truth`, P3:3087-3091) exists
  only as the output word of one program whose budget is the per-call budget of the time ledger `B`
  (`prim:runtime`, P3:3105-3115), with error `n^{−D}` on every admissible tuple; the circuits `C_i` are circuits of
  the class mode (`Mode.Circuit`, the Theorem 2.5 integer syntax) and their functions are `Mode.eval`, a definition;
  a call carries its named carriers and the common star translation, which are per-run data (the machine "guesses
  [...] one sparse grid sum for each distinct PCPP variable" and then "selects the common star translation,
  constructs the shared coordinate filters", P3:3669-3674); an admissible tuple is one whose gates
  are contained in the named carriers (`GatesIn`, P3:3083-3086), and the mask `M(e,x)` is the product of the
  `filt:gap` regular filters of the named carriers' signed mixed-residual populations at the translation, with one
  common seed (P3:3074-3080, 3432-3436), a definition, not an input;
* the union weak machine (P3:3669-3697) as `UnionConstruction I`: a construction applied to the primitive, with
  `tr:soundness` (P3:3504-3554) and `tr:time` (P3:3797-3811) stated for every primitive at `I`; `tr:time` is the
  split of `Runtime3`, so the machine's `o(T(N))` clock comes from `Runtime3.littleO`;
* canonical recovery, `E^NP`, and Cases 1 and 2 (P3:3704-3779) as `Recovery U P`, indexed by the machine built
  from `P`.

Main types: `Parts`, one structure fusing the time ledger, the primitive's inputs, the union construction, the
primitive and the recovery obligations; and the root producer `literals_rowB_of_parts : (Literals → Parts) →
Literals → rowB`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.CLW20Theorem113 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Filters

/-! ## The seam to the statement (P3:3813-3853) -/

/-- One class clause of `WireExponent3_5Hard` at one multiplier, in the Theorem 2.5 vocabulary (`wireCount`,
`agreement`), which is what the Case 1 and Case 2 hardness results produce. -/
def ThrHardAt (c KT : ℝ) (language : Language) (AT : ℝ) : Prop :=
  ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n → ∀ circuit : ThresholdThresholdCircuit n,
    (circuit.wireCount : ℝ) ≤ AT * (n : ℝ) ^ ((7 : ℝ) / 2) / (Nat.clog 2 (n + 2) : ℝ) ^ KT →
      agreement circuit.eval (language n) < 1 / 2 + (Nat.clog 2 (n + 2) : ℝ) ^ (-c)

/-- The `SYM∘THR` clause of `WireExponent3_5Hard` at one multiplier. -/
def SymHardAt (c KS : ℝ) (language : Language) (AS : ℝ) : Prop :=
  ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n → ∀ circuit : SymmetricThresholdCircuit n,
    (circuit.wireCount : ℝ) ≤ AS * (n : ℝ) ^ ((7 : ℝ) / 2) / (Nat.clog 2 (n + 2) : ℝ) ^ KS →
      agreement circuit.eval (language n) < 1 / 2 + (Nat.clog 2 (n + 2) : ℝ) ^ (-c)

/-- The statement's THR wire count is the Theorem 2.5 `wireCount`. -/
theorem thr_wires_eq {n : ℕ} (circuit : ThresholdThresholdCircuit n) :
    ((∑ i : Fin circuit.bottomCount,
        if circuit.topWeight i = 0 then 0 else (circuit.bottom i).support.card + 1 : ℕ) : ℝ) =
      (circuit.wireCount : ℝ) := by
  unfold ThresholdThresholdCircuit.wireCount
  rw [Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : circuit.topWeight i = 0 <;> simp [h]

/-- The statement's SYM wire count is the Theorem 2.5 `wireCount`. -/
theorem sym_wires_eq {n : ℕ} (circuit : SymmetricThresholdCircuit n) :
    ((∑ i : Fin circuit.bottomCount, ((circuit.bottom i).support.card + 1) : ℕ) : ℝ) =
      (circuit.wireCount : ℝ) := rfl

/-- The last step (P3:3813-3853): `E^NP` plus per-class hardness at every fixed multiplier is `WireExponent3_5`. -/
theorem wireExponent3_5_of_parts (c KT KS : ℝ) (language : Language)
    (certificate : OrdinaryENPCertificate RecoveryOracle.correctedSat language)
    (thr : ∀ AT : ℝ, 0 < AT → ThrHardAt c KT language AT)
    (sym : ∀ AS : ℝ, 0 < AS → SymHardAt c KS language AS) :
    WireExponent3_5 c KT KS := by
  refine ⟨language, Closeout.membership language certificate, ?_⟩
  intro AT AS hAT hAS
  obtain ⟨o₁, h₁⟩ := thr AT hAT
  obtain ⟨o₂, h₂⟩ := sym AS hAS
  refine ⟨max o₁ o₂, fun n hn => ⟨fun circuit hcap => ?_, fun circuit hcap => ?_⟩⟩
  · rw [thr_wires_eq] at hcap
    exact h₁ n (le_of_max_le_left hn) circuit hcap
  · rw [sym_wires_eq] at hcap
    exact h₂ n (le_of_max_le_right hn) circuit hcap

/-! ## The refuter step (P3:3699-3702) -/

/-- `tr:soundness` in the refuter's terms, past an onset: "no branch of the weak machine accepts a hierarchy
no-instance, for all sufficiently large source lengths" (P3:3506-3508). -/
def OneSided (M : OrdinaryWeakMachine) (L : Language) : Prop :=
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ x : BitInput n, M.accepts n x → L n x = true

/-! ## The primitive (`lem:primitive`, P3:3066-3116) -/

/-- The circuits of a class mode (P3:209-216), in the Theorem 2.5 integer syntax with exact support
(`SupplierPipeline`): `THR∘THR` and `SYM∘THR`. Every circuit of the statement's types has one with the same
function and wire count (`SupplierPipeline.normalizeThresholdCircuit`, `normalizeSymmetricCircuit`, from the
normalization contract; `alg:normalization`, P3:1552-1566). Constants, complemented atoms and the systematic parity
(P3:3092-3094) are `SYM∘THR` circuits of this syntax. -/
def Mode.Circuit : Mode → ℕ → Type
  | .thr, n => SupplierPipeline.NormalizedThresholdThresholdCircuit n
  | .sym, n => SupplierPipeline.NormalizedSymmetricThresholdCircuit n

/-- The circuit's function: the standard semantics of each class mode. -/
def Mode.eval {n : ℕ} : (m : Mode) → m.Circuit n → BitInput n → Bool
  | .thr, c => SupplierPipeline.NormalizedThresholdThresholdCircuit.eval c
  | .sym, c => SupplierPipeline.NormalizedSymmetricThresholdCircuit.eval c

/-- The circuit's canonical code (the Theorem 2.5 family-tagged encoding). -/
def Mode.code {n : ℕ} : (m : Mode) → m.Circuit n → ℕ
  | .thr, c => SupplierPipeline.encodeNormalizedThresholdThresholdCircuit c
  | .sym, c => SupplierPipeline.encodeNormalizedSymmetricThresholdCircuit c

/-- The charged gates of a circuit of a class mode (P3:213-216: the gates its wire count charges): the bottoms at
retained top positions of a `THR∘THR` circuit, every bottom of a `SYM∘THR` circuit. -/
def Mode.gates {n : ℕ} : (m : Mode) → m.Circuit n → Stars.Carrier n
  | .thr, c => Stars.thrGates c
  | .sym, c => Stars.symGates c

/-- The circuit's public description length (the Theorem 2.5 `descriptionBits`). -/
def Mode.descriptionBits {n : ℕ} : (m : Mode) → m.Circuit n → ℕ
  | .thr, c => SupplierPipeline.NormalizedThresholdThresholdCircuit.descriptionBits c
  | .sym, c => SupplierPipeline.NormalizedSymmetricThresholdCircuit.descriptionBits c

/-- The unnormalized masked expectation `E_{e,x}[M(e,x) ∏_{i<a} C_i(x)]` of `prim:truth` (P3:3087-3091): the mask
multiplies inside the average and is never divided out. -/
noncomputable def maskedMean {Seed : Type} [Fintype Seed] {n a : ℕ}
    (M : Seed → BitInput n → Bool) (C : Fin a → BitInput n → Bool) : ℝ :=
  (∑ e, ∑ x, (if M e x then (1 : ℝ) else 0) * ∏ i, (if C i x then (1 : ℝ) else 0)) /
    ((Fintype.card Seed : ℝ) * 2 ^ n)

/-- A primitive call (P3:3071-3091): length, class mode, a tuple of at most four circuits of that mode, the named
carriers whose filters form the mask (a name is its position in `carriers`; "Each call uses only a fixed number of
these names", P3:3078), and the common star translation (P3:3072), as one syndrome code per block
(`StarParams.translationOfCodes`). Carriers and translation are per-run data of the union machine (P3:3669-3674),
so the call carries them. -/
structure PrimRequest where
  n : ℕ
  mode : Mode
  a : ℕ
  ha : a ≤ 4
  circuits : Fin a → mode.Circuit n
  carriers : List (Stars.Carrier n)
  translation : List ℕ

/-- The framed encoding of a request: the circuits and the carriers by their canonical codes, and the translation's
syndrome codes. -/
def PrimRequest.word (r : PrimRequest) : List Bool :=
  natWord r.n ++ [(match r.mode with | .thr => true | .sym => false)] ++ natWord r.a ++
    (List.ofFn fun i => natWord (r.mode.code (r.circuits i))).flatten ++
    natListWord (r.carriers.map Stars.Carrier.code) ++ natListWord r.translation

/-- The charged gates of every circuit of a request. -/
def PrimRequest.gates (req : PrimRequest) : Fin req.a → Stars.Carrier req.n :=
  fun i => req.mode.gates (req.circuits i)

/-- **"Whose gates are contained in these carriers"** (P3:3083-3086): every circuit's gate list is a sub-multiset
of the union of the named carriers. -/
def PrimRequest.gatesIn (req : PrimRequest) (named : List (Stars.Carrier req.n)) : Prop :=
  Stars.GatesIn req.gates named

/-- The printed estimate: numerator and denominator words. -/
def ratWord (q : ℚ) : List Bool := intWord q.num ++ natWord q.den


/-- The caller's inputs of `lem:primitive`, fixed before the algorithm (P3:3068-3084): "Fix a polynomial
description envelope, a tuple arity at most four, and an accuracy exponent `D > 0`. Let `r` be even, use the
partition of star:partition, and suppose `L ≤ k = rs ≤ polylog(n)`. Let `B ≥ 1` be polynomially bounded. [...] For
each name, use the regular filter of filt:gap on its signed mixed-residual population, with cap `B` and an endpoint
error chosen as a sufficiently small fixed inverse power of `n`." The primitive is indexed by these inputs and cannot
choose them: the accuracy exponent `D`, the description envelopes of the circuits and of the carriers, the number of
names per call, the polylogarithmic bound on `k`, and the endpoint error exponent. The star multiplier `r` and the
per-mode caps `B_i` are the ledger's (`B.rOf`, `B.capOf`: the parameter ledger chooses them, P3:3425-3430,
3823-3824, and the load `B.psiOf` is computed from them). The carriers and the translation are
per-run data carried by each call; the admissible tuples (`PrimRequest.gatesIn`), the regular filters and their
common seed space (`filt:gap`), and the circuits' functions (`Mode.eval`) are definitions, not inputs. -/
structure PrimitiveInputs {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) where
  /-- the accuracy exponent `D > 0` -/
  D : ℕ
  D_pos : 0 < D
  /-- `k ≤ polylog(n)`: `k ≤ L(n)^kDeg` -/
  kDeg : ℕ
  /-- the polynomial description envelope: each circuit has at most `(n+1)^descDeg` description bits -/
  descDeg : ℕ
  /-- each call uses at most `nameCount` names -/
  nameCount : ℕ
  /-- the carriers' description envelope: at most `(n+1)^carrierDeg` atoms of `(n+1)^carrierDeg` bits each
  (P3:3071-3072, 3092-3094) -/
  carrierDeg : ℕ
  /-- the endpoint error exponent: the filters' error is `2^{−filterErrDeg·L(n)} ≤ (n+2)^{−filterErrDeg}`
  (P3:3075-3076) -/
  filterErrDeg : ℕ

namespace PrimitiveInputs
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- The star hypotheses of `lem:primitive` at length `n` (P3:3069-3070, `star:partition` P3:1188-1189), for the
ledger's multiplier `r = B.rOf n` (whose star width `B.kOf n = r·⌊log₂(n/r+1)⌋` is a definition): `r` even,
`2 ≤ r ≤ n/4`, and `L(n) ≤ k ≤ L(n)^kDeg`. -/
def StarAt (I : PrimitiveInputs B) (n : ℕ) : Prop :=
  Even (B.rOf n) ∧ 2 ≤ B.rOf n ∧ 4 * B.rOf n ≤ n ∧
    Nat.clog 2 (n + 2) ≤ B.kOf n ∧ B.kOf n ≤ Nat.clog 2 (n + 2) ^ I.kDeg

/-- The star parameters at a length where the star hypotheses hold (`star:partition`, P3:1188). -/
def starParams (I : PrimitiveInputs B) (n : ℕ) (h : I.StarAt n) : Shared.StarParams :=
  ⟨n, B.rOf n, h.1, h.2.1, h.2.2.1⟩

/-- The regular filter's parameters in class mode `m` at length `n` (`filt:gap`, P3:2019-2025): the
population-vector length bound `2(n+1)^carrierDeg` (two residual bits per atom), the ledger's cap `B_m(n)`
(P3:3406-3407, 3425-3430), and the endpoint error exponent. -/
def filterParams (I : PrimitiveInputs B) (m : Mode) (n : ℕ) : GapParams :=
  ⟨2 * (n + 1) ^ I.carrierDeg, B.capOf m n, I.filterErrDeg * Nat.clog 2 (n + 2)⟩

/-- The common finite seed space of the named filters in class mode `m` at length `n` (P3:3079-3080). -/
abbrev Seed (I : PrimitiveInputs B) (m : Mode) (n : ℕ) : Type := GapSeed (I.filterParams m n)

open Classical in
/-- The mask `M(e,x)` of a call (P3:3072-3080, 3432-3436): the product, over the call's named carriers, of the
`filt:gap` regular filter of the carrier's signed mixed-residual population at `x`, read through the decomposition
`x = c + u + v` in the call's translation, with one common seed `e`. Reusing a name's carrier reuses its filter. -/
noncomputable def mask (I : PrimitiveInputs B) (req : PrimRequest) (e : I.Seed req.mode req.n)
    (x : BitInput req.n) : Bool :=
  if h : I.StarAt req.n then
    req.carriers.all fun X => gapFilter (I.filterParams req.mode req.n) e
      (Stars.inputResidualBits (I.starParams req.n h)
        ((I.starParams req.n h).translationOfCodes req.translation) X x)
  else true

/-- The translation codes are well formed: one syndrome code `< 2^s` per block (P3:1206-1207). -/
def _root_.NearCubicWires.WireExponent3_5.Cost.TimeBudget.TranslationOk (B : TimeBudget kclk E) (req : PrimRequest) :
    Prop :=
  req.translation.length = B.rOf req.n ∧ ∀ t ∈ req.translation, t < 2 ^ Nat.log 2 (req.n / B.rOf req.n + 1)

/-- The per-call hypothesis: an admissible tuple (its gates contained in the named carriers, P3:3083-3086) within
the circuit and carrier description envelopes and the name count, with a well-formed translation, at a length where
the star hypotheses and the ledger's fit conditions hold (the load condition `max{Ψ_i, Ψ_aux} ≤ c₀(n−k)`,
P3:3106-3107, is `Fits.pre`). -/
def Call (I : PrimitiveInputs B) (req : PrimRequest) : Prop :=
  req.gatesIn req.carriers ∧ (∀ X ∈ req.carriers, X.WithinEnvelope I.carrierDeg) ∧
    (∀ i, req.mode.descriptionBits (req.circuits i) ≤ (req.n + 1) ^ I.descDeg) ∧
    req.carriers.length ≤ I.nameCount ∧ B.TranslationOk req ∧ I.StarAt req.n ∧ B.FitsAt req.n

/-- The quantity the primitive estimates, `E_{e,x}[M(e,x) ∏ C_i(x)]` (`prim:truth`, P3:3087-3091), with the
call's mask and the circuits' own functions. -/
noncomputable def truth (I : PrimitiveInputs B) (req : PrimRequest) : ℝ :=
  maskedMean (Seed := I.Seed req.mode req.n) (I.mask req) (fun i => req.mode.eval (req.circuits i))

end PrimitiveInputs

/-- `lem:primitive` (P3:3066-3116) at the caller's inputs `I`: "there is a deterministic algorithm estimating
`E_{e,x}[M(e,x) ∏ C_i(x)]` to absolute error at most `n^{−D}`" for every admissible tuple, in the running time
`prim:runtime` (P3:3105-3115). The five field groups are: the inputs (the index `I`), the precondition
(`I.Call`), the budget (`B.callBudget`), the output (`value`, which exists only as the output word of
`estimator`), and the error (`error`). -/
structure FusedPrimitive {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B) where
  /-- the printed estimate -/
  value : PrimRequest → ℚ
  /-- one program printing `value` within the per-call budget, on every call meeting the precondition -/
  estimator : OrdinaryWordFunction {req : PrimRequest // I.Call req} (fun req => req.1.word)
    (fun req => ratWord (value req.1)) (fun req => B.callBudget req.1.n)
  /-- error `n^{−D}` against the caller's masked mean, for every call meeting the precondition -/
  error : ∀ req, I.Call req → |(value req : ℝ) - I.truth req| ≤ (req.n : ℝ) ^ (-(I.D : ℝ))

/-! ## The union weak machine (P3:3669-3697) -/

/-- The union weak machine as a construction applied to a primitive at the caller's inputs `I`: "The weak machine
[...] selects the common star translation, constructs the shared coordinate filters, and performs (tr:tests)"
(P3:3689-3691). Its obligations are stated for every primitive at `I`: `tr:soundness` (P3:3504-3554) and
`tr:time` (P3:3797-3811), the latter as the ledger's split of the built machine's running time, at the hierarchy
clock of P3:3633, "Choose a polynomial hierarchy clock `T(N)=N^{C_clk}`", with `C_clk = kclk + 2`. -/
structure UnionConstruction {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B) where
  build : FusedPrimitive I → Language → OrdinaryWeakMachine
  /-- `tr:soundness` (P3:3504-3554), from the primitive's error bound -/
  soundness : ∀ (P : FusedPrimitive I) (L : Language), InNTIME (fun n => n ^ (kclk + 2)) L →
    OneSided (build P L) L
  /-- `tr:time` (P3:3797-3811), from the primitive's program budget -/
  time : ∀ (P : FusedPrimitive I) (L : Language), B.Split (build P L)

/-- The built machine's `Runtime3`: the ledger with the machine's split. -/
def UnionConstruction.runtime3 {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}
    (U : UnionConstruction I) (P : FusedPrimitive I) (L : Language) :
    Runtime3 (U.build P L) kclk E :=
  { B with split := U.time P L }

/-! ## Recovery, `E^NP`, and Cases 1 and 2 (P3:3704-3779) -/

/-- The recovery obligations, indexed by the machine actually built from `P`: canonical recovery with the growing
XOR schedule (P3:3736-3756), the slice in `E^NP` (P3:3758-3772), and Cases 1 and 2 with padding and the target
comparisons (P3:3704-3729, 3774-3779, 3813-3852), whose conclusions are exactly the row-B class clauses. -/
structure Recovery {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}
    (U : UnionConstruction I) (P : FusedPrimitive I) where
  language : Language → Language
  certificate : ∀ L, OrdinaryENPCertificate RecoveryOracle.correctedSat (language L)
  thr : ∀ L, InNTIME (fun n => n ^ (kclk + 2)) L →
    (∃ onset : ℕ, ∀ n, onset ≤ n → ∃ x : BitInput n, L n x = true ∧ ¬ (U.build P L).accepts n x) →
      ∀ AT : ℝ, 0 < AT → ThrHardAt (1 / 8) (11 / 2) (language L) AT
  sym : ∀ L, InNTIME (fun n => n ^ (kclk + 2)) L →
    (∃ onset : ℕ, ∀ n, onset ≤ n → ∃ x : BitInput n, L n x = true ∧ ¬ (U.build P L).accepts n x) →
      ∀ AS : ℝ, 0 < AS → SymHardAt (1 / 8) (9 / 2) (language L) AS

/-! ## The one open part -/

/-- The premises of `rowB_of_fused`, fused: the time ledger (with its clock exponent and envelope), the
primitive's caller inputs, the union construction, the primitive at those inputs, and the recovery obligations for
the machine built from that primitive. -/
structure Parts where
  kclk : ℕ
  envelope : Envelope
  budget : TimeBudget kclk envelope
  inputs : PrimitiveInputs budget
  union : UnionConstruction inputs
  primitive : FusedPrimitive inputs
  recovery : Recovery union primitive

end NearCubicWires.WireExponent3_5
