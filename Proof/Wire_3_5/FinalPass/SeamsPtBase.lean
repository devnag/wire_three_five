import Proof.Wire_3_5.FinalPass.SeamsBase

/-! # The final pass's seams, part 2: the per-point evaluators, the front's exit, the cost residual

Consumer backward from `NumDenOut` (P3:3170-3181): `Num = Σ_c Σ_e Σ_ℓ M(e, x)·Σ R̂(x)` at `x = (c, u_ℓ, v_ℓ)`.
`R̂` does not depend on the filter seed `e` (`thrRhat`, `symRhatFast` take no seed) and the mask `M` is the SAME
function in both modes (`maskBits`), so the point value factors (`ptThr_mask`, `ptSym_mask`): the per-point
evaluators (S2 THR, S3 SYM) compute `Σ R̂` alone (`rsumThr`, `rsumSym`), and the seeds phase (S4) computes the mask
once per point and seed (stage 7 on the seed's table) and adds `M·Σ R̂` to its binary accumulator.

* **`PtIn`** / **`PtOut`**: the per-point evaluator's entry and exit at a generic layout. Streams: the point
  `frame (ofFn c)`, `frame (ofFn e_L(u))`, `frame (ofFn e_R(v))` (stage 2's `C, U, V`; the center stream is X3's
  `ctrW` output, `frame_eq_frameP`), the evaluator's call words (read-only), its scratch streams (reading blank:
  every cell `false`); all these heads at `0`. Registers: the accumulator and the scratch registers zero, the call
  numbers. Exit: the accumulator holds `v`, every head and every other register as at entry, every stream outside
  the scratch unchanged, the scratch reading blank again (loop-safe).
* **`PtEvalW`**: one evaluator per mode; it DECLARES its call words and numbers (the words the front must leave),
  with capacity and cost polynomial in `ptSize` (the point, the words, the numbers). S2 is
  `PtEvalW ThrCall … rsumThr`, S3 is `PtEvalW SymCall … rsumSym`.
* **`FrontOut`** (S5 → S4): the front's exit bank at a request: the declared words on their tapes, the numbers in
  `W`-bit binary (`frame (binary W v)`, C6's `NumOn` form), every other tape `false` of the declared length `bl`
  (S4's register tapes), every head at `0`.
* **`ptCount`**, **`seedCount`**, **`FitsRes`**, `fits_of` (S6): the phases' cost bounds against `c₅·finalClasses`,
  with the seeds phase's bound in the shape `|E|·tab + (|centers|·|E|·Q)·pt + ov` (`seedsShape`).

Paper quantities: the per-point sums `Σ_{g,p} R̂_{g,p}` and `Σ_{e'} R̂_{e'}`, the mask `M(e, x)`, the numbers of
seeds and of point evaluations, the budget `c₅·finalClasses`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.NumDen
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.Split

/-! ## The per-point sums and the mask factor -/

section Point
variable (P : StarParams) {a : ℕ}

/-- **The THR per-point sum** `Σ_{g,p} R̂_{g,p}(c, u, v)` at the reporter `report`. -/
def rsumThr (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ) (c : BitInput P.n)
    (u v : P.Errors) : ℕ :=
  ∑ gp : ThrEq P Cs algorithm × PrimeIndex (thrCutoff P Cs algorithm den),
    (thrRhat P Cs algorithm den report gp.1 gp.2 c u v).toNat

/-- **The SYM per-point sum** `Σ_{e'} R̂_{e'}(c, u, v)` over the list seeds. -/
def rsumSym (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (Pl : FlatListParams) (c : BitInput P.n)
    (u v : P.Errors) : ℕ :=
  ∑ el : Pl.FlatSeed, (symRhatFast P Cs Pl el c u v).toNat

variable (σ : P.Translation) {N Q : ℕ} (eqv : P.Errors ≃ Fin N) (S : Fin Q → Fin N × Fin N)

/-- The THR point value is the mask times the per-point sum. -/
theorem ptThr_mask (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ)
    (c : {c // P.IsCenter σ c}) (e : GapSeed FP) (l : Fin Q) :
    ptThr P σ eqv S Cs carriers FP algorithm den report c e l =
      (maskBits P σ carriers FP e (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))).toNat *
        rsumThr P Cs algorithm den report c.1 (eqv.symm (S l).1) (eqv.symm (S l).2) := by
  unfold ptThr rsumThr
  rw [Finset.mul_sum]

/-- The SYM point value is the mask times the per-point sum. -/
theorem ptSym_mask (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (Pl : FlatListParams) (c : {c // P.IsCenter σ c}) (e : GapSeed FP) (l : Fin Q) :
    ptSym P σ eqv S Cs carriers FP Pl c e l =
      (maskBits P σ carriers FP e (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))).toNat *
        rsumSym P Cs Pl c.1 (eqv.symm (S l).1) (eqv.symm (S l).2) := by
  unfold ptSym rsumSym
  rw [Finset.mul_sum]

end Point

/-! ## The per-point evaluator's entry, exit and type -/

section Eval
variable {ns nr nw nn nsc nrs : ℕ} (S : Fin 3 ⊕ Fin nw ⊕ Fin nsc ↪ Fin (ns + 1))
  (R : Fin 1 ⊕ Fin nn ⊕ Fin nrs ↪ Fin nr)

/-- **The per-point entry**: the point framed on `S (inl 0..2)`, the call words `ws` on `S (inr (inl k))`, the
scratch streams `S (inr (inr j))` reading blank, all these heads at `0`; the numbers `vs` in `R (inr (inl i))`, the
accumulator `R (inl 0)` and the scratch registers `R (inr (inr j))` zero. -/
structure PtIn {n : ℕ} (c eu ev : BitInput n) (ws : Fin nw → List Bool) (vs : Fin nn → ℕ) (σ : WState ns nr) :
    Prop where
  ptC : σ.st (S (.inl 0)) = frame (List.ofFn c)
  ptU : σ.st (S (.inl 1)) = frame (List.ofFn eu)
  ptV : σ.st (S (.inl 2)) = frame (List.ofFn ev)
  wd : ∀ k, σ.st (S (.inr (.inl k))) = ws k
  sc : ∀ j, ∀ b ∈ σ.st (S (.inr (.inr j))), b = false
  heads : ∀ i, σ.sh (S i) = 0
  num : ∀ i, σ.val (R (.inr (.inl i))) = vs i
  acc : σ.val (R (.inl 0)) = 0
  zero : ∀ j, σ.val (R (.inr (.inr j))) = 0

/-- **The per-point exit**: the accumulator holds `v`; every head, every other register and the cell as at entry;
every stream outside the scratch unchanged; the scratch reading blank again. -/
structure PtOut (σ τ : WState ns nr) (v : ℕ) : Prop where
  val : τ.val = Function.update σ.val (R (.inl 0)) v
  sh : τ.sh = σ.sh
  cell : τ.cell = σ.cell
  st : ∀ i, (∀ j, i ≠ S (.inr (.inr j))) → τ.st i = σ.st i
  sc : ∀ j, ∀ b ∈ τ.st (S (.inr (.inr j))), b = false

end Eval

/-- **A per-point evaluator** of the value `val` over the calls `K` (S2 / S3 → S4): it declares its call words and
numbers; one word program per layout, with capacity and cost polynomial in `ptSize`, writes `val k c u v` into the
accumulator from every `PtIn` entry at the point `(c, u, v)` (the halves as error vectors, `e_L(u)`, `e_R(v)`). -/
structure PtEvalW (K : Type) (P : K → StarParams)
    (val : (k : K) → BitInput (P k).n → (P k).Errors → (P k).Errors → ℕ) where
  nw : ℕ
  nn : ℕ
  nsc : ℕ
  nrs : ℕ
  words : K → Fin nw → List Bool
  nums : K → Fin nn → ℕ
  prog : ∀ {ns nr : ℕ}, (Fin 3 ⊕ Fin nw ⊕ Fin nsc ↪ Fin (ns + 1)) → (Fin 1 ⊕ Fin nn ⊕ Fin nrs ↪ Fin nr) → WM ns nr
  need : ℕ → ℕ
  bound : ℕ → ℕ
  C : ℕ
  D : ℕ
  need_le : ∀ M, need M ≤ C * (M + 1) ^ D
  bound_le : ∀ M, bound M ≤ C * (M + 1) ^ D
  run : ∀ {ns nr : ℕ} (S : Fin 3 ⊕ Fin nw ⊕ Fin nsc ↪ Fin (ns + 1)) (R : Fin 1 ⊕ Fin nn ⊕ Fin nrs ↪ Fin nr)
    (k : K) (c : BitInput (P k).n) (u v : (P k).Errors) (cap : ℕ) (σ : WState ns nr),
    PtIn S R c ((P k).errorVector (P k).leftBlock u) ((P k).errorVector (P k).rightBlock v) (words k) (nums k) σ →
    need ((P k).n + (∑ i, (words k i).length) + ∑ i, nums k i) ≤ cap →
    ∃ τ, WExec cap (prog S R) σ τ (bound ((P k).n + (∑ i, (words k i).length) + ∑ i, nums k i)) ∧
      PtOut S R σ τ (val k c u v)

/-- **The THR call data** a THR per-point evaluator sees: the tuple, the algorithm, the cutoff's `den`, and the
digit lists' data `D` (the reporter is `ListFast.listReportFast D`; at a call, the fixed hash's data). -/
structure ThrCall where
  P : StarParams
  a : ℕ
  ha : a ≤ 4
  Cs : Fin a → NormalizedThresholdThresholdCircuit P.n
  alg : RepairRepresentation.DecompositionAlgorithm
  den : ℕ
  D : ListData

/-- **The SYM call data** a SYM per-point evaluator sees: the tuple and the flat lists' parameters. -/
structure SymCall where
  P : StarParams
  a : ℕ
  ha : a ≤ 4
  Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n
  Pl : FlatListParams

/-- **S3's type**: the SYM per-point evaluator of `Σ_{e'} R̂_{e'}`. -/
abbrev SymPtEval : Type :=
  PtEvalW SymCall (fun k => k.P) fun k c u v => rsumSym k.P k.Cs k.Pl c u v

/-! ## S5 → S4: the front's exit -/

section Family
variable (l : Literals) (E₅ : Envelope) (c₅ kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-! ## S6: the cost residual -/

/-- **The number of point evaluations** at a request: `|centers|·|filter seeds|·Q`. -/
def ptCountOf {kc : ℕ} {E : Envelope} {B : TimeBudget kc E} (I : PrimitiveInputs B)
    (alg : RepairRepresentation.DecompositionAlgorithm) : PrimRequest → ℕ
  | ⟨n, .sym, _, _, Cs, carriers, translation⟩ =>
      if hs : I.StarAt n then
        Fintype.card {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c} *
          Fintype.card (GapSeed (I.filterParams .sym n)) *
            ((SeedFix.greedySampler I alg).symS Cs carriers translation hs).Q
      else 0
  | ⟨n, .thr, _, _, Cs, carriers, translation⟩ =>
      if hs : I.StarAt n then
        Fintype.card {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c} *
          Fintype.card (GapSeed (I.filterParams .thr n)) *
            ((SeedFix.greedySampler I alg).thrS Cs carriers translation hs).Q
      else 0

/-- **The seeds phase's cost shape** (S4 → S6): per filter seed the table (`tab`), per point evaluation the point
(`pt`: stage 0, the mask, the evaluator, the accumulator), plus the overhead `ov`. -/
def seedsShape (nE tab nPt pt ov : ℕ) : ℕ := nE * tab + nPt * pt + ov

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams
