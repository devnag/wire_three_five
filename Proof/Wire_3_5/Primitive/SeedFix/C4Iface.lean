import Proof.Wire_3_5.Primitive.SeedFix.C4Geo

/-! # SEEDFIX C4.L: two stage interfaces built by C6

**(2) The compiler's input assembler.** "For each candidate child prefix [...] the printed objective is compiled"
(P3:3035-3037) through `alg:compiler` (P3:1886-1906), whose machine reads the request as one framed record of framed
fields (`c3Input R = (c3Fields R).flatMap frame`, on its tape `0` framed once more). Per call, the fields other than
the expression are fixed; per child, the expression `V` is the enumeration's raw `exprWord V` (JLink's `sampEnum_run`
leaves it overlaid on its output tape, so any tail may follow). **`AsmStage`**: from `frame PRE`, `frame POST` (the
fixed fields before and after the expression, each already `flatMap frame`-ed) and `exprWord V ++ tail`, the output
port ends as `frame (PRE ++ frame (exprWord V) ++ POST)`, the two field ports unchanged, within `asmCost`.

**(6) The sample expansion.** "Fix the seed [...] The sample positions are `S_j = π(f(λ_j))`" (`samp:seed`,
P3:2932-2937), printed in the final pass's format (`sampleWord`, P3:3044-3053). **`SampStage`**: from the seed bits
`s` (framed, bit `0` first), `1^{kh}`, `1^Q`, `1^ℓ` and the modulus word `frame (binary ℓ p)` (PA's `modulus_step`),
the output port ends as `sampleWord kh` of the positions `posC P (bitsNum s) j`, `j < Q`, within `sampCost`.

Both are one fixed machine each, from blank scratch with every head at `0` to every head at `0` (the consumer pads
the enclosing stage with `Step.pad` to rerun it on scrubbed tapes).

Paper quantities of the main types: the compiler's input `frame (PRE ++ frame (exprWord V) ++ POST)` and the sample
positions `posC P (bitsNum s)`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Iface
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (exprWord)

/-! ## (2) The compiler's input assembler -/

/-- The assembler's step bound: linear in the words it reads. -/
def asmCost (PRE POST : List Bool) (V : List (ℤ × List (List (List ℕ)))) : ℕ :=
  4096 * (PRE.length + POST.length + (exprWord V).length + 1)

/-- The assembler's entry bank: `frame PRE`, `frame POST`, `exprWord V ++ tail` on the three input ports, every other
tape (the output and the scratch) blank. -/
def asmIn {t : ℕ} (pA pB pE : Fin t) (PRE POST : List Bool) (V : List (ℤ × List (List (List ℕ))))
    (tail : List Bool) : Fin t → List Bool :=
  fun i => if i = pA then frame PRE else if i = pB then frame POST else if i = pE then exprWord V ++ tail else []

/-- **The compiler's input assembler** (built by C6). -/
structure AsmStage where
  t : ℕ
  s : ℕ
  M : Machine t s
  pA : Fin t
  pB : Fin t
  pE : Fin t
  pO : Fin t
  hAB : pA ≠ pB
  hAE : pA ≠ pE
  hAO : pA ≠ pO
  hBE : pB ≠ pE
  hBO : pB ≠ pO
  hEO : pE ≠ pO
  run : ∀ (PRE POST : List Bool) (V : List (ℤ × List (List (List ℕ)))) (tail : List Bool),
    ∃ A' : Fin t → List Bool,
      Step M (asmCost PRE POST V) (fun _ => 0) (asmIn pA pB pE PRE POST V tail) (fun _ => 0) A' ∧
      A' pO = frame (PRE ++ frame (exprWord V) ++ POST) ∧ A' pA = frame PRE ∧ A' pB = frame POST

/-! ## (6) The sample expansion -/

/-- The sample pairs of a seed: `posC P seed j` as `(row, column)` for `j < Q`, the pairs `seedWord` prints. -/
def seedPairs (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) : List (ℕ × ℕ) :=
  List.ofFn fun j : Fin P.Q =>
    ((SeedFix.posC P (SeedFix.bitsNum _ s) j).1.val, (SeedFix.posC P (SeedFix.bitsNum _ s) j).2.val)

/-- The expansion's step bound: `Q` samples, each a degree-`7` evaluation in `GF(2^ℓ)`. -/
def sampCost (P : Sampler.SeedParams) : ℕ := 1048576 * (P.Q + 1) * (P.ell + 1) ^ 4

/-- The expansion's entry bank: the framed seed bits (bit `0` first), `1^{kh}`, `1^Q`, `1^ℓ`, the modulus word; every
other tape blank. -/
def sampIn {t : ℕ} (pS pK pQ pL pM : Fin t) (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) :
    Fin t → List Bool :=
  fun i => if i = pS then frame (List.ofFn s) else if i = pK then List.replicate P.kh true
    else if i = pQ then List.replicate P.Q true else if i = pL then List.replicate P.ell true
    else if i = pM then frame (binary P.ell P.modulus) else []

/-- **The sample expansion** (built by C6). -/
structure SampStage where
  t : ℕ
  s : ℕ
  M : Machine t s
  pS : Fin t
  pK : Fin t
  pQ : Fin t
  pL : Fin t
  pM : Fin t
  pO : Fin t
  distinct : [pS, pK, pQ, pL, pM, pO].Nodup
  run : ∀ (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool), ∃ A' : Fin t → List Bool,
    Step M (sampCost P) (fun _ => 0) (sampIn pS pK pQ pL pM P s) (fun _ => 0) A' ∧
      A' pO = FinalPass.Sample.sampleWord P.kh (seedPairs P s)

end NearCubicWires.WireExponent3_5.PrimT.C4Iface
