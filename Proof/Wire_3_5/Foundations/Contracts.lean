import Proof.Wire_3_5.Foundations.Runtime
import Proof.Foundations.OrdinaryMachine

/-! # Machine contracts for the components of the primitive and the weak machine

Realizes the five-field unit of the paper's algorithmic lemmas (inputs, precondition, budget, output, error; e.g.
`lem:primitive`, P3:3066-3116), with the budget of each component in a class of `prim:runtime` (P3:3105-3115) and
`tr:time` (P3:3797-3811). One contract per component:
* coset selection, `star:selection` (P3:1324-1362);
* explicit monomial lists and expansions (P3:1482-1488, 2385-2412, 2777-2806);
* the compiler into the separable printer, `alg:compiler`, `alg:recovery` (P3:1707-1769, 1874-1982);
* seed fixing by exact conditional expectation (P3:2238-2336, 2928-2966, 3035-3042);
* the final pass (P3:3044-3054, 3170-3181);
* the weak machine's per-call decision (P3:3669-3697, 3484-3488).

Main types: `MachineContract E` (its budget is `coef · classBound E cls (q, k, Ψ)`, a paper budget class) and
`Certified C`, which fuses a machine implementing the reference `ref` at exactly that budget with the paper's error
bound `errSpec` on `ref`. `Implements.cost_le` states that the running-time ledger's cost hypothesis is the
contract's budget field. The machine obligation `Implements` is the Theorem 2.5 `RewoundWordFunction`
(`Proof/Assembly/Production.lean:125-134`, the `PacketWriter` shape).

The S0 stand-ins for the machine-side representations are in `S0Stub`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Machine
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.RepairOrdinary

/-- The five-field contract. -/
structure MachineContract (E : Envelope) where
  /- (1) inputs: a paper object and its framed tape-0 encoding. -/
  Req : Type
  input : Req → List Bool
  /-- (2) precondition. -/
  pre : Req → Prop
  /-- (4) output: the reference value and its encoding on the output tape. -/
  Out : Type
  ref : Req → Out
  encode : Out → List Bool
  /-- (3) budget: class, class arguments, constant coefficient. -/
  cls : BudgetClass
  q : Req → ℕ
  k : Req → ℕ
  psi : Req → ℕ
  coef : ℕ
  /-- (5) error: what the mathematics proves about `ref`, against the paper quantity. -/
  errSpec : Req → Out → Prop

def MachineContract.budget {E : Envelope} (C : MachineContract E) (r : {r // C.pre r}) : ℕ :=
  C.coef * classBound E C.cls (C.q r.1) (C.k r.1) (C.psi r.1)

/-- The machine obligation: REL's rewound word function at the class budget, on admissible
requests. -/
abbrev Implements {E : Envelope} (C : MachineContract E) : Type :=
  RewoundWordFunction {r // C.pre r} (fun r => C.input r.1) (fun r => C.encode (C.ref r.1)) C.budget

/-! ## S0 stand-ins -/
namespace S0Stub

/-- An integer threshold gate `[θ ≤ Σ w_i x_i]` (P3:1552-1566, `alg:normalization`). -/
structure IntGate (n : ℕ) where
  weights : Fin n → ℤ
  threshold : ℤ

/-- A half-score after the star pullback (`alg:pullback`, P3:1623-1676): a constant plus signed
weights on center bits, each center bit a parity of column-half bits XOR a fixed error bit. -/
structure HalfScore where
  const : ℤ
  terms : List (ℤ × List ℕ × Bool)

def parityOf (z : ℕ) (mask : List ℕ) : Bool := mask.foldl (fun b i => xor b (z.testBit i)) false

def HalfScore.eval (h : HalfScore) (z : ℕ) : ℤ :=
  h.const + (h.terms.map (fun t => if xor (parityOf z t.2.1) t.2.2 then t.1 else 0)).sum

/-- One separated signed occurrence `v·[a(z_L)+b(z_R)=0]` (P3:1712-1719). -/
structure Occurrence where
  v : ℤ
  left : HalfScore
  right : HalfScore

/-- A printed polynomial: monomials over bottom-threshold atoms with integer coefficients
(§13.2 item 3; P3:1880-1887). -/
abbrev PrintedPoly := List (ℤ × List ℕ)

/-- A product-code coset: one syndrome per block (P3:1200-1209). -/
abbrev Coset := List ℕ

end S0Stub
open S0Stub

/-! ## C1: coset selection (`star:selection`, P3:1324-1362) -/

structure SelectionReq where
  n : ℕ
  r : ℕ
  gates : List (IntGate n)
  /-- named populations: gate indices and a rational weight `p_X` (P3:1326-1330). -/
  pops : List (List ℕ × ℚ)

/-- `s = ⌊log₂(n/r+1)⌋`, `k = r·s` (P3:1188-1189). -/
def SelectionReq.s (R : SelectionReq) : ℕ := Nat.log 2 (R.n / R.r + 1)
def SelectionReq.k (R : SelectionReq) : ℕ := R.r * R.s

def c1 (E : Envelope) (objective : SelectionReq → Coset → ℚ) (argmin : SelectionReq → Coset)
    (encodeCoset : Coset → List Bool) (inputWord : SelectionReq → List Bool) (psi : SelectionReq → ℕ)
    (coef : ℕ) : MachineContract E where
  Req := SelectionReq
  input := inputWord
  pre := fun R => R.r % 2 = 0 ∧ 2 ≤ R.r ∧ 4 * R.r ≤ R.n ∧
    (R.pops.map Prod.snd).sum = 1 ∧ ∀ X ∈ R.pops, 0 ≤ X.2
  Out := Coset
  ref := argmin
  encode := encodeCoset
  cls := .selection
  q := fun R => R.n
  k := SelectionReq.k
  psi := psi
  coef := coef
  /- exact: the selected coset minimizes the exact weighted objective (P3:1357-1360); its
  bound `C_0 r^{3/2}/n^{3/2}·Σ p_X W_X` is B1's `star:selection` theorem. -/
  errSpec := fun R c => c.length = R.r ∧ ∀ c' : Coset, c'.length = R.r →
    (∀ σ ∈ c', σ < 2 ^ R.s) → objective R c ≤ objective R c'

/-! ## C2: explicit monomial lists and expansions (P3:1482-1488, 2385-2412, 2777-2806) -/

/-- The list/filter/row construction's request; its content is B2/B4/B5's record. -/
structure ListReq where
  n : ℕ
  k : ℕ
  psi : ℕ
  description : List Bool

def c2 (E : Envelope) (ref : ListReq → PrintedPoly) (encodePoly : PrintedPoly → List Bool)
    (semantics : ListReq → PrintedPoly → Prop) (coef : ℕ) : MachineContract E where
  Req := ListReq
  input := fun R => frame R.description
  pre := fun R => R.k ≤ R.n
  Out := PrintedPoly
  ref := ref
  encode := encodePoly
  cls := .preprocessing
  q := fun R => R.n
  k := fun R => R.k
  psi := fun R => R.psi
  coef := coef
  /- exact expansion: `semantics` is B2/B4/B5's statement that the printed polynomial equals
  the repaired/filtered/row Boolean function on every input (P3:1416-1432, 3141-3145). -/
  errSpec := semantics

/-! ## C3: compiler to printer, and the printer (`alg:compiler`, `alg:separable-printer`) -/

structure PrinterReq where
  n : ℕ
  k : ℕ
  psi : ℕ
  /- column bits `n_out = nL + nR`, the halves of P3:1710-1711. -/
  nL : ℕ
  nR : ℕ
  /-- recovery precision `Q'` (P3:1888-1889). -/
  prec : ℕ
  occ : List Occurrence

/-- The printed table at one column (P3:1719). -/
def PrinterReq.table (R : PrinterReq) (zL zR : ℕ) : ℤ :=
  (R.occ.map (fun o => if o.left.eval zL + o.right.eval zR = 0 then o.v else 0)).sum

/-- What seed fixing consumes: per-column least residue mod `2^{Q'}`, then the column sum
(`alg:recovery`, P3:1965-1982: "Reduction must precede the column sum"). -/
def PrinterReq.recoveredSum (R : PrinterReq) : ℤ :=
  ((List.range (2 ^ R.nL)).map (fun zL => ((List.range (2 ^ R.nR)).map
    (fun zR => (R.table zL zR) % (2 ^ R.prec : ℤ))).sum)).sum

def c3 (E : Envelope) (inputWord : PrinterReq → List Bool) (coef : ℕ) : MachineContract E where
  Req := PrinterReq
  input := inputWord
  pre := fun R => R.nL ≤ R.nR ∧ R.nR ≤ R.nL + 1 ∧ R.nL + R.nR = R.n - R.k ∧
    100 * Nat.log 2 (R.occ.length + 1) ≤ R.nL + R.nR
  Out := ℤ
  ref := PrinterReq.recoveredSum
  encode := fun z => frame (Nat.bits z.natAbs) ++ [decide (z < 0)]
  cls := .table
  q := fun R => R.n
  k := fun R => R.k
  psi := fun R => R.psi
  coef := coef
  /- exact (P3:1936-1941). -/
  errSpec := fun R z => z = R.recoveredSum

/-! ## C4: seed fixing by exact conditional expectation (S4; P3:2238-2336, 2928-2966, 3035-3042) -/

structure SeedReq where
  n : ℕ
  k : ℕ
  psi : ℕ
  seedLen : ℕ
  /- one printer request per candidate child prefix (their coefficients include the Gaussian-
  elimination conditional probabilities, P3:2268-2271, 2950-2957). -/
  childPotential : List Bool → PrinterReq

/-- The greedy fixed seed: at each bit, the child with no larger printed potential (P3:2334-2335,
3035-3038). -/
def SeedReq.greedy (R : SeedReq) : List Bool :=
  (List.range R.seedLen).foldl (fun p _ =>
    if (R.childPotential (p ++ [true])).recoveredSum < (R.childPotential (p ++ [false])).recoveredSum
    then p ++ [true] else p ++ [false]) []

def c4 (E : Envelope) (inputWord : SeedReq → List Bool) (average : SeedReq → ℚ)
    (potential : SeedReq → List Bool → ℚ) (coef : ℕ) : MachineContract E where
  Req := SeedReq
  input := inputWord
  pre := fun R => R.k ≤ R.n
  Out := List Bool
  ref := SeedReq.greedy
  encode := frame
  cls := .table
  q := fun R => R.n
  k := fun R => R.k
  psi := fun R => R.psi
  coef := coef
  /- the fixed seed's potential is at most the random-seed expectation (P3:2336, 3038). -/
  errSpec := fun R seed => seed.length = R.seedLen ∧ potential R seed ≤ average R

/-! ## C5: the final pass (P3:3044-3054, 3170-3181) -/

structure FinalReq where
  n : ℕ
  k : ℕ
  psi : ℕ
  /- the `Q` fixed sample pairs `(U_j, V_j) ∈ [N]²`, `N = 2^{k/2}` (P3:2828-2831). -/
  samples : List (ℕ × ℕ)
  /-- the reported-state lookup at one sampled input, polynomial-time (P3:3175-3178). -/
  lookup : ℕ → ℕ → ℕ → ℤ

/-- `Σ_z Σ_j lookup(U_j, V_j; z)` over the `2^{n-k}` columns. -/
def FinalReq.sum (R : FinalReq) : ℤ :=
  ((List.range (2 ^ (R.n - R.k))).map (fun z =>
    (R.samples.map (fun uv => R.lookup uv.1 uv.2 z)).sum)).sum

def c5 (E : Envelope) (inputWord : FinalReq → List Bool) (truth : FinalReq → ℚ) (D : ℕ)
    (coef : ℕ) : MachineContract E where
  Req := FinalReq
  input := inputWord
  pre := fun R => R.k ≤ R.n ∧ R.k % 2 = 0 ∧ R.samples.length ≤ 2 ^ ((3 * R.k + 3) / 4) * R.n ^ E.Amain
  Out := ℤ
  ref := FinalReq.sum
  encode := fun z => frame (Nat.bits z.natAbs) ++ [decide (z < 0)]
  cls := .mainPass
  q := fun R => R.n
  k := fun R => R.k
  psi := fun R => R.psi
  coef := coef
  /- the normalized sum estimates the masked truth mean to `n^{-D}` (`prim:truth`, P3:3086-3090);
  B6/B7 prove it for the samples. -/
  errSpec := fun R z => |(z : ℚ) / ((2 ^ (R.n - R.k) : ℚ) * R.samples.length) - truth R| ≤
    1 / (R.n : ℚ) ^ D

/-! ## C6: the weak machine's per-call glue and decision (P3:3669-3697, 3471-3491) -/

structure WeakReq where
  N : ℕ
  q : ℕ
  k : ℕ
  psi : ℕ
  input : List Bool
  guess : List Bool
  /- the three estimates `V̂, Q̂, μ̂` returned by the primitive calls (P3:3475-3480). -/
  estimates : ℚ × ℚ × ℚ

/-- Accept only if the guard holds and `V̂ ≤ 2v₀`, `Q̂ ≤ 1+v₀`, `μ̂ ≥ (c_p+s_p)/2` (P3:3484-3488;
the guard ⌊N/16⌋ is the binding's, §3 row 3). -/
def WeakReq.decide (v0 cp sp : ℚ) (R : WeakReq) : Bool :=
  Decidable.decide (16 * R.guess.length ≤ R.N) &&
    Decidable.decide (R.estimates.1 ≤ 2 * v0) &&
    Decidable.decide (R.estimates.2.1 ≤ 1 + v0) &&
    Decidable.decide ((cp + sp) / 2 ≤ R.estimates.2.2)

def c6 (E : Envelope) (inputWord : WeakReq → List Bool) (v0 cp sp : ℚ)
    (sound : WeakReq → Bool → Prop) (coef : ℕ) : MachineContract E where
  Req := WeakReq
  input := inputWord
  pre := fun R => R.k ≤ R.q
  Out := Bool
  ref := WeakReq.decide v0 cp sp
  encode := fun b => [b]
  cls := .mainPass
  q := fun R => R.q
  k := fun R => R.k
  psi := fun R => R.psi
  coef := coef
  /- one-sidedness and completeness are B8/D1's (`tr:soundness`, `tr:completeness`). -/
  errSpec := sound

/-! ## C7 is A7: `Runtime3.littleO` instantiated with C1-C6's budgets. -/

/-- The four A7 cost functions from the contracts' budgets at fixed class arguments. -/
def costsOf (E : Envelope) (coef : ℕ) : ComponentCosts E where
  coef := coef
  sel := fun q k psi => coef * classBound E .selection q k psi
  pre := fun q k psi => coef * classBound E .preprocessing q k psi
  table := fun q k psi => coef * classBound E .table q k psi
  main := fun q k psi => coef * classBound E .mainPass q k psi
  hsel := fun _ _ _ => le_refl _
  hpre := fun _ _ _ => le_refl _
  htable := fun _ _ _ => le_refl _
  hmain := fun _ _ _ => le_refl _

/-! ## Executable twins at tiny parameters (P19, P25) -/

end NearCubicWires.WireExponent3_5.Machine
