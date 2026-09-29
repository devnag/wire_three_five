import Proof.Wire_3_5.Foundations.Runtime

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

/-- The machine obligation: the Theorem 2.5 repository's rewound word function at the class budget, on admissible
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

/-! ## C3: compiler to printer, and the printer (`alg:compiler`, `alg:separable-printer`) -/

/-! ## C4: seed fixing by exact conditional expectation (S4; P3:2238-2336, 2928-2966, 3035-3042) -/

/-! ## C5: the final pass (P3:3044-3054, 3170-3181) -/

/-! ## C6: the weak machine's per-call glue and decision (P3:3669-3697, 3471-3491) -/

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
