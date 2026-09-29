import Proof.PCP.PCPPSubstitutionRequest
import Proof.Wire_3_5.Stars.StarSelectionChoice
import Proof.Wire_3_5.Transfer.TransferSeedCalls

/-! # The union weak machine's acceptance condition on a guess (P3:3669-3697)

Realizes, as definitions, the union weak machine of `tr:machine` (P3:3669-3691): "The weak machine guesses one
size-`q^G` general oracle, a class tag, and one sparse grid sum for each distinct PCPP variable. It rejects malformed
descriptions, oversized atoms, and coefficients outside the fixed grid. Systematic parities are constructed from the
PCPP output. It then selects the common star translation, constructs the shared coordinate filters, and performs
(tr:tests). Every guess has `q^{O(1)} = o(N)` bits [...] At the finitely many source lengths where this fixed envelope
exceeds the refuter's `N/10` guess budget, the machine rejects outright". Its PCPP is the pointwise PCPP of the outer
verifier with the guessed oracle substituted: "Substituting a guessed size-`q^G` general oracle now gives a circuit
`H`" (P3:3651-3653), built exactly as in the Theorem 2.5 Case-2 donor (`PCPPSubstitution.sourceRequest` of the outer
projection PCP's query addresses and decision formula).

* `UnionSetup I`: everything fixed before the machine is presented to the refuter (P3:3693-3697): the hierarchy
  language and the outer projection PCP (CLW L3.10) deciding it, with its soundness on no-instances ("soundness at
  most `N^{−10}` against every oracle on a no-instance", P3:3257-3259), the pointwise PCPP (CLW L3.11), the oracle
  exponent `G`, the masked verifier's constants (`tr:thresholds`), the run-time numerals `Λ̄(q)`, `s(q)` of the grid,
  and the constant and encoding-parity atoms of each class mode, with their semantics (P3:3092-3094).
* `UnionGuess S z`: one guess at the input `z`: the oracle, the class tag, and per PCPP variable `s(q)` grid signs
  `σ ∈ {−1,0,1}` and atoms (circuits of the mode).
* Derived, as the machine computes them: the systematic parity atoms, the carrier of each variable (the charged gates
  of its atoms, and of its parity if systematic, P3:3409-3410, 3432-3433), the incidence weights `p_X`
  (P3:3395-3399), the common translation `selectCodes` of `star:selection` (P3:1360, 3413-3419), the atom forms
  `S_X = (Λ̄/s)Σ_a σ_a C_{X,a}`, the constant and the parity, the primitive calls on four-atom tuples (`tupleRequest`, one carrier for `V`/`Q` terms, two for `μ` terms), and the estimates `V̂, Q̂, μ̂` formed from the
  fused primitive's printed values `P.value` (`Poly4.estimate`).
* **`UnionAccepts S P z g`**: the guess passes every check: oracle size `≤ q^G` (`oracleSizeBound`), grid signs, the
  guess word within `⌊N/16⌋` bits, every call with a nonzero coefficient admissible (`I.Call`: gates in the named
  carriers, envelopes, translation, star and fit conditions), and `tr:thresholds` at the estimates.
* **`CompleteFor S P M`** (every accepting guess makes `M` accept) and **`SoundFor S P M`** (`M` accepts only through
  an accepting guess): the union leaf's contract, with `tr:time`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.Shared (uMean bitR)
open NearCubicWires.RepairOrdinary.PCPPSubstitution (sourceRequest)
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)
open NearCubicWires.ComponentwiseBranchExtraction (systematicConstraint)

/-- The PCPP request of the outer verifier at `z` with the oracle substituted (P3:3651-3653; the Case-2 donor's
`PCPPSubstitution.sourceRequest`). -/
def unionRequest {M : TimedDecisionMachine} {T : ℕ → ℕ} (pcp : ProjectionPCP M T) (a : PointwisePCPPAlgorithm)
    {N : ℕ} (z : BitInput N) (oracle : BooleanCircuit (pcp.nativeWidth N)) : PCPPRequest a.minimumArity :=
  sourceRequest a oracle (pcp.queryAddressBits z) (pcp.decision z (fun _ => false))

section Union
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- Everything the union machine fixes before it is presented to the refuter (P3:3693-3697). -/
structure UnionSetup (I : PrimitiveInputs B) where
  /-- the hierarchy language and the time-bounded computation deciding it -/
  language : Language
  machine : TimedDecisionMachine
  clock : ℕ → ℕ
  decides : ∀ N (z : BitInput N), language N z = machine.accepts N z
  /-- the outer projection PCP (CLW L3.10) -/
  pcp : ProjectionPCP machine clock
  /-- the pointwise PCPP (CLW L3.11) -/
  pcppAlg : PointwisePCPPAlgorithm
  /-- outer soundness with any substituted oracle: on a no-instance the substituted circuit accepts at most
  `N^{−10}` of its random inputs (P3:3257-3259, 3544) -/
  outerSound : ∀ N, 1 ≤ N → ∀ (z : BitInput N), machine.accepts N z = false →
    ∀ oracle : BooleanCircuit (pcp.nativeWidth N),
      uMean (fun x : BitInput (unionRequest pcp pcppAlg z oracle).arity =>
        bitR ((unionRequest pcp pcppAlg z oracle).circuit.eval x)) ≤ 1 / (N : ℝ) ^ 10
  /-- the oracle size exponent: oracles of size at most `oracleSizeBound G q` (P3:3669) -/
  G : ℕ
  /-- the masked verifier's constants (`tr:thresholds`, P3:3485-3491) -/
  params : MaskedSoundnessParameters pcppAlg.completeness pcppAlg.soundness
  /-- the grid `Λ̄(q)/s(q)·{−1,0,1}` (run-time numerals, P3:3399-3403, 3693-3697) -/
  gridMass : ℕ → ℚ
  gridMass_nonneg : ∀ q, 0 ≤ gridMass q
  gridSize : ℕ → ℕ
  /-- the constant atom of each class mode (P3:3092-3094) -/
  constAtom : (m : Mode) → (n : ℕ) → m.Circuit n
  constAtom_eval : ∀ (m : Mode) (n : ℕ) (x : BitInput n), m.eval (constAtom m n) x = true
  /-- a constant charges no gates (no wires, P3:209-216) -/
  constAtom_gates : ∀ (m : Mode) (n : ℕ), m.gates (constAtom m n) = []
  /-- the systematic encoding parity of each class mode (P3:3092-3094, 3409-3410) -/
  parityAtom : (m : Mode) → (n : ℕ) → Finset (Fin n) → m.Circuit n
  parityAtom_eval : ∀ (m : Mode) (n : ℕ) (S : Finset (Fin n)) (x : BitInput n),
    m.eval (parityAtom m n S) x = parityOn S x

variable {I : PrimitiveInputs B}

namespace UnionSetup
variable (S : UnionSetup I) {N : ℕ} (z : BitInput N)

/-- The PCPP request at `z` for an oracle. -/
def request (oracle : BooleanCircuit (S.pcp.nativeWidth N)) : PCPPRequest S.pcppAlg.minimumArity :=
  unionRequest S.pcp S.pcppAlg z oracle

/-- The pointwise PCPP of the substituted circuit (CLW L3.11). -/
def pcppOf (oracle : BooleanCircuit (S.pcp.nativeWidth N)) : PointwisePCPP (S.request z oracle).circuit :=
  S.pcppAlg.output (S.request z oracle)

end UnionSetup

/-- One guess of the union machine at the input `z` (P3:3669-3671): the oracle, the class tag, and one sparse grid
sum per PCPP variable (its signs and atoms). -/
structure UnionGuess (S : UnionSetup I) {N : ℕ} (z : BitInput N) where
  oracle : BooleanCircuit (S.pcp.nativeWidth N)
  mode : Mode
  sign : PcppVar (S.pcppOf z oracle) → Fin (S.gridSize (S.request z oracle).arity) → ℤ
  atom : PcppVar (S.pcppOf z oracle) → Fin (S.gridSize (S.request z oracle).arity) →
    mode.Circuit (S.request z oracle).arity

namespace UnionGuess
variable {S : UnionSetup I} {N : ℕ} {z : BitInput N} (g : UnionGuess S z)

/-- The circuits' input arity `q` (the PCPP input: the outer randomness, padded to the PCPP's minimum arity). -/
abbrev q : ℕ := (S.request z g.oracle).arity

/-- The PCPP of the guess's oracle. -/
abbrev pcpp : PointwisePCPP (S.request z g.oracle).circuit := S.pcppOf z g.oracle

/-- The grid size `s(q)`. -/
abbrev s : ℕ := S.gridSize g.q

/-- Whether a variable is systematic (its bit is an encoding parity). -/
def sysBit (X : PcppVar g.pcpp) : Bool := decide (X.val < g.pcpp.systematicBits)

/-- The encoding support of a systematic variable (empty otherwise). -/
def support (X : PcppVar g.pcpp) : Finset (Fin g.q) :=
  if h : X.val < g.pcpp.systematicBits then g.pcpp.systematicSupport ⟨X.val, h⟩ else ∅

/-- The encoding parity of a variable, constructed from the PCPP output (P3:3672). -/
def parity (X : PcppVar g.pcpp) : g.mode.Circuit g.q := S.parityAtom g.mode g.q (g.support X)

/-- The carrier of a variable: the charged gates of its atoms, and of its encoding parity if systematic
(P3:3409-3410, 3432-3433). -/
def carrier (X : PcppVar g.pcpp) : Stars.Carrier g.q :=
  (List.ofFn fun a => g.mode.gates (g.atom X a)).flatten ++ (if g.sysBit X then g.mode.gates (g.parity X) else [])

/-- The incidence weight `p_X = #{(i,j) : X(i,j) = X}/2M` (P3:3395-3399). -/
noncomputable def weight (X : PcppVar g.pcpp) : ℚ :=
  ((Finset.univ.filter fun p : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 => posVar g.pcpp p.1 p.2 = X).card : ℚ) /
    (2 * 2 ^ g.pcpp.clauseBits)

/-- The weighted carriers handed to `star:selection`. -/
noncomputable def pops : List (ℚ × Stars.Carrier g.q) :=
  (List.finRange (g.pcpp.systematicBits + g.pcpp.auxiliaryBits)).map fun X => (g.weight X, g.carrier X)

open Classical in
/-- The common star translation: the first minimizer of `star:selection`'s exact objective (P3:1360, 3413-3419). -/
noncomputable def translation : List ℕ :=
  if h : I.StarAt g.q then (I.starParams g.q h).selectCodes g.pops else []

/-- The atoms of the calls: the constant, the grid atoms `C_{X,a}`, and the encoding parities. -/
abbrev AtomIx : Type := Unit ⊕ (PcppVar g.pcpp × Fin g.s) ⊕ PcppVar g.pcpp

/-- The circuit of each atom. -/
def circ : g.AtomIx → g.mode.Circuit g.q
  | Sum.inl _ => S.constAtom g.mode g.q
  | Sum.inr (Sum.inl (X, a)) => g.atom X a
  | Sum.inr (Sum.inr X) => g.parity X

/-- The grid sum `S_X = (Λ̄/s)Σ_a σ_{X,a} C_{X,a}` as a linear form in the atoms. -/
noncomputable def wS (X : PcppVar g.pcpp) : g.AtomIx → ℝ
  | Sum.inr (Sum.inl p) => if p.1 = X then ((S.gridMass g.q : ℝ) / g.s) * (g.sign p.1 p.2 : ℝ) else 0
  | _ => 0

/-- The constant `1` as a linear form. -/
def wOne : g.AtomIx → ℝ
  | Sum.inl _ => 1
  | _ => 0

/-- The encoding parity `E_X` as a linear form. -/
def wE (X : PcppVar g.pcpp) : g.AtomIx → ℝ
  | Sum.inr (Sum.inr Y) => if Y = X then 1 else 0
  | _ => 0

/-- The call for a `V`/`Q` term at a position (one named carrier). -/
noncomputable def vCall (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (t : Fin 4 → g.AtomIx) : PrimRequest :=
  tupleRequest g.mode g.q g.circ t [g.carrier (posVar g.pcpp pos.1 pos.2)] g.translation

/-- The call for a `μ` term of a clause (the two named carriers). -/
noncomputable def muCall (i : Fin (2 ^ g.pcpp.clauseBits)) (t : Fin 4 → g.AtomIx) : PrimRequest :=
  tupleRequest g.mode g.q g.circ t [g.carrier (posVar g.pcpp i 0), g.carrier (posVar g.pcpp i 1)] g.translation

/-- The validity polynomial at a position. -/
noncomputable def polyVAt (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) : Poly4 g.AtomIx :=
  polyV (g.sysBit (posVar g.pcpp pos.1 pos.2)) (g.wS (posVar g.pcpp pos.1 pos.2)) g.wOne
    (g.wE (posVar g.pcpp pos.1 pos.2))

/-- The second-moment polynomial at a position. -/
noncomputable def polyQAt (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) : Poly4 g.AtomIx :=
  polyQ (g.wS (posVar g.pcpp pos.1 pos.2)) g.wOne

/-- The clause polynomial of a clause. -/
noncomputable def polyMuAt (i : Fin (2 ^ g.pcpp.clauseBits)) : Poly4 g.AtomIx :=
  polyMu (posNeg g.pcpp i 0) (posNeg g.pcpp i 1) (g.wS (posVar g.pcpp i 0)) (g.wS (posVar g.pcpp i 1)) g.wOne

variable (P : FusedPrimitive I)

/-- The machine's `V̂`, from the primitive's printed values. -/
noncomputable def Vhat : ℝ :=
  uMean fun pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 =>
    (g.polyVAt pos).estimate (fun _ t => (P.value (g.vCall pos t) : ℝ))

/-- The machine's `Q̂`. -/
noncomputable def Qhat : ℝ :=
  uMean fun pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 =>
    (g.polyQAt pos).estimate (fun _ t => (P.value (g.vCall pos t) : ℝ))

/-- The machine's `μ̂`. -/
noncomputable def μhat : ℝ :=
  uMean fun i : Fin (2 ^ g.pcpp.clauseBits) =>
    (g.polyMuAt i).estimate (fun _ t => (P.value (g.muCall i t) : ℝ))

/-- The guess as a word: the class tag, the oracle's code, and per variable its signs and atom codes. -/
def word : List Bool :=
  [(match g.mode with | Mode.thr => true | Mode.sym => false)] ++ natWord (ExecutableInterfaces.encodeBooleanCircuit g.oracle) ++
    (List.ofFn fun X : PcppVar g.pcpp =>
      (List.ofFn fun a : Fin g.s => intWord (g.sign X a) ++ natWord (g.mode.code (g.atom X a))).flatten).flatten

end UnionGuess

/-- **The union machine accepts on the guess** (P3:3669-3691, 3485-3489): the oracle has size at most `q^G`, the
coefficients lie on the grid, the guess fits the refuter's `⌊N/16⌋` witness, every primitive call with a nonzero
coefficient is admissible, and the estimates pass `tr:thresholds`. -/
def UnionAccepts (S : UnionSetup I) (P : FusedPrimitive I) {N : ℕ} (z : BitInput N) (g : UnionGuess S z) : Prop :=
  g.oracle.size ≤ oracleSizeBound S.G (S.pcp.nativeWidth N) ∧
  (∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ)) ∧
  g.word.length ≤ N / 16 ∧
  (∀ pos j t, (g.polyVAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t)) ∧
  (∀ pos j t, (g.polyQAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t)) ∧
  (∀ i j t, (g.polyMuAt i).coeff j t ≠ 0 → I.Call (g.muCall i t)) ∧
  g.Vhat P ≤ 2 * (S.params.v0 : ℝ) ∧ g.Qhat P ≤ 1 + (S.params.v0 : ℝ) ∧ (S.params.threshold : ℝ) ≤ g.μhat P

end Union

end NearCubicWires.WireExponent3_5.Transfer
