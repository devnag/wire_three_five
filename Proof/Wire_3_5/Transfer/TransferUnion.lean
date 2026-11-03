import Lean
import W3.Joins.Cases
import Proof.Wire_3_5.Front35.Pair
import Outer.Apply
import Proof.Wire_3_5.Transfer.TransferSeedCalls
import Proof.Wire_3_5.Stars.StarSelectionChoice
import Proof.PCP.PCPPSubstitutionRequest
import Proof.Foundations.RecoveryScheduleEnvelope




/-! # The union weak machine's acceptance condition on a guess (Lemma H.7; §H.5 "The machine")

Realizes, as definitions, the union weak machine of the outer step (paper v2, Lemma H.7 and its machine paragraph): "the
weak machine guesses a circuit Γ_src with q inputs and at most q^G gates … checks deterministically that
Γ_src(bin_a(i)0^{q−a})=z_i for every i<N … runs A_G on ⟨Γ_src⟩_a … guesses a second circuit Γ_pf … H_Γ(u)=
¬C^{O_{Γ_pf}}(u_1,…,u_{ℓ_out})", then the class tag and one sparse grid sum per PCPP variable, the masked tests and
the thresholds, as before. Its PCPP request is the pointwise PCPP request at `H_Γ` itself (`requestAt`, of arity
`q(N)`).

* `UnionSetup I`: everything fixed before the machine is presented to the refuter (order of the constants): the
  hierarchy language with its hierarchy `hier` at the clock `N^{kclk+2}`, the short PCP `mw` (§H.1 item 1), the
  succinct verifier `SV` of Lemma H.6 at the description length `λ_a = instLength lenG a`, the pointwise PCPP, the
  liveness flag `live` (the machine rejects outright off the recovered language), the onset of the length gate (past
  it: `SV`'s onset, the PCPP's minimum arity below `q(N)`, and the reserve `1/λ_a ≤ outerError` of Lemma H.3's proof),
  the oracle exponent `G`, the masked verifier's constants and the grid and atom data.
* `UnionGuess S z`: one guess at `z`: the pair `Γ = (Γ_src, Γ_pf)` on the width `q(N)` (`OuterGuess`), the class tag, and
  per PCPP variable `s(q)` grid signs and atoms.
* **`UnionAccepts S P z g`**: the guess passes every check, in the machine's order: `live`; `N = 2^a` and the onset
  `≤ a` (`a = ⌊log₂ N⌋`); both circuits of size `≤ oracleSizeBound G q`; the description-length guard
  `SrcFits lenG a Γ_src`; the source check `CheckAt a z Γ_src`; the grid signs; the guess word within `⌊N/16⌋` bits;
  every call with a nonzero coefficient admissible; and the thresholds at the estimates.
* **`outerSound`** (Lemma H.7(c)): past the onset, on a no-instance, for every pair passing the description-length
  guard and the source check, `H_Γ` accepts at most a `1/λ_a` fraction of its inputs; **`outerSound_reserve`** puts it
  below the masked verifier's `outerError`.
* **`CompleteFor S P M`** and **`SoundFor S P M`**: the union leaf's contract, with the time bound. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.Shared (uMean bitR)
open NearCubicWires.RepairOrdinary.PCPPSubstitution (sourceRequest)
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)
open NearCubicWires.ComponentwiseBranchExtraction (systematicConstraint)

open NearCubicGates.Close.Outer (OuterGuess SrcFits CheckAt instLength)

noncomputable section Union
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- Everything the union machine fixes before it is presented to the refuter (P3:3693-3697). -/
structure UnionSetup (I : PrimitiveInputs B) where
  /-- the hierarchy language and the hierarchy deciding it at the clock `N^{kclk+2}` -/
  language : Language
  hier : OrdinaryHierarchy (fun n => n ^ (kclk + 2))
  decides : ∀ N (z : BitInput N), language N z = true ↔ hier.verifier.language hier.time N z
  /-- the short PCP (§H.1 item 1) and the succinct verifier `𝒱_G` (Lemma H.6) at `λ_a = instLength lenG a` -/
  mw : NearCubicGates.Close.Outer.MWSource
  lenG : ℕ
  SV : NearCubicGates.Close.Outer.SuccinctVerifier hier lenG
  /-- the pointwise PCPP (§H.1 item 2) -/
  pcppAlg : PointwisePCPPAlgorithm
  /-- the machine runs only at the recovered language; elsewhere it rejects outright -/
  live : Bool
  /-- the oracle size exponent: circuits of size at most `oracleSizeBound G q` -/
  G : ℕ
  /-- the masked verifier's constants (`tr:thresholds`, P3:3485-3491) -/
  params : MaskedSoundnessParameters pcppAlg.completeness pcppAlg.soundness
  /-- the length gate's onset (in `a = log₂ N`): `𝒱_G`'s onset, the PCPP's minimum arity, and the reserve
  `1/λ_a ≤ outerError` (Lemma H.3's proof: "s_out(N)=1/λ_a ≤ (c_p−s_p)/8" for large `N`) -/
  onset : ℕ
  onset_sv : SV.onset ≤ onset
  onset_pos : 1 ≤ onset
  onset_arity : ∀ a, onset ≤ a → pcppAlg.minimumArity ≤ NearCubicGates.Close.Outer.width mw SV (2 ^ a)
  onset_reserve : ∀ a, onset ≤ a → 1 / (instLength lenG a : ℝ) ≤ (params.outerError : ℝ)
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

/-- The width `q(N)` (57). -/
abbrev width (N : ℕ) : ℕ := NearCubicGates.Close.Outer.width S.mw S.SV N

/-- The PCPP request at `H_Γ` for the pair `Γ` (`requestAt`: arity `q(N)` once `q(N)` reaches the PCPP's minimum
arity; `a = ⌊log₂ N⌋`). It does not depend on `z`; `z` fixes `N`. -/
noncomputable def request (_z : BitInput N) (B : OuterGuess (S.width N)) : PCPPRequest S.pcppAlg.minimumArity :=
  W3.NearCubicWires.RepairSource.Outer3.requestAt S.mw S.SV S.pcppAlg (Nat.log 2 N) B

/-- The pointwise PCPP of `H_Γ` (§H.1 item 2). -/
noncomputable def pcppOf (B : OuterGuess (S.width N)) : PointwisePCPP (S.request z B).circuit :=
  S.pcppAlg.output (S.request z B)

end UnionSetup

/-- The uniform mean of a circuit's acceptance indicator is its accepting fraction. -/
theorem uMean_bitR_card {n : ℕ} (c : BooleanCircuit n) :
    uMean (fun x : BitInput n => bitR (c.eval x)) =
      ((Finset.univ.filter fun x : BitInput n => c.eval x = true).card : ℝ) / 2 ^ n := by
  unfold uMean bitR
  rw [Finset.sum_boole]
  simp [BitInput]

namespace UnionSetup
variable (S : UnionSetup I)

/-- The hierarchy no-instance in the hierarchy's own terms. -/
theorem not_hier_of_no {N : ℕ} {z : BitInput N} (hno : S.language N z = false) :
    ¬ S.hier.verifier.language S.hier.time N z := fun h => by
  have := (S.decides N z).2 h
  rw [hno] at this
  exact Bool.false_ne_true this

/-- **`outerSound′`** (Lemma H.7(c)): at a source length `N = 2^a` past the onset, on a hierarchy no-instance, for
every pair whose source circuit passes the description-length guard and the source check, `H_Γ` accepts at most a
`1/λ_a` fraction of its `q(N)`-bit inputs. -/
theorem outerSound {N : ℕ} (z : BitInput N) (B : OuterGuess (S.width N))
    (hN : N = 2 ^ Nat.log 2 N) (hon : S.onset ≤ Nat.log 2 N) (hno : S.language N z = false)
    (hfit : SrcFits S.lenG (Nat.log 2 N) B.src) (hcheck : CheckAt (Nat.log 2 N) z B.src) :
    uMean (fun x : BitInput (S.request z B).arity => bitR ((S.request z B).circuit.eval x)) ≤
      1 / (instLength S.lenG (Nat.log 2 N) : ℝ) := by
  have hq : S.pcppAlg.minimumArity ≤ NearCubicGates.Close.Outer.width S.mw S.SV N := by
    have h := S.onset_arity (Nat.log 2 N) hon
    rwa [← hN] at h
  have hreq : S.request z B =
      W3.NearCubicWires.RepairSource.Outer3.requestOf S.mw S.SV S.pcppAlg (Nat.log 2 N) B hq :=
    W3.NearCubicWires.RepairSource.Outer3.requestAt_of S.mw S.SV S.pcppAlg (Nat.log 2 N) B hq
  rw [hreq, uMean_bitR_card]
  have hs : ((Finset.univ.filter fun x =>
      (W3.NearCubicWires.RepairSource.Outer3.requestOf S.mw S.SV S.pcppAlg (Nat.log 2 N) B hq).circuit.eval x =
        true).card : ℝ) ≤
      (2 : ℝ) ^ (W3.NearCubicWires.RepairSource.Outer3.requestOf S.mw S.SV S.pcppAlg (Nat.log 2 N) B hq).arity /
        (instLength S.lenG (Nat.log 2 N) : ℝ) :=
    NearCubicGates.Close.Outer.sound_at S.mw S.SV (Nat.log 2 N) N hN z B (S.onset_sv.trans hon)
      (S.onset_pos.trans hon) hfit hcheck (S.not_hier_of_no hno)
  have hpos : (0 : ℝ) < 2 ^
      (W3.NearCubicWires.RepairSource.Outer3.requestOf S.mw S.SV S.pcppAlg (Nat.log 2 N) B hq).arity := by positivity
  refine (div_le_div_of_nonneg_right hs hpos.le).trans (le_of_eq ?_)
  rw [div_div, mul_comm, ← div_div, div_self hpos.ne']

/-- `outerSound` below the masked verifier's outer error (the onset's reserve; Lemma H.3's proof). -/
theorem outerSound_reserve {N : ℕ} (z : BitInput N) (B : OuterGuess (S.width N))
    (hN : N = 2 ^ Nat.log 2 N) (hon : S.onset ≤ Nat.log 2 N) (hno : S.language N z = false)
    (hfit : SrcFits S.lenG (Nat.log 2 N) B.src) (hcheck : CheckAt (Nat.log 2 N) z B.src) :
    uMean (fun x : BitInput (S.request z B).arity => bitR ((S.request z B).circuit.eval x)) ≤
      (S.params.outerError : ℝ) :=
  (S.outerSound z B hN hon hno hfit hcheck).trans (S.onset_reserve _ hon)

end UnionSetup

/-- One guess of the union machine at the input `z`: the pair `Γ = (Γ_src, Γ_pf)`, the class tag, and one sparse grid
sum per PCPP variable (its signs and atoms). -/
structure UnionGuess (S : UnionSetup I) {N : ℕ} (z : BitInput N) where
  pair : OuterGuess (S.width N)
  mode : Mode
  sign : PcppVar (S.pcppOf z pair) → Fin (S.gridSize (S.request z pair).arity) → ℤ
  atom : PcppVar (S.pcppOf z pair) → Fin (S.gridSize (S.request z pair).arity) →
    mode.Circuit (S.request z pair).arity

namespace UnionGuess
variable {S : UnionSetup I} {N : ℕ} {z : BitInput N} (g : UnionGuess S z)

/-- The circuits' input arity `q` (the PCPP input: the outer randomness, padded to the PCPP's minimum arity). -/
abbrev q : ℕ := (S.request z g.pair).arity

/-- The PCPP of `H_Γ`. -/
abbrev pcpp : PointwisePCPP (S.request z g.pair).circuit := S.pcppOf z g.pair

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

/-- The guess as a word: the class tag, the pair field (`pairWord`: the framed codes of `Γ_src` and `Γ_pf`, as one framed
field), and per variable its signs and atom codes. -/
def word : List Bool :=
  [(match g.mode with | Mode.thr => true | Mode.sym => false)] ++
    NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairWord g.pair ++
    (List.ofFn fun X : PcppVar g.pcpp =>
      (List.ofFn fun a : Fin g.s => intWord (g.sign X a) ++ natWord (g.mode.code (g.atom X a))).flatten).flatten

end UnionGuess

/-- **The union machine accepts on the guess** (Lemma H.7; the machine paragraph), its checks in the machine's
order: the setup is live; `N = 2^a` and the onset `≤ a`, `a = ⌊log₂ N⌋` ("rejects unless …"); `Γ_src` and `Γ_pf` have
size at most `q^G`; the description of `Γ_src` has at most `λ_a` bits; the source check `Γ_src(bin_a(i)0^{q−a}) = z_i`;
the coefficients lie on the grid; the guess fits the refuter's `⌊N/16⌋` witness; every primitive call with a nonzero
coefficient is admissible; and the estimates pass the thresholds. -/
def UnionAccepts (S : UnionSetup I) (P : FusedPrimitive I) {N : ℕ} (z : BitInput N) (g : UnionGuess S z) : Prop :=
  S.live = true ∧ N = 2 ^ Nat.log 2 N ∧ S.onset ≤ Nat.log 2 N ∧
  g.pair.src.size ≤ oracleSizeBound S.G (S.width N) ∧ g.pair.pf.size ≤ oracleSizeBound S.G (S.width N) ∧
  SrcFits S.lenG (Nat.log 2 N) g.pair.src ∧ CheckAt (Nat.log 2 N) z g.pair.src ∧
  (∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ)) ∧
  g.word.length ≤ N / 16 ∧
  (∀ pos j t, (g.polyVAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t)) ∧
  (∀ pos j t, (g.polyQAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t)) ∧
  (∀ i j t, (g.polyMuAt i).coeff j t ≠ 0 → I.Call (g.muCall i t)) ∧
  g.Vhat P ≤ 2 * (S.params.v0 : ℝ) ∧ g.Qhat P ≤ 1 + (S.params.v0 : ℝ) ∧ (S.params.threshold : ℝ) ≤ g.μhat P

end Union

end NearCubicWires.WireExponent3_5.Transfer

