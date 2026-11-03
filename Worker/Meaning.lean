import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import NearCubicGates.FiniteAverages
import NearCubicGates.Gadget
import Joins.Counter
import Joins.Transfer
import Proof.Foundations.OuterPCPRecovery

/-!
# J10 — the weak worker's meaning (the near-cubic-gates paper's fixed weak machine, "A fixed weak machine and its source instance", with eq:gadget-pair-identity)

For a hierarchy input `x` of length `N = 2^ν`, a guess is: the pair `B = (B_src, B_pf)` of Boolean circuits on the native
width `q` (the (a′) repair, the near-cubic-gates paper's fixed weak machine: the source circuit, checked against `x`, and the outer proof oracle), one normalized circuit (J3's `NCircuit`) per auxiliary name — every proof coordinate of the three-query PCPP
of `checkedCircuit P.code D_B` and one fresh helper per gadget — and counter witness prefixes for every gadget and
term. The clause list is repeated to `M = 2^{cl}` gadgets (`cl = ⌈d_G lg(q+2)⌉`). Coordinates are systematic parities
of the outer randomness `r ∈ {0,1}^q` or guessed circuits evaluated at `r`. Each of the ten terms of a gadget is the
XOR of at most two atoms with a flip; its interval is exact (pure parities, repeated circuits) or one counter call
(single, circuit ⊕ parity, pair), flipped when needed. `U` is `Worker.upper` of these intervals.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Joins

variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)

/-- The native width at source length `N` (the near-cubic-gates paper's fixed weak machine, `q(N)`). -/
noncomputable def width (N : ℕ) : ℕ := Outer.width s.mw (g.sv s) N

/-- The source index `ν` of a length `N = 2^ν`. -/
def nu (N : ℕ) : ℕ := Nat.log 2 N

/-- The outer verifier `D_B` for the guessed pair `B = (B_src, B_pf)` (the near-cubic-gates paper's fixed weak machine: "Substituting `O_{B_pf}` for every
oracle gate and negating the output gives the outer verifier"). It does not read the source input; CHECK does
(`Guards`). -/
noncomputable def substituted {N : ℕ} (_x : BitInput N) (B : Outer.OuterGuess (width s g N)) : Circuit :=
  Outer.Dat s.mw (g.sv s) (nu N) B

/-- The set-up's guards on a guessed pair (the near-cubic-gates paper's fixed weak machine): `N = 2^ν` ("the weak machine first rejects unless N = 2^ν is
a power of two"); `ν` past the onset of `𝒱_G` (Lean's `SuccinctVerifier` holds from an onset, a finite set of lengths);
the length guard on the guessed source circuit ("it rejects unless the description of the source circuit B_src guessed
below has at most L_ν bits. By the choice of G′, once ν is large every general circuit with q inputs and at most q^G
gates has such a description, so the last guard rejects at only finitely many lengths"); and CHECK (eq:source-check).
See `Guess.SetupOK`. -/
def PairOK {N : ℕ} (x : BitInput N) (B : Outer.OuterGuess (width s g N)) : Prop :=
  N = 2 ^ nu N ∧ (g.sv s).onset ≤ nu N ∧ Outer.SrcFits g.lenExp (nu N) B.src ∧ Outer.CheckAt (nu N) x B.src

/-- The number of systematic coordinates: the outer randomness and its code parities. -/
noncomputable def sysCount {N : ℕ} (x : BitInput N) (B : Outer.OuterGuess (width s g N)) : ℕ :=
  (substituted s g x B).n + P.code.length (substituted s g x B).n

/-- The three-query PCPP of the checked substituted verifier (irreducible, to keep elaboration away from the
circuit builder). -/
noncomputable def pcpp {N : ℕ} (x : BitInput N) (B : Outer.OuterGuess (width s g N)) :
    RawThreeQueryPCPP (sysCount s P g x B) :=
  P.output (checkedCircuit P.code (substituted s g x B))

/-- The number of gadgets `M = 2^{cl}`. -/
noncomputable abbrev gadgets (N : ℕ) : ℕ := 2 ^ clauseWidth g.clauseDegree (width s g N)

namespace Guess

end Guess

/-! ## Intervals, the upper estimate, and the meaning -/

/-- The mean of a parity of `r` on support `S`: `1/2` when `S` is nonempty, else `0`. -/
def parityMean {q : ℕ} (S : Finset (Fin q)) : ℚ := if S.Nonempty then 1 / 2 else 0

namespace Guess

end Guess

end NearCubicGates.Close.Worker
