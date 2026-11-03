import Close.Chain
import Joins.Transfer
import Joins.Counter
import Gadget.ThreeQuery
import Proof.Hierarchy.HierarchySourceConstructor
import Proof.MachineModel.ClockJoin
import Proof.PCP.PCPPNativeRequestSchema
import Proof.Wire_3_5.Primitive.SeedFix.ReadEq

/-!
# R3.cp — the CheckedPCPP composite (statement)

The near-cubic-gates paper (the oracle `B` is substituted into the outer verifier, giving `D_B` on `q` inputs),
2099–2112 (imp:three-pcpp: the three-query PCPP is applied to `checkedCircuit Enc D_B`; "each systematic coordinate
is a parity of input coordinates"), 2546–2548 ("the honest PCPP proof and each AND helper are computable in
polynomial time once the oracle is known").

ONE machine per `(s, P, g)`, shared by the worker (W3: set-up, then H8 clause access and the parity supports) and the
Case 2 producer (O6b: the hard table). Input: the word of `C_{⟨B_src⟩_ν}` (`mwWord`, the imported constructor's output)
on the port `cIn` and the native descriptor `d = PCPPNative.descriptor B_pf` (what proof 1's `WitnessOracleRun.cold_run`
leaves) on the port `dIn`, every other tape empty (`portBank`). Output, all heads at `0`, each tape READING LIKE
(`RdEq`: the same bit at every cell, trailing blank cells allowed; this is all a consumer keeps after docking on
reused streams anyway) the word below:
* `circuitOut`: `frame (checkedCircuit P.code D_B).word` (the circuit part of the honest prover's input);
* `wordOut`: the J8 word `(P.output (checkedCircuit P.code D_B)).word`, unframed, exactly as H8
  (`ClauseAccess.clause_ready`) reads it;
* `supportsOut`: `frame (supportsWord P.code q)`: per code row `j < L`, `listWord natWord` of the canonical support
  list (the worker's parity lists, `Worker.singleCall`);
* `proofOut`, `randomOut`: the J8 header `frame proofBits.bits`, `frame randomBits.bits` (as in the J8 word).
Cost class: `C·(|word| + |d| + q + 1)^e` (rule M4: classes, not exact terms; `q` because `D_B` has `q` inputs).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.WireExponent3_5.PrimT.ReadEq

/-- The supports record word (the near-cubic-gates paper): code row `j < L` contributes `listWord natWord` of the canonical list of
its support (`canonList`, the order of `checkedCircuit`'s parity chains), as indices. -/
def supportsWord (E : LinearCodeFamily) (q : ℕ) : List Bool :=
  (List.finRange (E.length q)).flatMap fun j =>
    Joins.listWord natWord ((canonList (E.support q j)).map Fin.val)

/-- The composite's entry bank: `h` on the port `a`, `d` on the port `b`, every other tape empty. -/
def portBank (t : ℕ) (a b : Fin t) (h d : List Bool) : Fin t → List Bool :=
  fun i => if i = a then h else if i = b then d else []

/-- The word of the oracle circuit `C_{⟨B_src⟩_ν}` (`ν = log₂ N`) that the imported constructor returns (input 6's
`OracleOutput.word`; the near-cubic-gates paper's fixed weak machine, "It constructs `C^O_{⟨B_src⟩_ν}`"). -/
noncomputable def mwWord (s : GateSources) (g : GateParams) (N : ℕ)
    (Bsrc : BooleanCircuit (Outer.width s.mw (g.sv s) N)) : List Bool :=
  (Outer.outC s.mw (g.sv s) (Nat.log 2 N) Bsrc).word

/-- The outer verifier `D_B` of the guessed pair at source length `N` (the worker's `Worker.substituted`, the Case 2
producer's `D`; the near-cubic-gates paper's fixed weak machine, `D_B = ¬C^{O_{B_pf}}_{⟨B_src⟩_ν}` on `q` inputs). -/
noncomputable def substitutedAt (s : GateSources) (g : GateParams) {N : ℕ} (_x : BitInput N)
    (B : Outer.OuterGuess (Outer.width s.mw (g.sv s) N)) : Circuit :=
  Outer.Dat s.mw (g.sv s) (Nat.log 2 N) B

end NearCubicGates.Close.CheckedPCPP
