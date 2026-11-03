import ENP.TSpec
import ENP.TEval
import ENP.TPrefix
import Proof.Amplification.RecoveryPrefixCanonical
import Platform.WMX

/-!
# Stage 2: interfaces of the pieces of `ENP.TStage`

The near-cubic-gates paper's uniform recovery (sec:all-lengths, E^NP paragraph, stage 2): "a formula with one variable per oracle address and the
constraints `C^O_{⟨B*_src⟩_ν}(R) = 0` for all `2^{ℓ_out}` inputs `R` … (each oracle gate becomes a selector over the
`2^{ℓ_out}` oracle variables), finds the first oracle `O*`." The stage is the stage-2 builder (the circuit `TCirc.tCircuit C`,
emitted by a WMX program from the oracle circuit's raw word) followed by proof 1's circuit serializer and SAT prefix
search. The pieces, with the statements here:

* `TProg` — the stage-2 emitter as one WMX program (`ENP/TEmit*`).
* `TBytesSpec` — the bytes of the start region and seed 0 are at least the word (used by the emitter to rewind the
  word stream).
* `TFlagSpec`, `TTableSpec` — the meaning of the search's flag and prefix on `c_T`.
* `TStageOf` — the docking: emitter + serializer + search join ⇒ `TStage`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.ENP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairSource NearCubicWires.Bindings.MW20
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.CircuitInputCNF NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Platform NearCubicWires.SourceInterfaces

/-- The emitter's start state: the raw word (followed by `post`) on stream 0, every other stream empty, every head and
register at `0`. -/
def tStart (w : List Bool) : WState 3 40 where
  sh := fun _ => 0
  st := ![w, [], [], []]
  val := fun _ => 0
  cell := false

/-- The emitter's end states: stream 0 unchanged, stream 1 the marked graph, stream 2 scratch, stream 3 the info word;
every head and register at `0`. -/
def tFinish (w g junk info : List Bool) : WState 3 40 where
  sh := fun _ => 0
  st := ![w, g, junk, info]
  val := fun _ => 0
  cell := false

/-- The info word: the arity `n` and the output index `o` in unary, separated by one `false`. -/
def tInfo (n o : ℕ) : List Bool := List.replicate n true ++ false :: List.replicate o true

/-- The native graph of `c_T` (proof 1's serializer input `RecoveryBoundedGraphSerialize.graph`). -/
def tGraph {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) : List Bool :=
  (TCirc.tCircuit C).nodes.flatMap RepairOrdinary.PCPPRequestNodeSchema.native

/-- **Builder T's emitter** (producer L3): one WMX program that, started on the oracle circuit's raw word,
halts with the MARKED native graph of `c_T` on stream 1 (`RepairOrdinary.Streaming.marks`: a `true` marker before each bit, so
its end is detectable) and the info word `2^ℓ`, output index on stream 3, every head and register back at `0` (so
`CheckedPCPP.WXExec.ready` applies); cost polynomial in `2^ℓ + |word ++ post|`. -/
structure TProg where
  prog : WMX 3 40
  K : ℕ
  e : ℕ
  run : ∀ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool), ∃ cap n junk,
    n ≤ K * (2 ^ ℓ + ((OracleOutput.word ⟨ℓ, C⟩) ++ post).length + 1) ^ e ∧
    WXExec cap prog (tStart ((OracleOutput.word ⟨ℓ, C⟩) ++ post))
      (tFinish ((OracleOutput.word ⟨ℓ, C⟩) ++ post) (RepairOrdinary.Streaming.marks (tGraph C)) junk
        (tInfo (2 ^ ℓ) (TCirc.tCircuit C).output.val)) n

/-- **The word fits in the first seed's bytes** (pure): the emitter rewinds the word stream by the number of
bytes written so far. -/
def TBytesSpec : Prop :=
  ∀ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ),
    (OracleOutput.word ⟨ℓ, C⟩).length ≤
      ((TCirc.start ℓ).flatMap RepairOrdinary.PCPPRequestNodeSchema.native).length +
        ((TCirc.seed C 0).flatMap RepairOrdinary.PCPPRequestNodeSchema.native).length

/-- **The flag** (pure): the corrected SAT oracle on the uncommitted query of `c_T`'s input formula says
whether an honest table exists. -/
def TFlagSpec : Prop :=
  ∀ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ),
    RecoveryOracle.correctedSat (RecoveryQuery.code true
      (RecoveryFormulaPrefix.payload (circuitInputFormula (TCirc.tCircuit C))) 0 0) = true ↔
    ∃ t, Transfer.HonestTable C t

/-- **The prefix** (pure): proof 1's prefix search on `c_T`'s payload over all `2^ℓ` variables returns the
first honest table. -/
def TTableSpec : Prop :=
  ∀ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (first : Transfer.FirstTable C),
    RecoveryPrefixBody.search true (RecoveryFormulaPrefix.payload (circuitInputFormula (TCirc.tCircuit C)))
      (2 ^ ℓ) [] = List.ofFn first.table

/-- **The docking**: the emitter, proof 1's serializer and SAT search, and the meaning give stage 2. -/
def TStageOf : Prop := Nonempty TProg → TFlagSpec → TTableSpec → TStageRuns

end NearCubicGates.Close.ENP
