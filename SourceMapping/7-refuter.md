# 7. Refuter: CLW20 Theorem 1.13 at the polynomial clocks

The main theorems assume the Lean statement in the first row of the table below (`clw113 : CLW20_Theorem1_13_Poly`,
defined in `Statement_Wire_3_5.lean`). It is CLW20 Theorem 1.13, a refuter with an NP oracle for the
almost-everywhere nondeterministic time hierarchy of Fortnow and Santhanam, at the clocks T(n) = n^(k+2) for every
k ≥ 0. These are the hierarchy clocks the proof uses (paper, §H.1 item 3, and §H.5, "Choose a polynomial hierarchy
clock T(N) = N^{C_clk}"). Each of them is time-constructible and satisfies n ≤ T(n) ≤ 2^{poly(n)}, so hypothesis 8 is
a special case of the printed theorem. The second row shows the Lean proof of this: `theorem1_13_poly_of_literal`
derives hypothesis 8 from `CLW20_Theorem1_13`, the transcription of the printed theorem for every such T in
`Statement.lean`. The other rows show every definition the statement uses; they are definitions of `Statement.lean`,
the same as on page 7 of the Theorem 2.5 repository. In the docstrings, "Tier 1" is the proof's own multitape machine
model (the `OrdinaryMachine` section of `Statement.lean`) and "Tier 2" is Mathlib's standard `Turing.TM2` model; this
statement is read in Tier 1. The group's other result, CLW20 Lemma 3.8 (the XOR lemma, PDF p. 17), is not assumed:
`clw20_xor_source` proves it in Lean, following the paper's proof in CLW20 Appendix A.

[Bindings/CLW20_Lemma3_8.lean, lines 73–76](../Bindings/CLW20_Lemma3_8.lean#L73-L76)

Papers:
- L. Chen, X. Lyu, R. R. Williams, "Almost-Everywhere Circuit Lower Bounds from Non-Trivial Derandomization", ECCC
  TR20-150 (2020), https://eccc.weizmann.ac.il/report/2020/150/download/. Page numbers refer to that PDF,
  SHA-256 d760d3b8349b5e4cc118595767069c778315dd18499650a5fcc1870b085bc02c.
- L. Fortnow, R. Santhanam, "New Non-Uniform Lower Bounds for Uniform Classes", CCC 2016,
  https://doi.org/10.4230/LIPIcs.CCC.2016.19. Page numbers refer to that PDF,
  SHA-256 04c27d5f5641fa236119825d40c29ff9d7ef7cb192ce8002a05e7b27f6e00dcb.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>CLW20, PDF p. 6</b>
<pre>
Theorem 1.13 (Refuter with an NP Oracle, Informal). For every time-constructible function T(n) such that
n ≤ T(n) ≤ 2^{poly(n)}, there is a language L ∈ NTIME[T(n)] and an algorithm R such that:
1. Input. The input to R is a pair (M, 1^n), with the promise that M describes a nondeterministic Turing
machine running in o(T(n)) time and guessing at most n/10 bits.
2. Output. For every fixed M and every sufficiently large n, R(M, 1^n) outputs a string x ∈ {0, 1}^n such
that M(x) ≠ L(x).
3. Complexity. R runs in poly(T(n)) time with adaptive access to an SAT oracle.
</pre>

Hypothesis 8 is this statement at T(n) = n^(k+2), for every k ≥ 0. `Theorem1_13At T` is its conclusion at one T, and
`CLW20_Theorem1_13`, shown for comparison, is the printed statement for every T in its range.
</td><td>

[Statement_Wire_3_5.lean, lines 65–69](../Statement_Wire_3_5.lean#L65-L69)

<pre title="Statement_Wire_3_5.lean, lines 65–69">
/-- **Input 8**: CLW20 Theorem 1.13 ("For every time-constructible function T(n) such that n ≤ T(n) ≤ 2^{poly(n)}, there is
a language L ∈ NTIME[T(n)] and an algorithm R such that …", PDF p. 6) at the polynomial clocks `T(n) = n^(k+2)`, each of
which is time-constructible with `n ≤ T(n) ≤ 2^{poly(n)}`: the hierarchy clocks the proof uses. -/
def CLW20_Theorem1_13_Poly : Prop :=
  ∀ k : ℕ, NearCubicWires.Bindings.CLW20Theorem113.Theorem1_13At (fun n =&gt; n ^ (k + 2))
</pre>

[Statement.lean, lines 2291–2302](../Statement.lean#L2291-L2302)

<pre title="Statement.lean, lines 2291–2302">
/-- The conclusion of Theorem 1.13 at one clock `T`: "there is a language L ∈ NTIME[T(n)] and an
algorithm R such that" items 1–3 hold. The degree `d` of "poly(T(n))" belongs to `R`. The
coefficient `C` and the onset of "every sufficiently large n" may depend on the fixed `M`. -/
def Theorem1_13At (T : ℕ → ℕ) : Prop :=
  ∃ L : Language, InNTIME T L ∧
    ∃ (R : OrdinaryOracleProgram) (d : ℕ),
      ∀ M : OrdinaryWeakMachine, OrdinaryLittleO M T →
        ∃ C onset : ℕ, ∀ n, onset ≤ n →
          ∃ x : BitInput n,
            OrdinaryOracleRuns RecoveryOracle.sourceSAT R (pairInput M n) (List.ofFn x)
              (C * (T n + 1) ^ d) ∧
            machineValue M n x ≠ L n x
</pre>

[Statement.lean, lines 2304–2315](../Statement.lean#L2304-L2315)

<pre title="Statement.lean, lines 2304–2315">
/-- **CLW20 Theorem 1.13, PDF page 6 (printed p.5), verbatim:**
"Theorem 1.13 (Refuter with an NP Oracle, Informal). For every time-constructible function T(n)
such that n ≤ T(n) ≤ 2^{poly(n)}, there is a language L ∈ NTIME[T(n)] and an algorithm R such that:
1. Input. The input to R is a pair (M, 1^n), with the promise that M describes a nondeterministic
Turing machine running in o(T(n)) time and guessing at most n/10 bits.
2. Output. For every fixed M and every sufficiently large n, R(M, 1^n) outputs a string
x ∈ {0,1}^n such that M(x) ≠ L(x).
3. Complexity. R runs in poly(T(n)) time with adaptive access to an SAT oracle."
The module docstring records each reading, including the one step Lean does not check: the
multitape machine model. -/
def CLW20_Theorem1_13 : Prop :=
  ∀ T : ℕ → ℕ, TimeConstructible T → InClockRange T → Theorem1_13At T
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 6</b>
<pre>
For every time-constructible function T(n) such that
n ≤ T(n) ≤ 2^{poly(n)}
</pre>

Every clock n^(k+2) is in this range, so the printed statement applies to it. `ordinaryClock k` is the proof's
clock n^(k+2): a Tier 1 machine computes it from 1^n in O(n^(k+2)) steps, and n ≤ n^(k+2) ≤ 2^{poly(n)}.
`clock_timeConstructible` and `clock_inClockRange` turn such a clock into the two hypotheses of the printed
statement, and `theorem1_13_poly_of_literal` applies the printed statement at each k.
</td><td>

[Statement.lean, lines 2266–2270](../Statement.lean#L2266-L2270)

<pre title="Statement.lean, lines 2266–2270">
/-- "time-constructible" (standard notion, Tier 1 multitape model): a program that, given the word
`1^n`, outputs the binary digits of `T(n)` within `C·(T(n)+1)` steps. -/
def TimeConstructible (T : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, 0 &lt; C ∧ Nonempty (OrdinaryWordFunction ℕ (fun n =&gt; List.replicate n true)
    (fun n =&gt; (T n).bits) (fun n =&gt; C * (T n + 1)))
</pre>

<pre title="Statement.lean, lines 2272–2274">
/-- "n ≤ T(n) ≤ 2^{poly(n)}". -/
def InClockRange (T : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ T n) ∧ ∃ C k : ℕ, ∀ n, T n ≤ 2 ^ (C * (n + 1) ^ k)
</pre>

[StatementChecks/Wire_3_5_Inputs.lean, lines 21–24](../StatementChecks/Wire_3_5_Inputs.lean#L21-L24)

<pre title="StatementChecks/Wire_3_5_Inputs.lean, lines 21–24">
/-- CLW20 Theorem 1.13 as printed implies hypothesis 8: its conclusion at every clock `T(n) = n^(k+2)`. -/
theorem theorem1_13_poly_of_literal (h : CLW20_Theorem1_13) : CLW20_Theorem1_13_Poly := fun k =&gt;
  h _ (clock_timeConstructible (RepairOrdinary.PolynomialClock.ordinaryClock k))
    (clock_inClockRange (RepairOrdinary.PolynomialClock.ordinaryClock k))
</pre>

[Bindings/CLW20_Theorem1_13.lean, lines 149–151](../Bindings/CLW20_Theorem1_13.lean#L149-L151)

<pre title="Bindings/CLW20_Theorem1_13.lean, lines 149–151">
/-- The import's clock is time-constructible in the literal's sense. -/
theorem clock_timeConstructible {T : ℕ → ℕ} (clock : OrdinaryClock T) : TimeConstructible T :=
  ⟨clock.coefficient, clock.coefficientPositive, ⟨clock.computer⟩⟩
</pre>

<pre title="Bindings/CLW20_Theorem1_13.lean, lines 153–156">
/-- The import's clock lies in the literal's range `n ≤ T(n) ≤ 2^{poly(n)}`. -/
theorem clock_inClockRange {T : ℕ → ℕ} (clock : OrdinaryClock T) : InClockRange T := by
  obtain ⟨c, k, -, hb⟩ := clock.polynomial
  exact ⟨clock.atLeastInput, c, k, fun n =&gt; (hb n).trans Nat.lt_two_pow_self.le⟩
</pre>

[Proof/Circuits/PolynomialOrdinaryClock.lean, line 82](../Proof/Circuits/PolynomialOrdinaryClock.lean#L82)

<pre title="Proof/Circuits/PolynomialOrdinaryClock.lean, line 82">
noncomputable def ordinaryClock (k : ℕ) : OrdinaryClock (fun n =&gt; n^(k+2)) where
</pre>

[Proof/Foundations/SourceCore.lean, lines 17–23](../Proof/Foundations/SourceCore.lean#L17-L23)

<pre title="Proof/Foundations/SourceCore.lean, lines 17–23">
structure OrdinaryClock (T : ℕ → ℕ) where
  atLeastInput : ∀ n, n ≤ T n
  polynomial : PolynomiallyBounded T
  coefficient : ℕ
  coefficientPositive : 0 &lt; coefficient
  computer : OrdinaryWordFunction ℕ (fun n =&gt; List.replicate n true)
    (fun n =&gt; (T n).bits) (fun n =&gt; coefficient*(T n+1))
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 6</b>
<pre>
there is a language L ∈ NTIME[T(n)]
</pre>
<b>CLW20, PDF p. 6</b>
<pre>
Let NTIMEGUESS[t(n), g(n)] be the class of languages
decided by nondeterministic algorithms running in O(t(n)) steps and guessing at most g(n) bits.
</pre>
</td><td>

[Statement.lean, lines 2276–2280](../Statement.lean#L2276-L2280)

<pre title="Statement.lean, lines 2276–2280">
/-- "L ∈ NTIME[T(n)]" (nondeterministic `O(T(n))` time, Tier 1 multitape model): `L` is the
language of a verifier that halts within `c·(T(n)+1)` steps on every witness of length
`c·(T(n)+1)`. -/
def InNTIME (T : ℕ → ℕ) (L : Language) : Prop :=
  ∃ H : OrdinaryHierarchy T, ∀ n (x : BitInput n), L n x = true ↔ H.verifier.language H.time n x
</pre>

[Statement.lean, lines 1376–1382](../Statement.lean#L1376-L1382)

<pre title="Statement.lean, lines 1376–1382">
structure OrdinaryHierarchy (T : ℕ → ℕ) where
  verifier : OrdinaryVerifier
  coefficient : ℕ
  coefficientPositive : 0 &lt; coefficient
  halts : ∀ n (x : BitInput n) (w : BitInput (coefficient*(T n+1))),
    ∃ receipt, run verifier.machine (coefficient*(T n+1))
      (verifier.inputTapes (List.ofFn x) (List.ofFn w)) = some receipt
</pre>

<pre title="Statement.lean, lines 1384–1385">
def OrdinaryHierarchy.time {T : ℕ → ℕ} (H : OrdinaryHierarchy T) (n : ℕ) : ℕ :=
  H.coefficient*(T n+1)
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 6</b>
<pre>
The input to R is a pair (M, 1^n), with the promise that M describes a nondeterministic Turing
machine running in o(T(n)) time and guessing at most n/10 bits.
</pre>
</td><td>

[Statement.lean, lines 2282–2284](../Statement.lean#L2282-L2284)

<pre title="Statement.lean, lines 2282–2284">
/-- "The input to R is a pair (M, 1^n)": the framed description of `M`, then the framed `1^n`. -/
def pairInput (M : OrdinaryWeakMachine) (n : ℕ) : List Bool :=
  frame (VerifierEncoding.code M.verifier) ++ frame (List.replicate n true)
</pre>

[Statement.lean, lines 1387–1392](../Statement.lean#L1387-L1392)

<pre title="Statement.lean, lines 1387–1392">
structure OrdinaryWeakMachine where
  verifier : OrdinaryVerifier
  runtime : ℕ → ℕ
  halts : ∀ n (x : BitInput n) (w : BitInput (n/16)),
    ∃ receipt, run verifier.machine (runtime n)
      (verifier.inputTapes (List.ofFn x) (List.ofFn w)) = some receipt
</pre>

<pre title="Statement.lean, lines 1394–1396">
def OrdinaryWeakMachine.accepts (M : OrdinaryWeakMachine)
    (n : ℕ) (x : BitInput n) : Prop :=
  M.verifier.language (fun n =&gt; n/16) n x
</pre>

<pre title="Statement.lean, lines 1398–1400">
def OrdinaryLittleO (M : OrdinaryWeakMachine) (T : ℕ → ℕ) : Prop :=
  ∀ multiplier : ℕ, 0 &lt; multiplier →
    ∃ onset, ∀ n, onset ≤ n → multiplier*M.runtime n ≤ T n
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 6</b>
<pre>
R(M, 1^n) outputs a string x ∈ {0, 1}^n such
that M(x) ≠ L(x).
</pre>
<b>CLW20, PDF p. 19</b> (the big OR is over the witnesses w)
<pre>
Note that for an M using o(T(n)) time and g(n) guesses, we have
M(x) = 1 ⇔ ∨_{w∈{0,1}^{g(n)}} V_M(x, T(n), w) = 1.
</pre>
</td><td>

[Statement.lean, lines 2286–2289](../Statement.lean#L2286-L2289)

<pre title="Statement.lean, lines 2286–2289">
/-- `M(x)`, the truth value of "some witness makes `M` accept `x`" (CLW20 p.19). -/
noncomputable def machineValue (M : OrdinaryWeakMachine) (n : ℕ) (x : BitInput n) : Bool := by
  classical
  exact decide (M.accepts n x)
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 6</b>
<pre>
R runs in poly(T(n)) time with adaptive access to an SAT oracle.
</pre>
</td><td>

[Statement.lean, lines 1519–1521](../Statement.lean#L1519-L1521)

<pre title="Statement.lean, lines 1519–1521">
structure OracleReturn (stateCount : ℕ) where
  onFalse : Fin stateCount
  onTrue : Fin stateCount
</pre>

<pre title="Statement.lean, lines 1523–1527">
structure OrdinaryOracleProgram where
  base : OrdinaryProgram
  queryTape : Fin base.tapeCount
  queryFresh : queryTape.val ≠ 0
  query : Fin base.stateCount → Option (OracleReturn base.stateCount)
</pre>

<pre title="Statement.lean, lines 1532–1549">
/-- Literal costs are fixed by the local/query constructors; no arbitrary
counter attached to a semantic computation is accepted as execution evidence. -/
inductive OrdinaryOracleStep (oracle : ℕ → Bool) (program : OrdinaryOracleProgram) :
    ℕ → program.Config → program.Config → Prop where
  | local (before after : program.Config)
      (notHalted : program.base.machine.halted before.control = false)
      (notQuery : program.query before.control = none)
      (transition : step program.base.machine before = some after) :
      OrdinaryOracleStep oracle program 1 before after
  | ask (before : program.Config) (bits padding : List Bool)
      (rule : OracleReturn program.base.stateCount)
      (notHalted : program.base.machine.halted before.control = false)
      (atQuery : program.query before.control = some rule)
      (rewound : before.heads program.queryTape = 0)
      (writtenQuery : before.tapes program.queryTape = frame bits ++ padding) :
      OrdinaryOracleStep oracle program ((frame bits).length + 1) before
        { before with control := if oracle (CanonicalBinary.bitsValue bits)
            then rule.onTrue else rule.onFalse }
</pre>

<pre title="Statement.lean, lines 1551–1558">
inductive OrdinaryOracleTrace (oracle : ℕ → Bool) (program : OrdinaryOracleProgram) :
    ℕ → program.Config → program.Config → Prop where
  | refl (configuration : program.Config) :
      OrdinaryOracleTrace oracle program 0 configuration configuration
  | cons {cost rest : ℕ} {before middle after : program.Config}
      (step : OrdinaryOracleStep oracle program cost before middle)
      (tail : OrdinaryOracleTrace oracle program rest middle after) :
      OrdinaryOracleTrace oracle program (cost + rest) before after
</pre>

<pre title="Statement.lean, lines 1560–1569">
/-- Inputs and outputs are framed, with a distinct initially blank output tape.
All data preparation, querying and final head movements inside the program
must be present in the counted trace. -/
def OrdinaryOracleRuns (oracle : ℕ → Bool) (program : OrdinaryOracleProgram)
    (input output : List Bool) (budget : ℕ) : Prop :=
  ∃ cost final, cost ≤ budget ∧
    OrdinaryOracleTrace oracle program cost
      (initialConfiguration program.base.machine (program.base.inputTapes input)) final ∧
    program.base.machine.halted final.control = true ∧
    final.tapes program.base.outputTape = frame output
</pre>

[Statement.lean, lines 1611–1614](../Statement.lean#L1611-L1614)

<pre title="Statement.lean, lines 1611–1614">
noncomputable def sourceSAT (code : Nat) : Bool :=
  match decodeSourceSAT code with
  | some formula =&gt; formula.all (fun clause =&gt; clause.length = 3) &amp;&amp; mathSat formula
  | none =&gt; false
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 19</b>
<pre>
We fix a natural enumeration of all (multitape) nondeterministic Turing machines. Note that the specific
model does not really matter, see the discussion in [Wil13], Section 2.1.
</pre>
<b>FS16, PDF p. 13</b>
<pre>
Since we can universally simulate t(n)-time nondeterministic multitape Turing machines
on an O(t(n))-time 2-tape nondeterministic Turing machine
</pre>
</td><td>

[Statement.lean, lines 1138–1145](../Statement.lean#L1138-L1145)

<pre title="Statement.lean, lines 1138–1145">
/-- A finite local action: one replacement bit and one unit head move per
tape, plus the next finite control state. -/
structure Action (tapeCount stateCount : ℕ) where
  nextControl : Fin stateCount
  /-- `none` leaves a tape unchanged; `some bit` writes exactly its scanned
  cell. -/
  write : Fin tapeCount → Option Bool
  move : Fin tapeCount → HeadMove
</pre>

<pre title="Statement.lean, lines 1147–1154">
/-- The transition function has a finite domain (`Fin stateCount` and one bit
per tape), so it is extensionally a finite transition table. -/
structure Machine (tapeCount stateCount : ℕ) where
  descriptionBits : ℕ
  start : Fin stateCount
  halted : Fin stateCount → Bool
  rule : Fin stateCount → (Fin tapeCount → Bool) →
    Option (Action tapeCount stateCount)
</pre>

<pre title="Statement.lean, lines 1169–1175">
def step
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount)
    (configuration : Configuration tapeCount stateCount) :
    Option (Configuration tapeCount stateCount) :=
  (machine.rule configuration.control configuration.scanned).map
    (applyAction configuration)
</pre>

[Statement.lean, lines 1327–1332](../Statement.lean#L1327-L1332)

<pre title="Statement.lean, lines 1327–1332">
structure Verifier where
  tapeCount : ℕ
  stateCount : ℕ
  twoTapes : 2 ≤ tapeCount
  machine : Machine tapeCount stateCount
  accepting : Fin stateCount → Bool
</pre>

<pre title="Statement.lean, lines 1334–1337">
def Verifier.inputTapes (v : Verifier)
    (input witness : List Bool) : Fin v.tapeCount → List Bool :=
  fun i =&gt; if i.val = 0 then frame input
    else if i.val = 1 then frame witness else []
</pre>

<pre title="Statement.lean, lines 1344–1345">
def Verifier.accepts (v : Verifier) (input witness : List Bool) : Prop :=
  ∃ fuel, v.acceptsAt fuel input witness
</pre>

<pre title="Statement.lean, lines 1347–1353">
/-- A bare witness-length function is a semantic parameter, not evidence of
    computable nondeterminism; executable source packages must supply its
    computer and its ordinary cost separately. -/
def Verifier.language (v : Verifier) (witnessLength : ℕ → ℕ) :
    (n : ℕ) → BitInput n → Prop :=
  fun n x =&gt; ∃ w : BitInput (witnessLength n),
    v.accepts (List.ofFn x) (List.ofFn w)
</pre>

</td></tr>
</table>

Superscripts are written with `^`, with `{…}` around a superscript of more than one symbol (`2^{poly(n)}` is
2<sup>poly(n)</sup>), and subscripts with `_`.

**The reading that needs an argument: the machine model.** Lean cannot check readings: o(T(n)), poly(T(n)), the SAT
encoding and witnesses as guesses are all fixed by the definitions below. The one reading that needs an argument is the
machine model. The paper's “Turing machine”, “NTIME” and “algorithm R” are read in Tier 1: finite control, one-sided
binary tapes, one scanned bit per tape, and in each step one write and a head move of at most one cell on each tape
(last row of the table). CLW20 (“the specific model does not really matter”) and FS16's universal multitape simulation
support this reading. The reading also covers the oracle: “SAT” is read as satisfiability of 3-CNF formulas in a fixed
explicit encoding (`RecoveryOracle.sourceSAT`). The Tseitin reduction makes the two interreducible in polynomial time,
and the poly(T(n)) budget absorbs that cost.

This is also why the transcription uses Theorem 1.13 and not the paper's formal Theorem 4.6 (PDF p. 22). Section 4
states:

<b>CLW20, PDF p. 19</b>
<pre>
For simplicity, we assume all machines are
random-access machines in the following.
</pre>

Theorem 4.6 refutes one specific language, whose definition runs random-access machines. Theorem 1.13 asks only for
some L ∈ NTIME[T(n)]. In the multitape reading, L can be a clocked variant of the hard language: FS16's universal 2-tape
simulation, run for O(T(n)) of its own steps. Each fixed promise machine runs in time o(T(n)), so its simulation
finishes for every large n, and every guarantee of the theorem is claimed only for large n.

Theorem 4.6 is stated for random-access machines, and the Lean statement is read for multitape machines. The Lean
statement follows from the proof of Theorem 4.6 carried out for multitape machines: Definition 4.2 run as the clocked
FS16 simulation with witness length ⌊n/16⌋; Lemma 4.3, which holds at large n because a promise machine's running time
is eventually below the clock; and the case analysis of Theorem 1.12 and Corollary 4.5 with its SAT queries,
unchanged. The paper states this reading in §H.8, paragraph "A multitape reading", which ends: "The public Lean
development of row B uses this multitape reading, with the refuter of item 3 at the polynomial clocks T(N)=N^{k+2}."

**What to check** (a few minutes):

1. The order is the paper's, at each clock: for every k, with T(n) = n^(k+2), there are L ∈ NTIME[T], an algorithm R
   and one degree d, such that for every M satisfying the promise there are a coefficient C and an onset, and for
   every n past the onset there is an x ∈ {0,1}^n. The degree belongs to R, because item 3 is a property of the one
   algorithm R. The coefficient C and the onset of “every sufficiently large n” may depend on the fixed M, whose
   description is part of R's input. L, R and d may depend on k, as they may depend on T in the printed statement.
2. Hypothesis 8 asks, for every k, for the conclusion `Theorem1_13At` of the printed statement at T(n) = n^(k+2), and
   for nothing else. It assumes no more than the printed statement: `theorem1_13_poly_of_literal` applies
   `CLW20_Theorem1_13` to each of these T.
3. The range of the printed statement, used in that proof: CLW20 does not define time-constructible, and the standard
   notion is used (a machine that, given 1^n, writes T(n) in binary within C·(T(n)+1) steps); n ≤ T(n) for every n, and
   T(n) ≤ 2^(C·(n+1)^k) for some constants C and k.
4. “L ∈ NTIME[T(n)]” says that L is the language of a verifier that halts within c·(T(n)+1) steps on every witness
   of that length and accepts x exactly when some such witness is accepted.
5. The promise: M is a verifier with a witness of exactly ⌊n/16⌋ bits and a step bound (`runtime n`) that holds on
   every input and every witness. “o(T(n))” is `OrdinaryLittleO`: for every m > 0, eventually m·runtime(n) ≤ T(n).
   M(x) is true when some witness is accepted, as on PDF p. 19.
6. The input (M, 1^n) is the framed code of M followed by 1^n framed. The code determines everything that a run of M
   reads, so two machines with the same code have the same language.
7. The output: R halts within C·(T(n)+1)^d steps with x on its output tape (`OrdinaryOracleRuns`), and
   “M(x) ≠ L(x)” is the Boolean inequality `machineValue M n x ≠ L n x`.
8. The oracle: R is a deterministic multitape program with query states. Its next state depends on the oracle's
   answer, so its access is adaptive. A query costs its framed length plus one step.

**The promise class.** The machines M guess exactly ⌊n/16⌋ bits, which is within the printed “at most n/10 bits”.
With fewer machines M, the assumed statement claims less. A promise machine here is a verifier that reads its witness
from a tape; it becomes a nondeterministic machine in the printed sense by guessing each witness bit when it first
reads it, with constant overhead and at most ⌊n/16⌋ ≤ n/10 guesses.

[Bindings/CLW20_Theorem1_13.lean, lines 132–134](../Bindings/CLW20_Theorem1_13.lean#L132-L134)

<pre title="Bindings/CLW20_Theorem1_13.lean, lines 132–134">
/-- The promise machines guess ⌊n/16⌋ bits, within the printed "at most n/10 bits". -/
theorem witness_bits_within_promise (n : ℕ) : n / 16 ≤ n / 10 :=
  actualWitnessBound n
</pre>

**How the proof uses it.** At each clock n^(k+2), `at_to_algorithm` turns the conclusion of Theorem 1.13 into the
refuter algorithm the proof runs; you need not read it. On polynomially bounded clocks with T(n) ≥ n that a Tier 1
machine computes in O(T(n)) steps, such as n^(k+2), the two are equivalent (`import_iff_on_clocks`), so the proof does
not change what the refuter guarantees.

[Bindings/CLW20_Theorem1_13.lean, lines 193–195](../Bindings/CLW20_Theorem1_13.lean#L193-L195)

<pre title="Bindings/CLW20_Theorem1_13.lean, lines 193–195">
/-- The literal's conclusion at `T` yields the import's refuter algorithm at `T`. -/
theorem at_to_algorithm {T : ℕ → ℕ} (h : Theorem1_13At T) :
    Nonempty (HierarchyRefuterAlgorithm T) := by
</pre>

[Bindings/CLW20_Theorem1_13.lean, lines 230–239](../Bindings/CLW20_Theorem1_13.lean#L230-L239)

<pre title="Bindings/CLW20_Theorem1_13.lean, lines 230–239">
/-- The import is exactly the literal's conclusion on the import's clocks: it narrows only the
T-domain (polynomially bounded ordinary clocks with `T n ≥ n`), not the refuter's guarantee. -/
theorem import_iff_on_clocks :
    HierarchyRefuterSource ↔ ∀ T : ℕ → ℕ, OrdinaryClock T → Theorem1_13At T := by
  constructor
  · intro source T clock
    obtain ⟨A⟩ := source T clock
    exact algorithm_to_at clock A
  · intro h T clock
    exact at_to_algorithm (h T clock)
</pre>

**Class:** special case of the printed statement (the clocks n^(k+2)), read for multitape machines; it follows from
the proof of Theorem 4.6 carried out for multitape machines (see "The reading that needs an argument" above).
