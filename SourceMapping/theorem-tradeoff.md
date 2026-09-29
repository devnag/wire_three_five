# Theorem 1.1, row B

The main theorem concludes `NearCubicWires.WireExponent3_5.rowB`, the Lean statement in the first row of the table
below: row B of the paper's Theorem 1.1, with the definitions of `Statement_Wire_3_5.lean` shown in full. The other rows
show the definitions it uses, beside the paper's own definitions. The last section links the statement checks that Lean
proves.

Paper: the paper's source is [`paper/paper.tex`](../paper/paper.tex); line numbers refer to that file, and the Lean
comments cite them as `P3:n`. The quotations are its LaTeX source, verbatim.

The nine published statements the main theorem assumes are not shown here. They are the hypotheses of the Theorem 2.5
repository, defined in `Statement.lean` (the same file, byte for byte), and each is put beside its published sentence
on that repository's pages: [SourceMapping/](https://github.com/devnag/near-cubic-wires/tree/main/SourceMapping).

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>paper/paper.tex, lines 225–238</b>
<pre>
\begin{theorem}[Parameterized wire--correlation tradeoff]
\label{thm:tradeoff}
Fix $c&gt;0$ and real constants $K_T&gt;5+2c$ and $K_S&gt;4+2c$.
There is a language $F\in\ENP$ such that, for every pair of fixed
constants $A_T,A_S&gt;0$, there is $n_0$ for which, for every $n\ge n_0$,
\begin{align*}
W(C)\le A_T n^{7/2}/L(n)^{K_T},\quad C\in\THR\circ\THR
&amp;\quad\Longrightarrow\quad \agr(F_n,C)&lt;\tfrac12+L(n)^{-c},\\
W(C)\le A_S n^{7/2}/L(n)^{K_S},\quad C\in\SYM\circ\THR
&amp;\quad\Longrightarrow\quad \agr(F_n,C)&lt;\tfrac12+L(n)^{-c}.
\end{align*}
The language may depend on $c,K_T,K_S$, but not on $A_T,A_S$;
the onset $n_0$ may depend on the multipliers.
\end{theorem}
</pre>
<b>paper/paper.tex, line 256</b>
<pre>
 &amp; Wire caps, THR / SYM &amp; Coefficient quantifier &amp; Advantage\\
</pre>
<b>paper/paper.tex, lines 261–262</b>
<pre>
B &amp; $A_T n^{7/2}/L^{11/2}$, $A_S n^{7/2}/L^{9/2}$
  &amp; Every fixed $A_T,A_S&gt;0$ &amp; $L^{-1/8}$\\[3pt]
</pre>
<b>paper/paper.tex, line 219</b>
<pre>
Almost everywhere means at every sufficiently large integer length.
</pre>
<b>paper/paper.tex, lines 36–38</b>
<pre>
\newcommand{\THR}{\mathrm{THR}}
\newcommand{\SYM}{\mathrm{SYM}}
\newcommand{\ENP}{\mathrm{E}^{\mathrm{NP}}}
</pre>
</td><td>

[Statement_Wire_3_5.lean, lines 54–55](../Statement_Wire_3_5.lean#L54-L55)

<pre title="Statement_Wire_3_5.lean, lines 54–55">
/-- Row B (P3:261-262): `c = 1/8`, `K_T = 11/2`, `K_S = 9/2`. -/
noncomputable def rowB : Prop := WireExponent3_5 (1 / 8) (11 / 2) (9 / 2)
</pre>

<pre title="Statement_Wire_3_5.lean, lines 47–52">
/-- `thm:tradeoff` (P3:225-238): one `E^NP` language, chosen before the multipliers `A_T, A_S`. -/
noncomputable def _root_.NearCubicWires.WireExponent3_5 (c KT KS : ℝ) : Prop :=
  ∃ language : Language,
    (∃ oracle : ℕ → Bool, Nonempty (EncodedNPVerifier oracle) ∧
        Nonempty (OrdinaryENPCertificate oracle language)) ∧
    WireExponent3_5Hard c KT KS language
</pre>

<pre title="Statement_Wire_3_5.lean, lines 26–45">
/-- The hardness half of `thm:tradeoff` for one language (P3:233-237): for every pair of fixed multipliers there
is an onset past which every capped circuit of either class has agreement below `1/2 + L(n)^{-c}`. -/
noncomputable def WireExponent3_5Hard (c KT KS : ℝ) (language : Language) : Prop :=
  ∀ AT AS : ℝ, 0 &lt; AT → 0 &lt; AS →
    ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n →
      (∀ circuit : ThresholdThresholdCircuit n,
        ((∑ i : Fin circuit.bottomCount,
            if circuit.topWeight i = 0 then 0
            else (circuit.bottom i).support.card + 1 : ℕ) : ℝ) ≤
          AT * (n : ℝ) ^ ((7 : ℝ) / 2) / (Nat.clog 2 (n + 2) : ℝ) ^ KT →
        ((Finset.univ.filter fun x =&gt; circuit.eval x = language n x).card : ℝ) /
            (Fintype.card (Fin n → Bool) : ℝ) &lt;
          1 / 2 + (Nat.clog 2 (n + 2) : ℝ) ^ (-c)) ∧
      (∀ circuit : SymmetricThresholdCircuit n,
        ((∑ i : Fin circuit.bottomCount,
            ((circuit.bottom i).support.card + 1) : ℕ) : ℝ) ≤
          AS * (n : ℝ) ^ ((7 : ℝ) / 2) / (Nat.clog 2 (n + 2) : ℝ) ^ KS →
        ((Finset.univ.filter fun x =&gt; circuit.eval x = language n x).card : ℝ) /
            (Fintype.card (Fin n → Bool) : ℝ) &lt;
          1 / 2 + (Nat.clog 2 (n + 2) : ℝ) ^ (-c))
</pre>

</td></tr>
<tr><td>
<b>paper/paper.tex, lines 209–213</b>
<pre>
A threshold gate outputs
$\ind[\sum_i a_i x_i\ge\theta]$, with arbitrary real weights in the
lower-bound statements. A symmetric gate applies an arbitrary Boolean
function to the number of its input ones. A circuit is strictly layered:
inputs feed threshold gates, which feed one threshold or symmetric gate.
</pre>
<b>paper/paper.tex, line 41</b>
<pre>
\newcommand{\ind}{\mathbf 1}
</pre>
</td><td>

[Statement.lean, lines 649–654](../Statement.lean#L649-L654)

<pre title="Statement.lean, line 641">
abbrev BitInput (n : ℕ) := Fin n → Bool
</pre>

<pre title="Statement.lean, line 643">
abbrev BoolFunction (n : ℕ) := BitInput n → Bool
</pre>

<pre title="Statement.lean, line 645">
abbrev Language := (n : ℕ) → BoolFunction n
</pre>

<pre title="Statement.lean, line 647">
def bitAsReal (bit : Bool) : ℝ := if bit then 1 else 0
</pre>

<pre title="Statement.lean, lines 649–654">
/-- A semantic threshold gate together with its exact retained support. -/
structure RealThresholdGate (n : ℕ) where
  weight : Fin n → ℝ
  threshold : ℝ
  support : Finset (Fin n)
  mem_support_iff : ∀ i, i ∈ support ↔ weight i ≠ 0
</pre>

<pre title="Statement.lean, lines 656–658">
noncomputable def RealThresholdGate.eval {n : ℕ} (gate : RealThresholdGate n)
    (input : BitInput n) : Bool :=
  decide (gate.threshold ≤ ∑ i, gate.weight i * bitAsReal (input i))
</pre>

[Statement.lean, lines 711–714](../Statement.lean#L711-L714)

<pre title="Statement.lean, lines 711–714">
structure SymmetricThresholdCircuit (n : ℕ) where
  bottomCount : ℕ
  bottom : Fin bottomCount → RealThresholdGate n
  top : ℕ → Bool
</pre>

<pre title="Statement.lean, lines 716–718">
noncomputable def SymmetricThresholdCircuit.eval {n : ℕ}
    (circuit : SymmetricThresholdCircuit n) (input : BitInput n) : Bool :=
  circuit.top ((Finset.univ.filter fun i =&gt; (circuit.bottom i).eval input).card)
</pre>

[Statement.lean, lines 720–724](../Statement.lean#L720-L724)

<pre title="Statement.lean, lines 720–724">
structure ThresholdThresholdCircuit (n : ℕ) where
  bottomCount : ℕ
  bottom : Fin bottomCount → RealThresholdGate n
  topWeight : Fin bottomCount → ℝ
  topThreshold : ℝ
</pre>

<pre title="Statement.lean, lines 726–729">
noncomputable def ThresholdThresholdCircuit.eval {n : ℕ}
    (circuit : ThresholdThresholdCircuit n) (input : BitInput n) : Bool :=
  decide (circuit.topThreshold ≤
    ∑ i, circuit.topWeight i * bitAsReal ((circuit.bottom i).eval input))
</pre>

</td></tr>
<tr><td>
<b>paper/paper.tex, lines 214–216</b>
<pre>
We count bottom-gate occurrences and all input-to-bottom and bottom-to-top
incidences. Parallel input incidences can be combined before applying an
algorithm; retaining them only increases the charged wire count.
</pre>
<b>paper/paper.tex, lines 318–319</b>
<pre>
A circuit with $G$ bottom-gate occurrences and simple input edges has
$W\le(n+1)G$ wires.
</pre>
</td><td>

The wire counts are written inside `WireExponent3_5Hard` (first row): for THR∘THR
`∑ i, if circuit.topWeight i = 0 then 0 else (circuit.bottom i).support.card + 1`, for SYM∘THR
`∑ i, ((circuit.bottom i).support.card + 1)`. The statement check below names both THR∘THR readings:

[StatementChecks/Wire_3_5_Readings.lean, lines 33–36](../StatementChecks/Wire_3_5_Readings.lean#L33-L36)

<pre title="StatementChecks/Wire_3_5_Readings.lean, lines 33–36">
/-- The statement's THR∘THR wire count, as `WireExponent3_5Hard` writes it. -/
noncomputable def thrStatementWires {n : ℕ} (circuit : ThresholdThresholdCircuit n) : ℕ :=
  ∑ i : Fin circuit.bottomCount,
    if circuit.topWeight i = 0 then 0 else (circuit.bottom i).support.card + 1
</pre>

<pre title="StatementChecks/Wire_3_5_Readings.lean, lines 29–31">
/-- The THR∘THR wire count with every top incidence counted, zero-weight tops included (P3:213-216, raw). -/
def thrRawWires {n : ℕ} (circuit : ThresholdThresholdCircuit n) : ℕ :=
  ∑ i : Fin circuit.bottomCount, ((circuit.bottom i).support.card + 1)
</pre>

</td></tr>
<tr><td>
<b>paper/paper.tex, lines 217–218</b>
<pre>
For Boolean functions on $n$ bits put
$\agr(F_n,C)=\Pr_{x\in\{0,1\}^n}[F_n(x)=C(x)]$.
</pre>
<b>paper/paper.tex, line 50</b>
<pre>
\newcommand{\agr}{\operatorname{agr}}
</pre>
</td><td>

Written inside `WireExponent3_5Hard` (first row) as the number of inputs `x` with `circuit.eval x = language n x`,
divided by `Fintype.card (Fin n → Bool)`, which is 2^n.

</td></tr>
<tr><td>
<b>paper/paper.tex, line 208</b>
<pre>
Let $L(n)=\lceil\log_2(n+2)\rceil$
</pre>
</td><td>

Written inside `WireExponent3_5Hard` (first row) as `Nat.clog 2 (n + 2)`, Mathlib's upper logarithm: the least `k`
with `n + 2 ≤ 2^k`.

</td></tr>
<tr><td>
<b>paper/paper.tex, lines 220–223</b>
<pre>
The class $\ENP$ is deterministic $2^{O(n)}$ time with an NP oracle,
the standard home of hard functions in the algorithm-to-lower-bound
framework: the language is explicitly computable there, though not
efficiently.
</pre>
</td><td>

[Statement.lean, lines 1572–1584](../Statement.lean#L1572-L1584)

<pre title="Statement.lean, lines 1572–1584">
/-- LOCAL NP witness for the actual numeric query predicate. Both ordinary
verifier time and witness length are polynomial in the ENCODED query length.
The input is binary code.bits; no unary numeric-code or prefix-count input. -/
structure EncodedNPVerifier (oracle : ℕ → Bool) where
  verifier : OrdinaryVerifier
  coefficient : ℕ
  coefficientPositive : 1 ≤ coefficient
  degree : ℕ
  correct : ∀ code : ℕ, oracle code = true ↔
    ∃ witness : List Bool,
      witness.length ≤ coefficient * (natBitLength code + 1) ^ degree ∧
      verifier.acceptsAt (coefficient * (natBitLength code + 1) ^ degree)
        code.bits witness
</pre>

<pre title="Statement.lean, lines 1586–1592">
structure OrdinaryENPCertificate (oracle : ℕ → Bool) (language : Language) where
  program : OrdinaryOracleProgram
  exponent : ℕ
  exponentPositive : 1 ≤ exponent
  computes : ∀ n (input : BitInput n),
    OrdinaryOracleRuns oracle program (List.ofFn input) (language n input).toNat.bits
      (2 ^ (exponent * max 1 n))
</pre>

[Statement.lean, lines 1561–1570](../Statement.lean#L1561-L1570)

<pre title="Statement.lean, lines 1561–1570">
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

[Statement.lean, line 56](../Statement.lean#L56)

<pre title="Statement.lean, line 56">
def natBitLength (value : ℕ) : ℕ := Nat.log 2 value + 1
</pre>

</td></tr>
</table>

The machine model under `EncodedNPVerifier` and `OrdinaryENPCertificate` (the verifier, the oracle program and their
steps) is the Theorem 2.5 repository's, shown on its
[page 7](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/7-refuter.md).

**What to check** (a few minutes):

1. The quantifier order: the language first, with its E^NP certificate; then both multipliers A_T, A_S > 0; then the
   onset; then n; then the circuits. So the language does not depend on A_T, A_S, and the onset may (“The language may
   depend on $c,K_T,K_S$, but not on $A_T,A_S$”). “Almost everywhere” is the onset quantifier.
2. One common language serves both circuit classes.
3. Row B's constants: `rowB` is `WireExponent3_5 (1 / 8) (11 / 2) (9 / 2)`, that is c = 1/8 (the advantage L^{-1/8}),
   K_T = 11/2 (the THR∘THR cap A_T n^{7/2}/L^{11/2}) and K_S = 9/2 (the SYM∘THR cap A_S n^{7/2}/L^{9/2}). They satisfy
   the theorem's conditions c > 0, K_T > 5 + 2c and K_S > 4 + 2c (`rowB_ledger_arithmetic`, below).
4. The implications: a cap on the wires, W(C) ≤ A·n^{7/2}/L^K, gives agreement strictly below 1/2 + L^{-c}. The powers
   are real powers (`Real.rpow`) of the natural numbers n and L, as `(n : ℝ) ^ ((7 : ℝ) / 2)` and
   `(Nat.clog 2 (n + 2) : ℝ) ^ KT`; L ≥ 1, so every power is positive.
5. The circuits: a bottom gate is a threshold gate with real weights whose `support` is exactly its set of
   nonzero-weight inputs (`mem_support_iff`). The symmetric top is an arbitrary function of the number of accepting
   bottom gates; the threshold top compares a real weighted sum of the bottom gates with a real threshold. Bottom gates
   are listed as occurrences, so a repeated gate is counted each time.
6. The wire count W(C): each bottom gate contributes its input incidences, `support.card`, and its incidence to the
   top, `+ 1`. This is the paper's count (“We count bottom-gate occurrences and all input-to-bottom and bottom-to-top
   incidences”), and the corollary “$W\le(n+1)G$” confirms that no further term per gate is added. Lean's count never
   exceeds the paper's for the same circuit (zero-weight inputs carry no incidence in Lean, and parallel input
   incidences are one weight), so a cap on Lean's count covers at least the circuits a cap on the paper's count covers.
   For THR∘THR the sum skips the bottom gates whose top weight is 0; `rowB_iff_raw` (below) proves that counting their
   incidences too gives the same theorem.
7. Agreement is the fraction of the 2^n inputs on which the circuit and the language agree.
8. L = ⌈log₂(n+2)⌉ is `Nat.clog 2 (n + 2)`.
9. E^NP: an oracle, a predicate on ℕ with an NP verifier (`EncodedNPVerifier`: witness length and verifier time
   polynomial in the bit length of the query), and a deterministic oracle program that computes the language within
   2^(e·max(1, n)) steps (`OrdinaryENPCertificate`). This is DTIME(2^{O(n)}) with an NP oracle, the definition used for
   Theorem 2.5.

**Documented deviations:** none.

Lean proves three statement checks; you need not read them.

- Row B is the instance of the general statement, and its constants satisfy the theorem's conditions:

  [StatementChecks/Wire_3_5.lean, lines 22–23](../StatementChecks/Wire_3_5.lean#L22-L23)

  [StatementChecks/Wire_3_5.lean, lines 25–31](../StatementChecks/Wire_3_5.lean#L25-L31)

- The THR∘THR wire count may include the bottom gates of top weight 0: the statement with every top incidence counted,
  `WireExponent3_5Raw`, is equivalent to row B.

  [StatementChecks/Wire_3_5_Readings.lean, lines 120–122](../StatementChecks/Wire_3_5_Readings.lean#L120-L122)

- The statement is not trivially true. `constant_language_fails` shows that no constant language satisfies row B's
  bound: a symmetric circuit with no bottom gates and a constant top agrees with it everywhere and has no wires, and
  1 ≥ 1/2 + L^{-1/8} once L ≥ 256.

  [StatementChecks/Wire_3_5.lean, lines 46–76](../StatementChecks/Wire_3_5.lean#L46-L76)

**Class:** literal.
