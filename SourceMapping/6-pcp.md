# 6. PCP: the short PCP of Murray and Williams, and CLW20 Lemma 3.11

The main theorems assume the Lean statements in the first rows of the two tables below: `mw20` is the short PCP in the
form of Murray and Williams (paper, §H.1 item 1), which they credit to Ben-Sasson and Viola, and `clw311` is CLW20
Lemma 3.11 (the two-query PCP of proximity, which CLW20 takes from CW19 and VW20; paper, §H.1 item 2). The other rows
show every definition those statements use. All of them are in `Statement.lean`, the same as on page 6 of the
Theorem 2.5 repository. In the docstrings, "Tier 1" is the proof's own multitape machine model (the `OrdinaryMachine`
section of `Statement.lean`) and "Tier 2" is Mathlib's standard `Turing.TM2` model. Every algorithm that the two
statements promise is stated in Tier 2.

Papers:
- C. D. Murray, R. R. Williams, "Circuit Lower Bounds for Nondeterministic Quasi-Polytime from a New Easy Witness
  Lemma", SIAM Journal on Computing 49(5), STOC18-300–STOC18-322 (2020), DOI 10.1137/18M1195887; open-access copy in
  MIT's repository DSpace (https://hdl.handle.net/1721.1/134017),
  https://dspace.mit.edu/server/api/core/bitstreams/fd66c806-f889-483b-ba4c-9ee9e99e2228/content. Page numbers refer
  to that PDF, SHA-256 b633f81dc40dc20ca011cdedf29bb43b290fa2ed678bd6628d84646267ca2fec. The statement is in Section 5,
  in the proof of Theorem 1.4, on the journal's pp. STOC18-316–STOC18-317, which are PDF pp. 18–19 (the PDF's first
  page is MIT's cover sheet).
- L. Chen, X. Lyu, R. R. Williams, "Almost-Everywhere Circuit Lower Bounds from Non-Trivial Derandomization", ECCC
  TR20-150 (2020), https://eccc.weizmann.ac.il/report/2020/150/download/. Page numbers refer to that PDF,
  SHA-256 d760d3b8349b5e4cc118595767069c778315dd18499650a5fcc1870b085bc02c.
- L. Chen, R. R. Williams, "Stronger Connections Between Circuit Analysis and Circuit Lower Bounds, via PCPs of
  Proximity", CCC 2019, https://doi.org/10.4230/LIPIcs.CCC.2019.19. Page numbers refer to that PDF,
  SHA-256 c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533.

## The short PCP of Murray and Williams (paper, §H.1 item 1)

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>MW20, PDF p. 18</b>
<pre>
In particular, for every verifier algorithm V(x, y) running in time T(n) ≥ n, they give
an algorithm A running in poly(n, log T(n)) time which, given x ∈ {0, 1}^n, outputs
an oracle circuit C^O_x with the following properties:^5
• C^O_x has ℓ = log_2(T(n)) + O(log log T(n)) inputs, poly(n, log T(n)) size, and
each copy of the oracle gate O in C^O_x has ℓ inputs as well.
…
^5This is not formally stated in their article, but it is immediate from their Theorem 1.1.
</pre>
<b>MW20, PDF p. 19</b>
<pre>
• If there is a y of length T(n) such that V(x, y) accepts, then there is an oracle
O : {0, 1}^ℓ → {0, 1} such that C^O_x is unsatisfiable.
• If V(x, y) rejects on all y of length T(n), then for every oracle O : {0, 1}^ℓ →
{0, 1}, C^O_x has at least 2^ℓ · (1 − 1/n) satisfying assignments.
</pre>
</td><td>

[Statement.lean, lines 2061–2100](../Statement.lean#L2061-L2100)

<pre title="Statement.lean, lines 2061–2100">
/-- **Input 6: the short PCP as an oracle circuit (Murray–Williams 2020, Section 5, in the proof of Theorem 1.4,
pp. STOC18-316–STOC18-317, PDF pp. 18–19)**, verbatim:
"for every verifier algorithm V(x, y) running in time T(n) ≥ n, they give an algorithm A running in
poly(n, log T(n)) time which, given x ∈ {0,1}^n, outputs an oracle circuit C^O_x with the following
properties:
• C^O_x has ℓ = log2(T(n)) + O(log log T(n)) inputs, poly(n, log T(n)) size, and each copy of the oracle
  gate O in C^O_x has ℓ inputs as well.
• If there is a y of length T(n) such that V(x, y) accepts, then there is an oracle O : {0,1}^ℓ → {0,1}
  such that C^O_x is unsatisfiable.
• If V(x, y) rejects on all y of length T(n), then for every oracle O : {0,1}^ℓ → {0,1}, C^O_x has at
  least 2^ℓ · (1 − 1/n) satisfying assignments."
Readings: the hidden constants are chosen after `V` and `T`; `T` is not assumed time-constructible, so `A`
receives `T(n)` in binary with `x`; `A` is a Mathlib polynomial-time TM2 machine (`Turing.TM2ComputableInPolyTime`);
the properties are claimed for `n ≥ 1` ("1/n"); `ℓ = log₂T + O(log log T)` is read as its upper half
`2^ℓ ≤ K·T·L(T)^e` with `L = logScale`. -/
def MW20_OracleCircuitPCP_TM2 : Prop :=
  ∀ (V : OrdinaryVerifier) (T : ℕ → ℕ), (∀ n, n ≤ T n) → RunsInTime V T →
  ∃ out : InputRequest → OracleOutput,
    -- "an algorithm A running in poly(n, log T(n)) time which, given x ∈ {0,1}^n, outputs an oracle
    -- circuit C^O_x"
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun x : InputRequest =&gt; frame (List.ofFn x.2) ++ frame (T x.1).bits)
      (fun w : List Bool =&gt; w) (fun x =&gt; (out x).word)) ∧
    -- "ℓ = log2(T(n)) + O(log log T(n)) inputs"
    (∃ K e : ℕ, ∀ x : InputRequest, 1 ≤ x.1 →
      2 ^ (out x).ell ≤ K * T x.1 * logScale (T x.1) ^ e) ∧
    -- "poly(n, log T(n)) size"
    (∃ K e : ℕ, ∀ x : InputRequest, 1 ≤ x.1 →
      (out x).circuit.size ≤ K * (x.1 + natBitLength (T x.1) + 1) ^ e) ∧
    -- "If there is a y of length T(n) such that V(x, y) accepts, then there is an oracle
    -- O : {0,1}^ℓ → {0,1} such that C^O_x is unsatisfiable."
    (∀ x : InputRequest, 1 ≤ x.1 →
      (∃ y : BitInput (T x.1), V.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∃ O : BitInput (out x).ell → Bool, ∀ z, (out x).circuit.eval O z = false) ∧
    -- "If V(x, y) rejects on all y of length T(n), then for every oracle O : {0,1}^ℓ → {0,1}, C^O_x has
    -- at least 2^ℓ · (1 − 1/n) satisfying assignments."
    (∀ x : InputRequest, 1 ≤ x.1 →
      (¬ ∃ y : BitInput (T x.1), V.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∀ O : BitInput (out x).ell → Bool,
        (2 : ℝ) ^ (out x).ell * (1 - 1 / (x.1 : ℝ)) ≤ ((out x).satCount O : ℝ))
</pre>

</td></tr>
<tr><td>
<b>MW20, PDF p. 18</b>
<pre>
for every verifier algorithm V(x, y) running in time T(n) ≥ n
</pre>
<b>MW20, PDF p. 19</b>
<pre>
If there is a y of length T(n) such that V(x, y) accepts
</pre>
<b>MW20, PDF p. 19</b>
<pre>
If V(x, y) rejects on all y of length T(n)
</pre>
</td><td>

[Statement.lean, lines 2055–2059](../Statement.lean#L2055-L2059)

<pre title="Statement.lean, lines 2055–2059">
/-- "every verifier algorithm V(x, y) running in time T(n)": on EVERY `(x, y)` with `|x| = n`, `V` halts within `T(n)`
steps. -/
def RunsInTime (V : OrdinaryVerifier) (T : ℕ → ℕ) : Prop :=
  ∀ n (x : BitInput n) (y : List Bool), ∃ receipt,
    run V.machine (T n) (V.inputTapes (List.ofFn x) y) = some receipt
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

<pre title="Statement.lean, lines 1339–1342">
def Verifier.acceptsAt (v : Verifier) (fuel : ℕ)
    (input witness : List Bool) : Prop :=
  ∃ receipt, run v.machine fuel (v.inputTapes input witness) = some receipt ∧
    v.accepting receipt.final.control = true
</pre>

<pre title="Statement.lean, lines 1344–1345">
def Verifier.accepts (v : Verifier) (input witness : List Bool) : Prop :=
  ∃ fuel, v.acceptsAt fuel input witness
</pre>

</td></tr>
<tr><td>
<b>MW20, PDF p. 18</b>
<pre>
outputs
an oracle circuit C^O_x
</pre>
<b>MW20, PDF p. 18</b>
<pre>
each copy of the oracle gate O in C^O_x has ℓ inputs as well.
</pre>

An oracle circuit is a Boolean circuit that may also contain gates computing O. Its nodes are those of the statement
file's general Boolean circuits (constants, inputs, NOT, fan-in-two AND and OR, in topological order, with a designated
output node; `BooleanCircuit`) and oracle gates, each wired to ℓ earlier nodes. An oracle gate outputs O applied to the
values of its ℓ argument nodes.
</td><td>

[Statement.lean, lines 1976–1985](../Statement.lean#L1976-L1985)

<pre title="Statement.lean, lines 1976–1985">
/-- One node of an oracle circuit on `n` inputs whose oracle gates have `arity` inputs: the nodes of
`BooleanCircuit` (constants, inputs, fan-in-two AND and OR, NOT) and one oracle gate, whose `arity` argument
wires are earlier nodes. -/
inductive OracleNode (n arity : ℕ) where
  | const (value : Bool)
  | input (index : Fin n)
  | not (child : ℕ)
  | and (left right : ℕ)
  | or (left right : ℕ)
  | oracle (args : Fin arity → ℕ)
</pre>

<pre title="Statement.lean, lines 1987–1994">
/-- Every child of the node at position `index` precedes it. -/
def OracleNode.WellFormedAt {n arity : ℕ} (index : ℕ) : OracleNode n arity → Prop
  | .const _ =&gt; True
  | .input _ =&gt; True
  | .not child =&gt; child &lt; index
  | .and left right =&gt; left &lt; index ∧ right &lt; index
  | .or left right =&gt; left &lt; index ∧ right &lt; index
  | .oracle args =&gt; ∀ j, args j &lt; index
</pre>

<pre title="Statement.lean, lines 1996–2005">
/-- The value of a node, given the values `prior` of the earlier nodes; an oracle gate returns
`O` applied to the values of its argument wires. -/
def OracleNode.eval {n arity : ℕ} (O : BitInput arity → Bool) (input : BitInput n)
    (prior : Array Bool) : OracleNode n arity → Bool
  | .const value =&gt; value
  | .input index =&gt; input index
  | .not child =&gt; !(prior[child]?.getD false)
  | .and left right =&gt; prior[left]?.getD false &amp;&amp; prior[right]?.getD false
  | .or left right =&gt; prior[left]?.getD false || prior[right]?.getD false
  | .oracle args =&gt; O fun j =&gt; prior[args j]?.getD false
</pre>

<pre title="Statement.lean, lines 2007–2012">
/-- "an oracle circuit C^O": a topologically ordered DAG of `OracleNode`s with a designated output node,
exactly like `BooleanCircuit`, plus oracle gates of arity `arity`. -/
structure OracleCircuit (n arity : ℕ) where
  nodes : List (OracleNode n arity)
  output : Fin nodes.length
  wellFormed : ∀ index : Fin nodes.length, (nodes.get index).WellFormedAt index.val
</pre>

<pre title="Statement.lean, lines 2014–2017">
/-- The values of all nodes of `C^O` on `input`. -/
def OracleCircuit.values {n arity : ℕ} (C : OracleCircuit n arity) (O : BitInput arity → Bool)
    (input : BitInput n) : Array Bool :=
  C.nodes.foldl (fun prior node =&gt; prior.push (node.eval O input prior)) #[]
</pre>

<pre title="Statement.lean, lines 2019–2022">
/-- `C^O(input)`. -/
def OracleCircuit.eval {n arity : ℕ} (C : OracleCircuit n arity) (O : BitInput arity → Bool)
    (input : BitInput n) : Bool :=
  (C.values O input)[C.output.val]?.getD false
</pre>

<pre title="Statement.lean, lines 2024–2026">
/-- The size: the number of nodes (input, constant and oracle nodes included), as `BooleanCircuit.size`. -/
def OracleCircuit.size {n arity : ℕ} (C : OracleCircuit n arity) : ℕ :=
  C.nodes.length
</pre>

</td></tr>
<tr><td>
<b>MW20, PDF p. 18</b>
<pre>
C^O_x has ℓ = log_2(T(n)) + O(log log T(n)) inputs, poly(n, log T(n)) size
</pre>
<b>MW20, PDF p. 19</b>
<pre>
C^O_x is unsatisfiable
</pre>
<b>MW20, PDF p. 19</b>
<pre>
C^O_x has at least 2^ℓ · (1 − 1/n) satisfying assignments.
</pre>
</td><td>

[Statement.lean, lines 2039–2043](../Statement.lean#L2039-L2043)

<pre title="Statement.lean, lines 2039–2043">
/-- "an oracle circuit C^O_x" with "ℓ inputs", "each copy of the oracle gate O in C^O_x has ℓ inputs as
well": the number `ℓ` and the circuit. -/
structure OracleOutput where
  ell : ℕ
  circuit : OracleCircuit ell ell
</pre>

<pre title="Statement.lean, lines 2051–2053">
/-- The number of satisfying assignments of `C^O`. -/
def OracleOutput.satCount (o : OracleOutput) (O : BitInput o.ell → Bool) : ℕ :=
  (Finset.univ.filter fun z : BitInput o.ell =&gt; o.circuit.eval O z = true).card
</pre>

</td></tr>
<tr><td>
<b>MW20, PDF p. 18</b>
<pre>
they give
an algorithm A running in poly(n, log T(n)) time which, given x ∈ {0, 1}^n, outputs
an oracle circuit C^O_x
</pre>

A outputs the oracle circuit as a word: each node is framed in the statement file's `natWord` code, an oracle gate as
tag 5 followed by its ℓ argument indices. A reads x framed and T(n) framed in binary (`InputRequest`, `frame`).
</td><td>

[Statement.lean, lines 2028–2037](../Statement.lean#L2028-L2037)

<pre title="Statement.lean, lines 2028–2037">
/-- The word of a node, in the native three-field form of the Boolean nodes (tag, then two numbers, `0` when unused:
`0` constant, `1` input, `2` NOT, `3` AND, `4` OR); an oracle gate is tag `5` followed by its `arity` argument wires.
Every field is a self-delimiting `natWord`. -/
def oracleNodeWord {n arity : ℕ} : OracleNode n arity → List Bool
  | .const value =&gt; natWord 0 ++ natWord value.toNat ++ natWord 0
  | .input index =&gt; natWord 1 ++ natWord index.val ++ natWord 0
  | .not child =&gt; natWord 2 ++ natWord child ++ natWord 0
  | .and left right =&gt; natWord 3 ++ natWord left ++ natWord right
  | .or left right =&gt; natWord 4 ++ natWord left ++ natWord right
  | .oracle args =&gt; natWord 5 ++ (List.ofFn fun j =&gt; natWord (args j)).flatten
</pre>

<pre title="Statement.lean, lines 2045–2049">
/-- The output word: `ℓ` (the number of inputs and the oracle arity), the number of nodes, the node words in order,
then the output address. -/
def OracleOutput.word (o : OracleOutput) : List Bool :=
  natWord o.ell ++ natWord o.circuit.nodes.length ++ o.circuit.nodes.flatMap oracleNodeWord ++
    natWord o.circuit.output.val
</pre>

[Statement.lean, line 1411](../Statement.lean#L1411)

<pre title="Statement.lean, line 1411">
abbrev InputRequest := Σ n : ℕ, BitInput n
</pre>

[Statement.lean, lines 1304–1306](../Statement.lean#L1304-L1306)

<pre title="Statement.lean, lines 1304–1306">
def frame : List Bool → List Bool
  | [] =&gt; [false]
  | b :: bs =&gt; true :: b :: frame bs
</pre>

</td></tr>
</table>

**The paper.** §H.1 item 1 quotes this statement and reads it, as the Lean statement does, for deterministic
multitape verifiers V, with T(n) given to A in binary together with x. Handing T(n) to A in binary claims less than
MW20's sentence: an algorithm that ignores the extra input satisfies it. The paper applies the statement once, to the
succinct hierarchy verifier of Lemma H.6, whose explicit inputs are short descriptions of circuits; the outer step built
on it is Lemma H.7.

**What to check for input 6** (a few minutes):

1. The order: for every Tier 1 verifier V (deterministic multitape, with x and y framed on tapes 0 and 1) and every
   T with T(n) ≥ n such that V halts within T(n) steps on every (x, y) with |x| = n, y of any length
   (`RunsInTime`), there are constants K, e and one Tier 2 algorithm A.
2. A reads x and T(n) in binary and runs in time polynomial in its input length, which is Θ(n + log T(n)); this is
   MW20's poly(n, log T(n)).
3. Only the upper half of ℓ = log₂T(n) + O(log log T(n)) is claimed: 2^ℓ ≤ K·T(n)·logScale(T(n))^e for n ≥ 1, and ℓ
   may depend on x. Finitely many small n are absorbed by K.
4. The oracle circuit has at most K·(n + bitlen T(n) + 1)^e nodes, inputs included, over fan-in-two AND, OR and NOT
   and ℓ-ary oracle gates: MW20's poly(n, log T(n)) size up to a polynomial change of basis.
5. Completeness and soundness are claimed for n ≥ 1, with "1/n" for n = |x| and y of length exactly T(n);
   "rejects" is read as "does not accept", which is the same thing because V halts.
6. Nothing bounds the number of oracle queries, and the soundness error is 1/n. Input 6 is an assumption of the main
   theorems, as are the other eight inputs.

**Adapter.** `mwSource_of_literal` carries the literal into the form the proof uses (the algorithm becomes an
ordinary word function of the repository's machine model, by the same Tier 2 → Tier 1 simulation as the other
bindings).

[Outer/Source.lean, lines 62–83](../Outer/Source.lean#L62-L83)

**Version 1.** Version 1 of this repository assumed the short PCP in the form of CLW20 Lemma 3.10, after Ben-Sasson and
Viola's Theorem 1.1. This version assumes the form of Murray and Williams instead, which their footnote 5 (first row)
calls immediate from the same theorem.

## Lemma 3.11: the two-query PCP of proximity

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
Lemma 3.11 ([CW19, VW20]). There are constants 0 &lt; s_pcpp &lt; c_pcpp &lt; 1 and a polynomial-time
transformation that, given a circuit D on n inputs of size m ≥ n, outputs a 2-SAT instance F on the
variable set Y ∪ Z where |Y| ≤ poly(n), |Z| ≤ poly(m), and the following hold for all x ∈ {0, 1}^n:
• If D(x) = 1, then F|Y=Enc(x) on variable set Z has a satisfying assignment Z_x such that at least
c_pcpp-fraction of the clauses are satisfied. Furthermore, there is a poly(m) time algorithm that given
x outputs Z_x.
• If D(x) = 0, then there is no assignment to the Z variables in F|Y=Enc(x) satisfies more than s_pcpp-
fraction of the clauses.
Moreover, the number of clauses in the 2-SAT instance F is a power of 2, and for each i ∈ [|Y|], Enc_i(x)
is a parity function depending on at most n/2 bits of x.
</pre>
</td><td>

[Statement.lean, lines 2520–2521](../Statement.lean#L2520-L2521)

<pre title="Statement.lean, lines 2520–2521">
/-- CLW20 Lemma 3.11 with `n ≥ 2` and the explicit-Enc output (Tier 2), the target form. -/
def CLW20_Lemma3_11_explicitEnc_TM2 : Prop := lemma3_11CoreTM2 2 (fun _ F =&gt; F.formulaEncWord)
</pre>

<pre title="Statement.lean, lines 2493–2518">
/-- CLW20 Lemma 3.11 (PDF p.18) on circuits with at least `n₀` inputs, with the transformation's
output word `outputWord`, the two algorithms in Mathlib's TM2 model. The conjuncts follow the
printed order, as in the Tier 1 `lemma3_11Core`. -/
def lemma3_11CoreTM2 (n₀ : ℕ) (outputWord : (n : ℕ) → Instance n → List Bool) : Prop :=
  ∃ s c : ℝ, 0 &lt; s ∧ s &lt; c ∧ c &lt; 1 ∧
  ∃ F : (C : CircuitFrom n₀) → Instance C.1.n,
    -- "a polynomial-time transformation that, given a circuit D …, outputs … F" (Tier 2)
    Nonempty (Turing.TM2ComputableInPolyTime (fun C : CircuitFrom n₀ =&gt; C.1.word)
      (fun w : List Bool =&gt; w) (fun C =&gt; outputWord C.1.n (F C))) ∧
    -- "|Y| ≤ poly(n)"
    (∃ K e : ℕ, ∀ C, (F C).Ybits ≤ K * (C.1.n + 1) ^ e) ∧
    -- "|Z| ≤ poly(m)"
    (∃ K e : ℕ, ∀ C, (F C).Zbits ≤ K * (C.1.m + 1) ^ e) ∧
    ∃ Zx : (C : CircuitFrom n₀) → BitInput C.1.n → BitInput (F C).Zbits,
      -- "If D(x) = 1, then F|Y=Enc(x) … has … Z_x such that at least c-fraction of the clauses
      -- are satisfied."
      (∀ C x, C.1.D.eval x = true → (F C).fraction x (Zx C x) ≥ c) ∧
      -- "there is a poly(m) time algorithm that given x outputs Z_x" (Tier 2)
      Nonempty (Turing.TM2ComputableInPolyTime
        (fun p : (Σ C : CircuitFrom n₀, BitInput C.1.n) =&gt; p.1.1.word ++ List.ofFn p.2)
        (fun w : List Bool =&gt; w) (fun p =&gt; List.ofFn (Zx p.1 p.2))) ∧
      -- "If D(x) = 0, then there is no assignment to the Z variables in F|Y=Enc(x) [that]
      -- satisfies more than s-fraction of the clauses."
      (∀ C x, C.1.D.eval x = false → ∀ z, (F C).fraction x z ≤ s) ∧
      -- "for each i ∈ [|Y|], Enc_i(x) is a parity function depending on at most n/2 bits of x"
      (∀ C i, ((F C).encSupport i).card ≤ C.1.n / 2)
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
given a circuit D on n inputs of size m ≥ n
</pre>
</td><td>

[Statement.lean, lines 2145–2149](../Statement.lean#L2145-L2149)

<pre title="Statement.lean, lines 2145–2149">
/-- "a circuit D on n inputs of size m ≥ n". -/
structure Circuit where
  n : ℕ
  D : BooleanCircuit n
  sizeAtLeast : n ≤ D.size
</pre>

<pre title="Statement.lean, lines 2151–2152">
/-- The size `m` of `D`: its number of nodes. -/
def Circuit.m (C : Circuit) : ℕ := C.D.size
</pre>

<pre title="Statement.lean, lines 2154–2155">
/-- The circuits the lemma is read on: those with at least `n₀` inputs. -/
abbrev CircuitFrom (n₀ : ℕ) := {C : Circuit // n₀ ≤ C.n}
</pre>

<pre title="Statement.lean, lines 2157–2159">
/-- Tier 1: the circuit as the transformation reads it (the import's `pcppInput` layout). -/
def Circuit.word (C : Circuit) : List Bool :=
  natWord C.n ++ (encodeBooleanCircuit C.D).bits
</pre>

[Statement.lean, lines 659–668](../Statement.lean#L659-L668)

<pre title="Statement.lean, lines 659–668">
/-- One node in a topologically ordered fan-in-two Boolean DAG.  Child
references are natural-number node addresses; `BooleanCircuit.wellFormed`
requires every child to precede the node that uses it. -/
inductive BooleanNode (n : ℕ) where
  | const (value : Bool)
  | input (index : Fin n)
  | not (child : ℕ)
  | and (left right : ℕ)
  | or (left right : ℕ)
  deriving Repr
</pre>

<pre title="Statement.lean, lines 670–676">
def BooleanNode.WellFormedAt {n : ℕ} (index : ℕ) :
    BooleanNode n → Prop
  | .const _ =&gt; True
  | .input _ =&gt; True
  | .not child =&gt; child &lt; index
  | .and left right =&gt; left &lt; index ∧ right &lt; index
  | .or left right =&gt; left &lt; index ∧ right &lt; index
</pre>

<pre title="Statement.lean, lines 678–686">
def BooleanNode.eval {n : ℕ} (input : BitInput n)
    (prior : Array Bool) : BooleanNode n → Bool
  | .const value =&gt; value
  | .input index =&gt; input index
  | .not child =&gt; !(prior[child]?.getD false)
  | .and left right =&gt;
      prior[left]?.getD false &amp;&amp; prior[right]?.getD false
  | .or left right =&gt;
      prior[left]?.getD false || prior[right]?.getD false
</pre>

<pre title="Statement.lean, lines 688–696">
/-- Ordinary Boolean circuits are finite DAGs with a topological node order.
Gate count—not formula-tree unfolding—is the source theorem's size measure. -/
structure BooleanCircuit (n : ℕ) where
  nodes : List (BooleanNode n)
  output : Fin nodes.length
  wellFormed :
    ∀ index : Fin nodes.length,
      (nodes.get index).WellFormedAt index.val
  deriving Repr
</pre>

<pre title="Statement.lean, lines 698–701">
def BooleanCircuit.values {n : ℕ} (circuit : BooleanCircuit n)
    (input : BitInput n) : Array Bool :=
  circuit.nodes.foldl
    (fun prior node =&gt; prior.push (node.eval input prior)) #[]
</pre>

<pre title="Statement.lean, lines 703–705">
def BooleanCircuit.eval {n : ℕ} (circuit : BooleanCircuit n)
    (input : BitInput n) : Bool :=
  (circuit.values input)[circuit.output.val]?.getD false
</pre>

<pre title="Statement.lean, lines 707–708">
def BooleanCircuit.size {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  circuit.nodes.length
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
outputs a 2-SAT instance F on the
variable set Y ∪ Z
</pre>
<b>CLW20, PDF p. 18</b>
<pre>
Moreover, the number of clauses in the 2-SAT instance F is a power of 2, and for each i ∈ [|Y|], Enc_i(x)
is a parity function depending on at most n/2 bits of x.
</pre>
</td><td>

[Statement.lean, lines 2161–2171](../Statement.lean#L2161-L2171)

<pre title="Statement.lean, lines 2161–2171">
/-- "a 2-SAT instance F on the variable set Y ∪ Z", together with `Enc`.
`Ybits = |Y|` and `Zbits = |Z|`, and the Y variables are the indices below `|Y|`.
"the number of clauses in the 2-SAT instance F is a power of 2": there are `2 ^ clauseBits`
clauses, and each one is an OR of two literals.
"Enc_i(x) is a parity function": `Enc_i(x)` is the XOR of `x` over `encSupport i`. -/
structure Instance (n : ℕ) where
  Ybits : ℕ
  Zbits : ℕ
  clauseBits : ℕ
  clauses : Fin (2 ^ clauseBits) → TwoLiteralClause (Ybits + Zbits)
  encSupport : Fin Ybits → Finset (Fin n)
</pre>

<pre title="Statement.lean, lines 2173–2175">
/-- `Enc(x) ∈ {0,1}^|Y|`, with `Enc_i(x) = ⊕_{j ∈ encSupport i} x_j`. -/
noncomputable def Instance.enc {n : ℕ} (F : Instance n) (x : BitInput n) : BitInput F.Ybits :=
  fun i =&gt; parityOn (F.encSupport i) x
</pre>

<pre title="Statement.lean, lines 2177–2180">
/-- The assignment behind "F|Y=Enc(x)" with the Z variables set to `z`. -/
noncomputable def Instance.restrict {n : ℕ} (F : Instance n) (x : BitInput n)
    (z : BitInput F.Zbits) : BitInput (F.Ybits + F.Zbits) :=
  Fin.addCases (F.enc x) z
</pre>

<pre title="Statement.lean, lines 2182–2186">
/-- The fraction of the clauses of `F|Y=Enc(x)` that the Z-assignment `z` satisfies. -/
noncomputable def Instance.fraction {n : ℕ} (F : Instance n) (x : BitInput n)
    (z : BitInput F.Zbits) : ℝ :=
  ((Finset.univ.filter fun i =&gt; (F.clauses i).eval (F.restrict x z)).card : ℝ) /
    (2 ^ F.clauseBits : ℝ)
</pre>

[Statement.lean, lines 1012–1014](../Statement.lean#L1012-L1014)

<pre title="Statement.lean, lines 1012–1014">
noncomputable def parityOn {n : ℕ} (support : Finset (Fin n))
    (input : BitInput n) : Bool :=
  support.toList.foldl (fun parity i =&gt; xor parity (input i)) false
</pre>

[Statement.lean, lines 1004–1006](../Statement.lean#L1004-L1006)

<pre title="Statement.lean, lines 1004–1006">
structure TwoLiteralClause (arity : ℕ) where
  left : Literal arity
  right : Literal arity
</pre>

<pre title="Statement.lean, lines 1008–1010">
def TwoLiteralClause.eval {arity : ℕ} (clause : TwoLiteralClause arity)
    (assignment : BitInput arity) : Bool :=
  clause.left.eval assignment || clause.right.eval assignment
</pre>

</td></tr>
</table>

Subscripts are written with `_` (`s_pcpp` is s<sub>pcpp</sub>), and the restriction bar is written `F|Y=Enc(x)`.

**What to check** (a few minutes):

1. The order is the paper's: first the constants s and c with 0 < s < c < 1, then the transformation F (one instance
   for each circuit), then the polynomial bounds. Each bound has its own constants K and e, chosen after F: the weakest
   reading of the hidden constants.
2. The transformation is a Tier 2 machine (`Turing.TM2ComputableInPolyTime`) from the circuit's word (`Circuit.word`:
   n, then the repository's canonical code of D) to the instance's word. Its time is polynomial in the input length.
3. |Y| ≤ K·(n+1)^e and |Z| ≤ K·(m+1)^e, where m is the number of nodes of D (`Circuit.m`), input nodes included.
   So "m ≥ n" holds for every circuit; a circuit with fewer than n gates is covered by padding it with dummy gates,
   which at most doubles m.
4. Completeness: if D(x) = 1, then Z_x satisfies at least a c fraction of the clauses (the reading of "a satisfying
   assignment Z_x such that at least c-fraction of the clauses are satisfied"). `Instance.fraction` sets the Y
   variables to Enc(x) and the Z variables to z, counts the satisfied clauses, and divides by their number.
5. “there is a poly(m) time algorithm that given x outputs Z_x” is one Tier 2 polynomial-time machine on pairs (D, x),
   the same machine for every D. If the algorithm could depend on D, the clause would say nothing, because a machine
   built for one D computes any function of x by table lookup. Its input has length at most K·(m+1)^10
   (`zxInput_length_le`), so the machine is polynomial in m, as the proof needs. Conversely the input has length at
   least m, so a poly(m)-time algorithm runs in time polynomial in the input length; CW19 gives one uniformly in the
   circuit ("Given the pair (C, w) ∈ Circuit-Eval, a proof π can be constructed in poly(|C| + |w|) time", Lemma 25(2)).
6. Soundness: if D(x) = 0, every z satisfies at most an s fraction of the clauses.
7. “Moreover”: there are 2^k clauses for some k (`clauseBits`, part of the type `Instance`). Enc_i(x) is the parity of x
   on the set `encSupport i`, which has at most n/2 elements (division in ℕ, so ⌊n/2⌋). Enc may depend on D, because the
   sentence does not fix Enc before D.

**Two readings.**

*First: n ≥ 2.* The hypothesis is stated for circuits D on n ≥ 2 inputs (`lemma3_11CoreTM2 2`), a special case of the
printed lemma. This is the range of the code that gives the “at most n/2 bits” property in CW19, one of the two papers
CLW20 cite for Lemma 3.11. CW19 Lemma 27 splits the message into three parts, so each codeword bit depends on at most
⌈n/3⌉ input bits, and ⌈n/3⌉ ≤ ⌊n/2⌋ exactly when n ≥ 2 or n = 0:

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>CW19, PDF p. 16</b>
<pre>
Lemma 27. There is a constant δ &gt; 0 such that there is a constant-rate linear error
correcting code ECC with minimum relative distance δ, an efficient encoder Enc and an
efficient decoder Dec recovering error up to c1 · δ, where c1 is a universal constant. Moreover,
each bit of the codeword depends on at most n/2 bits of the input.
Proof. Given a message x ∈ {0, 1}^n, we split it into three parts x1, x2, x3, each of length
between ⌊n/3⌋ and ⌈n/3⌉. Let Enc′ and Dec′ be the corresponding encoder and decoder of
Lemma 26.
We construct our new error correcting code by setting Enc(x) := Enc′(x1) ◦ Enc′(x2) ◦
Enc′(x3).
</pre>
</td><td>

[Bindings/CLW20_Lemma3_11.lean, lines 240–243](../Bindings/CLW20_Lemma3_11.lean#L240-L243)

<pre title="Bindings/CLW20_Lemma3_11.lean, lines 240–243">
/-- CW19 Lemma 27's split supports `n ≥ 2`: a third, rounded up, is at most a half, rounded
down, for every `n ≥ 2` (and `n = 0`). At `n = 1` it fails (`1 &gt; 0`). -/
theorem ceil_third_le_floor_half (n : ℕ) : (n + 2) / 3 ≤ n / 2 ↔ 2 ≤ n ∨ n = 0 := by
  omega
</pre>

</td></tr>
</table>

*Second: the encoder is written out.* The printed transformation “outputs a 2-SAT instance F” (`Instance.formulaWord`).
The hypothesis asks it to output the support of every Enc_i as well (`Instance.formulaEncWord`), because the proof needs
the supports and they cannot be recovered from F. The papers support the addition: CLW20's own algorithm enumerates the
bits that Enc_s depends on, and CW19's encoder is linear and efficient. A linear code with an efficient encoder has
computable supports: j is in the support of Enc_i exactly when bit i of Enc(e_j) is 1. Lean does not derive this
addition from the printed lemma; it rests on the sentences below.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>CLW20, PDF p. 28</b>
<pre>
Recall that Enc : {0, 1}^ℓ → {0, 1}^{|Y|} is the fixed F2-linear error correcting code
used in Lemma 3.11.
</pre>
<b>CLW20, PDF p. 29</b>
<pre>
Enc_s(x) depends on at most ℓ/2 bits (the moreover part
of Lemma 3.11). We can then enumerate all these bits
</pre>
<b>CW19, PDF p. 16</b>
<pre>
an efficient encoder Enc
</pre>
</td><td>

[Bindings/CLW20_Lemma3_11.lean, lines 122–127](../Bindings/CLW20_Lemma3_11.lean#L122-L127)

<pre title="Bindings/CLW20_Lemma3_11.lean, lines 122–127">
/-- Tier 1 output word of the literal: `F` alone (the counts, then every clause as two literal
indices). -/
def Instance.formulaWord {n : ℕ} (F : Instance n) : List Bool :=
  natListWord [F.Ybits, F.Zbits, F.clauseBits] ++
    natListWord ((List.ofFn fun i : Fin (2 ^ F.clauseBits) =&gt;
      [literalIndex (F.clauses i).left, literalIndex (F.clauses i).right]).flatten)
</pre>

<pre title="Statement.lean, lines 2188–2195">
/-- Tier 1 output word of the explicit-Enc reading: `F` with the support of every `Enc_i`
listed between the counts and the clauses (the import's `pcppOutput` layout). -/
def Instance.formulaEncWord {n : ℕ} (F : Instance n) : List Bool :=
  natListWord [F.Ybits, F.Zbits, F.clauseBits] ++
    (List.ofFn (fun i : Fin F.Ybits =&gt;
      List.ofFn (fun j : Fin n =&gt; decide (j ∈ F.encSupport i)))).flatten ++
    natListWord ((List.ofFn fun i : Fin (2 ^ F.clauseBits) =&gt;
      [literalIndex (F.clauses i).left, literalIndex (F.clauses i).right]).flatten)
</pre>

</td></tr>
</table>

Lean also proves that this statement gives what the proof uses (`clw20_lemma3_11_explicitEnc_tm2_to_import`); you need
not read it.

[Bindings/CLW20_Lemma3_11_TM2.lean, lines 132–135](../Bindings/CLW20_Lemma3_11_TM2.lean#L132-L135)

**Class:** the Murray–Williams short PCP (input 6) is literal plus one reading (the algorithm also receives T(n) in
binary), with its algorithm in Tier 2 (the verifier V it quantifies over stays in Tier 1). Lemma 3.11 is literal for
n ≥ 2, with the encoder's supports in the output, and both of its algorithms in Tier 2.
