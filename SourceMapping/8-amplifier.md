# 8. Amplifier: CLW20 Lemma 3.9 (STV01 Theorem 24) at the functions S(n) ≥ n^c

The main theorems assume the Lean statement in the first row of the table below (`clw39 : CLW20_Lemma3_9_TM2_Large`,
defined in `Statement_Wire_3_5.lean`). It is CLW20 Lemma 3.9, worst-case to average-case hardness amplification, which
CLW20 takes from Sudan, Trevisan and Vadhan (STV01, Theorem 24), with its constant c, at the time-constructible
functions S with S(n) ≥ n^c for every n. This is the regime in which STV01 state the parameters of their construction
(input length ℓ < s^γ; quoted below the table), and it contains the functions the proof uses (paper, §H.1 item 4:
"We use it for time-constructible sizes S(q) ≥ q^{c_STV}"). Hypothesis 9 is a special case of the printed lemma: the
last row shows `lemma3_9_large_of_literal`, which derives it from `CLW20_Lemma3_9_TM2`, the transcription of the printed
lemma in `Statement.lean`. The other rows show every definition the statement uses; they are definitions of
`Statement.lean`, the same as on page 8 of the Theorem 2.5 repository. In the docstrings, "Tier 1" is the proof's own
multitape machine model (the `OrdinaryMachine` section of `Statement.lean`) and "Tier 2" is Mathlib's standard
`Turing.TM2` model. The algorithm the lemma promises is stated in Tier 2 (`Turing.TM2ComputableInTime`).

Papers:
- L. Chen, X. Lyu, R. R. Williams, "Almost-Everywhere Circuit Lower Bounds from Non-Trivial Derandomization", ECCC
  TR20-150 (2020), https://eccc.weizmann.ac.il/report/2020/150/download/. Page numbers refer to that PDF,
  SHA-256 d760d3b8349b5e4cc118595767069c778315dd18499650a5fcc1870b085bc02c.
- (STV01) M. Sudan, L. Trevisan, S. Vadhan, "Pseudorandom Generators without the XOR Lemma", Journal of Computer and
  System Sciences 62 (2001) 236–266, https://doi.org/10.1006/jcss.2000.1730. Page numbers refer to that PDF,
  SHA-256 5517c11166fd93a05e6fddcb9f986b8d1b7ac103925a843d366e16568fdb1e94. Its text layer garbles the symbols, so its
  quotations were checked against the page image.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
Lemma 3.9 ([STV01]). There is a constant c ≥ 1 such that, for any time-constructible function S(n)
and every f : {0, 1}^n → {0, 1} that does not have (general) circuits of size S(n). There is a function
g : {0, 1}^{O(n)} → {0, 1} that cannot be (1/2 + S(n)^{−1/c})-approximated by circuits of size S(n)^{1/c}. Furthermore,
given the 2^n-length truth table of f, the truth table of g can be constructed in 2^{O(n)}
time.
</pre>

Hypothesis 9 is this statement, with the same constant c, for the time-constructible S with S(n) ≥ n^c for every n.
`CLW20_Lemma3_9_TM2`, shown for comparison, is the printed statement for every time-constructible S.
</td><td>

[Statement_Wire_3_5.lean, lines 71–79](../Statement_Wire_3_5.lean#L71-L79)

<pre title="Statement_Wire_3_5.lean, lines 71–79">
/-- **Input 9**: CLW20 Lemma 3.9 ("There is a constant c ≥ 1 such that, for any time-constructible function S(n) and every
f : {0,1}^n → {0,1} that does not have (general) circuits of size S(n). There is a function g : {0,1}^{O(n)} → {0,1} that
cannot be (1/2 + S(n)^{−1/c})-approximated by circuits of size S(n)^{1/c}. Furthermore, given the 2^n-length truth table
of f, the truth table of g can be constructed in 2^{O(n)} time.") at the functions `S(n) ≥ n^c`: the regime in which
STV01 state the parameters of its source, Theorem 24 (`ℓ &lt; s^γ`). -/
def CLW20_Lemma3_9_TM2_Large : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ S : ℕ → ℕ, NearCubicWires.SourceInterfaces.TimeConstructible S →
    (∀ n : ℕ, (n : ℝ) ^ c ≤ (S n : ℝ)) →
    Nonempty (NearCubicWires.Bindings.CLW20Lemma39TM2.Lemma3_9AtTM2 c S)
</pre>

[Statement.lean, lines 2248–2251](../Statement.lean#L2248-L2251)

<pre title="Statement.lean, lines 2248–2251">
/-- **CLW20 Lemma 3.9, literal (Tier 2).** "There is a constant c ≥ 1 such that, for any
time-constructible function S(n) and every f ..." -/
def CLW20_Lemma3_9_TM2 : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ S : ℕ → ℕ, TimeConstructible S → Nonempty (Lemma3_9AtTM2 c S)
</pre>

<pre title="Statement.lean, lines 2228–2246">
/-- What the sentence asserts for one constant `c` and one time-constructible `S` (Tier 2). All
fields but `construction` are those of the Tier 1 `Lemma3_9At`. -/
structure Lemma3_9AtTM2 (c : ℝ) (S : ℕ → ℕ) where
  /-- `g` for the input `f` on `n` bits. -/
  g : (n : ℕ) → BoolFunction n → AmplifierOutput
  /-- The hidden constant of `O(n)`. -/
  arityFactor : ℕ
  /-- The hidden onset of `O(n)`. -/
  arityOnset : ℕ
  /-- "every f ... that does not have (general) circuits of size S(n). There is a function
  g : {0,1}^{O(n)} → {0,1} that cannot be (1/2 + S(n)^{−1/c})-approximated by circuits of size
  S(n)^{1/c}." -/
  amplifies : ∀ (n : ℕ) (f : BoolFunction n), ¬ HasCircuitOfSize f (S n) →
    (arityOnset ≤ n → (g n f).arity ≤ arityFactor * n) ∧
    CannotBeApproximated (g n f).function
      ((S n : ℝ) ^ (-(1 : ℝ) / c)) ((S n : ℝ) ^ ((1 : ℝ) / c))
  /-- "Furthermore, given the 2^n-length truth table of f, the truth table of g can be
  constructed in 2^{O(n)} time." (Tier 2: Mathlib's TM2 model.) -/
  construction : TruthTableConstructionTM2 g
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
g : {0, 1}^{O(n)} → {0, 1} that cannot be (1/2 + S(n)^{−1/c})-approximated by circuits of size S(n)^{1/c}
</pre>
<b>CLW20, PDF p. 3</b>
<pre>
We say
that a function f : {0, 1}^n → {0, 1} cannot be (1/2 + ε)-approximated by circuits of type C, if every circuit
from C computes f correctly on less than (1/2 + ε)2^n of the n-bit inputs.
</pre>
</td><td>

[Statement.lean, lines 2122–2127](../Statement.lean#L2122-L2127)

<pre title="Statement.lean, lines 2122–2127">
/-- CLW20 PDF p.3: "cannot be (1/2 + ε)-approximated by circuits of type C, if every circuit from
C computes f correctly on less than (1/2 + ε)2^n of the n-bit inputs", with "circuits of size s"
read as size at most `s` (PDF p.17). -/
def CannotBeApproximated {m : ℕ} (g : BoolFunction m) (ε s : ℝ) : Prop :=
  ∀ circuit : BooleanCircuit m, (circuit.size : ℝ) ≤ s →
    ((Finset.univ.filter fun x =&gt; circuit.eval x = g x).card : ℝ) &lt; (1 / 2 + ε) * 2 ^ m
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
every f : {0, 1}^n → {0, 1} that does not have (general) circuits of size S(n)
</pre>
<b>CLW20, PDF p. 17</b> (Lemma 3.6)
<pre>
(general) circuits of size s. That is, for all circuit C of size at most s
</pre>
</td><td>

[Statement.lean, lines 2118–2120](../Statement.lean#L2118-L2120)

<pre title="Statement.lean, lines 2118–2120">
/-- "f ... has (general) circuits of size s": some circuit of size at most `s` computes `f`. -/
def HasCircuitOfSize {n : ℕ} (f : BoolFunction n) (s : ℕ) : Prop :=
  ∃ circuit : BooleanCircuit n, circuit.size ≤ s ∧ ∀ x, circuit.eval x = f x
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
given the 2^n-length truth table of f, the truth table of g can be constructed in 2^{O(n)}
time
</pre>
<b>STV01, PDF p. 21</b> (checked against the page image)
<pre>
Moreover, P′ can be evaluated in time 2^{O(ℓ)} with access to the entire truth table of P.
</pre>
</td><td>

[Statement.lean, lines 2216–2226](../Statement.lean#L2216-L2226)

<pre title="Statement.lean, lines 2216–2226">
/-- TIER 2 ALGORITHMIC CLAUSE. "given the 2^n-length truth table of f, the truth table of g can
be constructed in 2^{O(n)} time": a Mathlib `TM2ComputableInTime` machine from the truth table of
`f` (with its framed arity) to the truth table of `g` (with its framed arity), whose step bound
is at most `2^(timeExponent · n)` from the onset `timeOnset` on. -/
structure TruthTableConstructionTM2 (g : (n : ℕ) → BoolFunction n → AmplifierOutput) where
  machine : Turing.TM2ComputableInTime amplifierInput amplifierOutputWord
    (fun request : AmplifierRequest =&gt; g request.inputArity request.function)
  timeExponent : ℕ
  timeOnset : ℕ
  exponentialTime : ∀ request : AmplifierRequest, timeOnset ≤ request.inputArity →
    machine.time (amplifierInput request).length ≤ 2 ^ (timeExponent * request.inputArity)
</pre>

<pre title="Statement.lean, lines 2212–2214">
/-- The output word: the framed arity of `g`, then the full truth table of `g`. -/
def amplifierOutputWord (o : AmplifierOutput) : List Bool :=
  RepairOrdinary.frame o.arity.bits ++ boolFunctionTable o.function
</pre>

[Statement.lean, lines 1677–1679](../Statement.lean#L1677-L1679)

<pre title="Statement.lean, lines 1677–1679">
/-- The outer ordinary carrier additionally frames this complete payload. -/
def amplifierInput (request : AmplifierRequest) : List Bool :=
  RepairOrdinary.frame request.inputArity.bits ++ boolFunctionTable request.function
</pre>

<pre title="Statement.lean, lines 1673–1675">
structure AmplifierOutput where
  arity : ℕ
  function : BoolFunction arity
</pre>

[Statement.lean, lines 1083–1085](../Statement.lean#L1083-L1085)

<pre title="Statement.lean, lines 1083–1085">
structure AmplifierRequest where
  inputArity : ℕ
  function : BoolFunction inputArity
</pre>

<pre title="Statement.lean, lines 1060–1062">
def boolFunctionTable {n : ℕ} (function : BoolFunction n) : List Bool :=
  (List.range (2 ^ n)).map fun code =&gt;
    function fun index =&gt; code.testBit index.val
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
for any time-constructible function S(n)
</pre>

Hypothesis 9 adds S(n) ≥ n^c for every n, a real power with the lemma's c. `lemma3_9_large_of_literal` keeps the
printed c and drops the extra hypothesis, so the printed statement implies hypothesis 9.
</td><td>

[Statement.lean, lines 1016–1041](../Statement.lean#L1016-L1041)

<pre title="Statement.lean, lines 1016–1041">
structure TimeConstructible (bound : ℕ → ℕ) where
  program : NPOracleProgram
  coefficient : ℕ
  coefficientPositive : 0 &lt; coefficient
  oracleFree : program.all (fun instruction =&gt; match instruction with
    | .halt _ =&gt; true
    | .set _ _ _ =&gt; true
    | .copy _ _ _ =&gt; true
    | .increment _ _ =&gt; true
    | .decrement _ _ =&gt; true
    | .add _ _ _ _ =&gt; true
    | .subtract _ _ _ _ =&gt; true
    | .pair _ _ _ _ =&gt; true
    | .unpairLeft _ _ _ =&gt; true
    | .unpairRight _ _ _ =&gt; true
    | .branchZero _ _ _ =&gt; true
    | .encodeNat _ _ _ =&gt; true
    | .shiftRight _ _ _ _ =&gt; true
    | .shiftLeft _ _ _ _ =&gt; true
    | .testBit _ _ _ _ =&gt; true
    | .sat _ _ _ =&gt; false
    ) = true
  computesBound : ∀ n,
    runNPOracleProgram program (coefficient * (bound n + 1))
      (coefficient * (bound n + 1))
      (initialNPOracleState n n) = some (bound n)
</pre>

[StatementChecks/Wire_3_5_Inputs.lean, lines 26–30](../StatementChecks/Wire_3_5_Inputs.lean#L26-L30)

<pre title="StatementChecks/Wire_3_5_Inputs.lean, lines 26–30">
/-- CLW20 Lemma 3.9 as printed implies hypothesis 9: the same constant `c`, at the functions `S(n) ≥ n^c`. -/
theorem lemma3_9_large_of_literal (h : NearCubicWires.Bindings.CLW20Lemma39TM2.CLW20_Lemma3_9_TM2) :
    CLW20_Lemma3_9_TM2_Large := by
  obtain ⟨c, hc, hS⟩ := h
  exact ⟨c, hc, fun S hT _ =&gt; hS S hT⟩
</pre>

</td></tr>
</table>

Superscripts are written with `^`, with `{…}` around a superscript of more than one symbol: `S(n)^{1/c}` is
S(n)<sup>1/c</sup>.

The result CLW20 cites begins as follows; its hypothesis on P is the same worst-case hardness:

<b>STV01, PDF p. 20</b> (checked against the page image)
<pre>
Theorem 24. Let 𝒞 be a nice family of binary codes. Then there exists a constant
c such that the following is true. Let P: {0, 1}^ℓ → {0, 1} be a function such that no
circuit of size s computes P.
</pre>

The parameters of Theorem 24 are stated for input lengths below a power of the hardness s:

<b>STV01, PDF p. 21</b> (checked against the page image)

> In particular, taking ε = 1/s^γ and assuming ℓ < s^γ for a sufficiently small constant γ (e.g., γ = 1/4c), P′ has
> the following parameters: input length = ℓ′ = O(ℓ), adversary size = s′ = √s, adversary's maximum advantage = ε =
> 1/s^γ

**What to check** (a few minutes):

1. The order is the paper's: “There is a constant c ≥ 1” comes first, so one real number c serves every S. Then comes
   every time-constructible S with n^c ≤ S(n) for every n, with that same c. Everything the sentence does not state
   explicitly after that may depend on S: the function g, the constant and onset of O(n), the algorithm, and the
   constant and onset of 2^{O(n)}.
2. “does not have (general) circuits of size S(n)”: no circuit with at most S(n) nodes computes f on every input
   (`HasCircuitOfSize`, read with “size at most s” as on PDF p. 17).
3. Inapproximability: every circuit with at most S(n)^{1/c} nodes is correct on strictly fewer than
   (1/2 + S(n)^{−1/c})·2^m of the m-bit inputs. This is the PDF p. 3 definition, strict as printed. The powers are real
   powers (`Real.rpow`), as is n^c.
4. “g : {0, 1}^{O(n)} → {0, 1}”: for the hard f that the sentence speaks about, the arity of g is at most
   `arityFactor`·n once n ≥ `arityOnset`.
5. The algorithm is one Tier 2 machine (`Turing.TM2ComputableInTime`) from n and the truth table of f to the arity of g
   and the truth table of g. Its step bound is at most 2^(`timeExponent`·n) once n ≥ `timeOnset`. It runs on every
   truth table, and hardness is claimed only for hard f. STV01's P′ is likewise defined for every P and evaluated
   “with access to the entire truth table of P”.
6. Circuit size: CLW20 does not define it. The transcription counts nodes, input nodes included
   (`BooleanCircuit.size`). A gate count differs from it by at most the n input nodes, and another fan-in-two basis by
   a constant factor; the constant c absorbs both.
7. “time-constructible” is on the input side of the lemma, so it stays in Tier 1: `SourceInterfaces.TimeConstructible`
   is a register program without oracle calls that returns S(n) from n within K·(S(n)+1) steps and K·(S(n)+1) register
   bits. CLW20 uses the standard notion without defining it. The two agree up to polynomial overhead, and the lemma
   uses the hypothesis only so that its algorithm can learn S(n), within its 2^{O(n)} budget (item 9).
8. The range. CLW20 state the lemma for every time-constructible S; STV01 state the parameters of Theorem 24 for
   ℓ < s^γ (quoted above). Hypothesis 9 asks for the amplifier only when S(n) ≥ n^c. A larger c makes the statement
   weaker: for S(n) ≥ 1 it allows a larger advantage S(n)^{−1/c} and rules out only smaller circuits, of size
   S(n)^{1/c}, and it narrows the range of S. So c can be taken larger than 1/γ, and then S(n) ≥ n^c gives
   ℓ = n < S(n)^γ = s^γ for every n ≥ 2: STV01's regime. With c ≥ 2 also, STV01's adversary size √s is at least
   S(n)^{1/c}, and with c > 1/γ their advantage 1/s^γ lies strictly below S(n)^{−1/c}, which gives the strict
   inequality.
9. The running time. The algorithm must run in 2^{O(n)} steps on every truth table even when S(n) is enormous. Let
   D(n) = 4(n+1)·2^n: every n-bit function has a circuit with at most D(n) nodes (a truth-table DNF, input and NOT
   nodes included). The time-constructibility witness of S has a coefficient K > 0 and promises a successful run of
   the clock program with fuel and register bits both K·(S(n)+1) (`computesBound`). The algorithm runs the clock
   program with both limits K·(D(n)+1). If that run fails, then S(n) > D(n), since a successful run at K·(S(n)+1)
   stays successful when both limits grow. If it succeeds with a value v, then v = S(n), since the program is
   deterministic and the limits only stop a run, never change its value; the algorithm then compares v with D(n),
   because a fast clock can return an enormous S(n). Whenever S(n) > D(n), by either route, every n-bit function has a
   circuit of size at most S(n), so no f is hard, and the algorithm returns a fixed output. Only when
   S(n) ≤ D(n) = 2^{O(n)} does it run the STV01 construction (with item 10 for n ≤ 1). Each branch takes 2^{O(n)}
   steps for the fixed S and K; the constants of 2^{O(n)} may depend on S, as `Lemma3_9AtTM2` allows, while c does
   not. The constant c also absorbs the constant-factor changes of circuit basis.
10. The small inputs. The onsets of `Lemma3_9AtTM2` belong only to the arity bound and the running time; the hardness
    clause is claimed at every n. For n ≥ 2 it comes from items 8 and 9. For n = 0 and n = 1 it holds under the
    statement's own conventions, with g the constant function on zero bits (which meets every arity bound): every
    circuit has at least one node, its output node, so when S(n) = 0 no circuit has size at most
    S(n)^{1/c} = 0 and the clause is vacuous; a function of at most one bit has a circuit of at most two nodes, so no f
    is hard when S(n) ≥ 2, or when n = 0 and S(0) ≥ 1; and when n = 1 and S(1) = 1 the advantage S(n)^{−1/c} is 1, so
    every circuit agrees with g on fewer than (1/2 + 1)·2^m of the inputs.

Items 6 and 7 read terms that CLW20 does not define, and items 8–10 are arguments rather than readings. Lean checks
none of the five; it checks that hypothesis 9 follows from the printed lemma (last row).

**How the proof uses it.** The proof applies hypothesis 9 once, at S = `oracleSizeBound (17·⌈c⌉)`, a time-constructible
function with n^c ≤ S(n) for every n (`rpow_le_oracleSizeBound`), in `amplifier35`; you need not read them. The Tier 2
machine becomes a Tier 1 machine through the bridge `tm2ToOrdinary`, at linear overhead; `tm2ToOrdinaryOutputFree`
removes the output length from the budget, and `Lemma3_9AtTM2.toTier1` applies it to this lemma. The adapter rounds c
up to an integer and uses the proof's fixed hardness schedule for S.

[Proof/Wire_3_5/Transfer/LiteralSources.lean, lines 58–67](../Proof/Wire_3_5/Transfer/LiteralSources.lean#L58-L67)

<pre title="Proof/Wire_3_5/Transfer/LiteralSources.lean, lines 58–67">
/-- The ninth literal gives the amplifier at the degree `17·⌈c⌉`. -/
theorem amplifier35 (h : CLW20_Lemma3_9_TM2_Large) :
    Nonempty NearCubicWires.RepairSource.AmplifierAt35 := by
  obtain ⟨c, hc, hS⟩ := h
  obtain ⟨W⟩ := hS (oracleSizeBound (17 * ⌈c⌉₊))
    (_root_.NearCubicWires.RecoveryScheduleEnvelope.oracleSizeBoundConstructible _)
    (rpow_le_oracleSizeBound c hc _ (by omega))
  exact ⟨{ stvExponent := ⌈c⌉₊
           stvExponentPositive := Nat.ceil_pos.mpr (by linarith)
           schedule := _root_.NearCubicWires.Bindings.CLW20Lemma39.scheduleAmplifierOfLiteral hc _ W.toTier1 }⟩
</pre>

<pre title="Proof/Wire_3_5/Transfer/LiteralSources.lean, lines 36–38">
/-- `S(n) = oracleSizeBound d n` grows at least like `n^c` once `⌈c⌉ ≤ d`. -/
theorem rpow_le_oracleSizeBound (c : ℝ) (hc : 1 ≤ c) (d : ℕ) (hd : ⌈c⌉₊ ≤ d) (n : ℕ) :
    (n : ℝ) ^ c ≤ (oracleSizeBound d n : ℝ) := by
</pre>

[Bindings/TuringBridge/Bridge.lean, lines 141–147](../Bindings/TuringBridge/Bridge.lean#L141-L147)

[Bindings/TuringBridge/OutputFree.lean, lines 135–139](../Bindings/TuringBridge/OutputFree.lean#L135-L139)

[Bindings/CLW20_Lemma3_9_TM2.lean, lines 104–106](../Bindings/CLW20_Lemma3_9_TM2.lean#L104-L106)

**Class:** special case of the printed statement (the functions S(n) ≥ n^c), with its algorithm in Tier 2 (the
hypothesis “time-constructible function S(n)” stays in Tier 1); the size and clock conventions (items 6 and 7), and the
range, running time and small inputs (items 8–10), rest on the arguments given there.
