# Wire–correlation tradeoffs at exponent 7/2 for depth-two threshold circuits: a Lean proof of row B of Theorem 1.1

This repository contains a complete Lean 4 proof of row B of Theorem 1.1 of "Wire–Correlation Tradeoffs at Exponent
7/2 for Depth-Two Threshold Circuits" (Dev Nag; [doi:10.5281/zenodo.22774130](https://doi.org/10.5281/zenodo.22774130)).
[`paper/paper_v2.tex`](paper/paper_v2.tex) is version 2 (3 November 2026,
[doi:10.5281/zenodo.23925761](https://doi.org/10.5281/zenodo.23925761)), the version this proof
was checked against; the DOI above always resolves to the latest version. Theorem 1.1 is unchanged since version 1
([`paper/paper.tex`](paper/paper.tex), 15 September 2026,
[doi:10.5281/zenodo.22774131](https://doi.org/10.5281/zenodo.22774131)); version 2 takes the short PCP in the form of
Murray and Williams instead of CLW20 Lemma 3.10, and states the refuter and the amplification at the ranges the proof
uses (pages 6–8). Theorem 1.1 with the constants of row B of its Table 1 (c = 1/8, K_T = 11/2, K_S = 9/2) reads:

> There is a language F ∈ E^NP such that, for every pair of fixed constants A_T, A_S > 0, there is n_0 for which, for
> every n ≥ n_0, W(C) ≤ A_T n^{7/2}/L(n)^{11/2}, C ∈ THR∘THR ⟹ agr(F_n, C) < 1/2 + L(n)^{-1/8}, and
> W(C) ≤ A_S n^{7/2}/L(n)^{9/2}, C ∈ SYM∘THR ⟹ agr(F_n, C) < 1/2 + L(n)^{-1/8}.

Section 6 of the paper ("Limitations and verification scope") describes this Lean development. Lean proves two
statements:

- **row B** (`NearCubicWires.WireExponent3_5.rowB`): Theorem 1.1 at c = 1/8, K_T = 11/2, K_S = 9/2, as quoted above;
- **the cone above row B** (`NearCubicWires.WireExponent3_5.rowBCone`), a corollary: Theorem 1.1 for every
  0 < c ≤ 1/8, K_T ≥ 11/2 and K_S ≥ 9/2. A smaller c allows a larger advantage and larger K_T, K_S lower the wire
  caps, so each of these statements asks less than row B; Lean derives them from row B with the same language F.

Both assume nine hypotheses based on published results. Five are transcriptions of the published sentence, with
standard readings of its terms; four (inputs 6–9 below) carry a documented reading of the printed statement or are
restricted to the range the proof uses, each set out on its [`SourceMapping/`](SourceMapping/) page. Lean checks:
those nine statements ⇒ row B, and the same nine ⇒ the cone, using only Lean's three standard axioms.

## Verify it

1. Install Lean (Linux or macOS, one line):

   ```
   curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none && . ~/.elan/env
   ```

2. In this directory run `make`. It downloads prebuilt Mathlib (about 5 GB), builds the proof and runs
   `Check.lean`. It takes about 2½ hours on a large machine (measured: 2 h 20 min on 90 cores). The
   build is limited by a long chain of dependent modules, so fewer cores add less time than you might expect. It needs
   about 60 GB of disk and at least 96 GB of RAM: one module alone takes about 41 GB.
3. While it runs, check [`SourceMapping/theorem-tradeoff.md`](SourceMapping/theorem-tradeoff.md), which puts row B
   of Theorem 1.1, every definition it uses, and the cone above row B beside the Lean statements, with a short list of
   what to check, and the pages for the nine published statements (table below).

## Reading the output

The run ends by printing (a) the two statements written out in Lean (`rowB`, `rowBCone`, `WireExponent3_5` and
`WireExponent3_5Hard`), (b) the two main theorems, published statements ⇒ row B and published statements ⇒ the cone,
(c) their axioms, which must be exactly `[propext, Classical.choice, Quot.sound]` (an unfinished proof would show
`sorryAx`), and then for each theorem (d) one `assumes:` line per hypothesis and (e) `PASS` or `FAIL`. `PASS` means
that the theorem's hypotheses are exactly the nine below, in this order, that its conclusion is
`NearCubicWires.WireExponent3_5.rowB` (first theorem) or `NearCubicWires.WireExponent3_5.rowBCone` (second), and that
it uses only the three standard axioms.

## What is assumed

| # | Hypothesis | Published result | Reading | Used in the paper | Page |
|---|---|---|---|---|---|
| 1 | `CTW26_Lemma3_2` | Chen, Tal, Wang (ECCC TR26-039) Lemma 3.2, after Muroga, Toda, Takasu (1961); PDF p. 10 | literal | Lemma C.1 | [1](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/1-threshold-normalization.md) |
| 2 | `CW19_Proposition18_2_TM2` | Chen, Williams (CCC 2019) Proposition 18(2); PDF p. 14 | literal, construction in Mathlib's machine model | Lemma C.2; Appendix E | [2](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/2-decomposition.md) |
| 3 | `Williams14_Corollary4_4` | Williams (J. ACM 2014) Corollary 4.4 = C.2; PDF pp. 17, 29 | literal, multitape reading | Lemma C.4 | [3](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/3-matrix-product.md) |
| 4 | `HLW06_Theorem8_2` | Hoory, Linial, Wigderson (Bull. AMS 2006) Construction 8.1 / Theorem 8.2; PDF p. 65 | literal | Appendices B and D.1 | [4](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/4-expander.md) |
| 5 | `RS62_Theorem4_eq314` | Rosser, Schoenfeld (1962) Theorem 4, (3.14); PDF p. 7 | literal | Appendix E.3, through Lemma A.7 of the earlier paper | [5](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/5-prime-theta.md) |
| 6 | `MW20_OracleCircuitPCP_TM2` | Murray, Williams (SIAM J. Comput. 2020) Section 5, proof of Theorem 1.4, after Ben-Sasson, Viola; PDF pp. 18–19 | literal, algorithm in Mathlib's machine model, T(n) supplied in binary | §H.1 item 1 | [6](SourceMapping/6-pcp.md) |
| 7 | `CLW20_Lemma3_11_explicitEnc_TM2` | Chen, Lyu, Williams Lemma 3.11, after CW19 and VW20; PDF p. 18 | literal for n ≥ 2, with the encoder's supports in the output | §H.1 item 2 | [6](SourceMapping/6-pcp.md) |
| 8 | `CLW20_Theorem1_13_Poly` | Chen, Lyu, Williams Theorem 1.13 (refuter with an NP oracle); PDF p. 6 | special case of the printed statement: the clocks T(n) = n^(k+2); multitape reading | §H.1 item 3 | [7](SourceMapping/7-refuter.md) |
| 9 | `CLW20_Lemma3_9_TM2_Large` | Chen, Lyu, Williams Lemma 3.9, after Sudan, Trevisan, Vadhan Theorem 24; PDF p. 18 | special case of the printed statement: the functions S(n) ≥ n^c; algorithm in Mathlib's machine model | §H.1 item 4 | [8](SourceMapping/8-amplifier.md) |

Hypotheses 1–7 are defined in `Statement.lean`, with the sentence each transcribes and its PDF page. `Statement.lean` is
the Theorem 2.5 repository's file ([github.com/devnag/near-cubic-wires](https://github.com/devnag/near-cubic-wires),
version 3), byte for byte (SHA-256 `d29bc7f521a565220d976022b9bb30e90196524bb4ce56b443a153cba99bc8f2`), so the pages there apply unchanged to hypotheses 1–5.
Hypotheses 8 and 9 are defined in `Statement_Wire_3_5.lean` (SHA-256 `0bd0aea6101077dbd2af73cec13367b26a17154c07220955c5dc16d691a809b8`) as the printed
statements of `Statement.lean` (`CLW20_Theorem1_13`, `CLW20_Lemma3_9_TM2`) restricted to the range the proof uses:
Theorem 1.13 at the polynomial clocks T(n) = n^(k+2), and Lemma 3.9 at the functions S(n) ≥ n^c. Each restriction
assumes less than the printed statement: `StatementChecks/Wire_3_5_Inputs.lean` proves
`CLW20_Theorem1_13 → CLW20_Theorem1_13_Poly` and `CLW20_Lemma3_9_TM2 → CLW20_Lemma3_9_TM2_Large`. Pages 6–8 are in this
repository; hypotheses 6 and 7 share page 6, since the short PCP and CLW20 Lemma 3.11 are used together as one PCP
step. Two results the paper uses are not assumed: CLW20 Lemma 3.8 (the XOR lemma; Lemma H.1) is proved in Lean,
following CLW20 Appendix A, as in the Theorem 2.5 repository; and the matrix concentration bound the paper cites for
its sampler (Tropp, Theorem 1.6; Appendix F) is replaced by a direct Lean proof of the fixed moment the sampler needs.

## What to read

Read `Challenge.lean`, `Statement_Wire_3_5.lean`, `StatementChecks/` and `SourceMapping/`. `Statement_Wire_3_5.lean`
defines row B and the cone from the definitions of `Statement.lean`, and the restricted hypotheses 8 and 9.
`StatementChecks/` proves that the statement is not trivially satisfiable (`Wire_3_5.lean`: no constant language
satisfies it), that row B is the instance c = 1/8, K_T = 11/2, K_S = 9/2 of the general statement and satisfies the
theorem's conditions on c, K_T, K_S, that counting the THR∘THR top incidences of weight zero as well gives the same
theorem (`Wire_3_5_Readings.lean`), and that hypotheses 8 and 9 follow from the printed statements
(`Wire_3_5_Inputs.lean`). `Bindings/` and `Proof/` are checked by Lean; you need not read them. Module and declaration
names in the proof keep the names they were compiled under, some from the development; renaming them would not affect
any statement. Comments in the Lean files cite the paper as `P3:n`, meaning line n of `paper/paper.tex` (version 1),
and name parts of the construction by short labels (line ranges of `paper/paper.tex`):
- machines: C1 coset selection (1324–1362), C2 explicit monomial lists (1482–1488, 2385–2412, 2777–2806), C3 the
  compiler into the printer (1707–1769, 1874–1955; MC*n* are versions of its contract), C4 seed fixing (2238–2336,
  2928–2966, 3035–3042), C5 the final pass (3044–3054, 3170–3181), C6 the weak machine (3669–3697), C7 the running
  time (3797–3811), PA the primitive's per-call writers (3066–3229), W6 the THR numbers machine;
- mathematics: B1 stars (1186–1362), B2 lists (1375–1530), B3 the compiler's algebra (1623–1982), B4 filters
  (2016–2412), B5 rows (2433–2806), B6 the sampler (2818–3055), B7 the primitive and its loads (3066–3229), B8 the
  transfer (3356–3614), B9 row B's ledger (3736–3756, 3784–3853), D1 the union machine (3699–3779), D2 the final
  comparisons (3774–3779, 3831–3846);
- shared libraries: S2 finite fields GF(2^ℓ), S3 k-wise independence and moments, S4 derandomization by exact
  conditional expectation, S5 costed structured programs, S6 asymptotics, S7 masked expectations.

The modules of the outer step that version 2 changes (the short PCP, the succinct verifier and the recovery) cite
`paper/paper_v2.tex` by lemma and section number (Appendix H).

## Caveats

- The published results are assumed, not formalized.
- Only row B and the cone above it are proved. `WireExponent3_5 c KT KS` is defined for all parameters, but the other
  rows of Table 1 and the general theorem are not formalized here.
- Docstrings say "Tier 1" for the proof's own multitape machine model and "Tier 2" for Mathlib's `Turing.TM2` model,
  as in the Theorem 2.5 repository, whose README explains where each published algorithm is stated.
- The readings and restrictions of hypotheses 6–9, each with its Lean statement, are on the pages: the short PCP's
  properties are claimed for n ≥ 1, and its algorithm is also given T(n) in binary, which claims less than the
  printed statement (page 6); CLW20 Lemma 3.11 is assumed for n ≥ 2, with the encoder's supports in the output
  (page 6); the refuter is assumed at the clocks n^(k+2), read for multitape machines, with promise machines that
  guess ⌊n/16⌋ bits, within the printed n/10 (page 7); the amplifier is assumed for S(n) ≥ n^c (page 8). The paper
  states the same ranges (§H.1) and the multitape reading (§H.8).
- E^NP is ordinary exponential time with an NP oracle, and L = ⌈log₂(n+2)⌉ (page "Theorem 1.1, row B").

## AI use

Generative-AI models were used substantively to write this formalization, as they were for the paper (see its "Use of
generative AI" paragraph). The result does not depend on trusting them: Lean's kernel checks the proof, and the
`SourceMapping/` pages let a reader check that the assumed statements match the published papers.

## Optional extra checks

- `make kernel-replay`: re-check every declaration with Lean's independent `leanchecker` (slow; parallel).
- To avoid prebuilt Mathlib binaries, remove `lake exe cache get` from the Makefile (Mathlib then builds from
  source, adding 1–3 hours).
- `python3 scripts/check_names.py .`: the naming check used by CI.
- **comparator** ([leanprover/comparator](https://github.com/leanprover/comparator), Linux only). `Challenge.lean`
  states the two main theorems from `Statement.lean`, `Statement_Wire_3_5.lean` and Mathlib alone: the nine published
  statements imply row B, and they imply the cone. Their proofs are deliberate `sorry`s, the only ones in the
  repository: they are the statements comparator checks the proof against. `Check.lean` does not import
  `Challenge.lean`. `Solution.lean` proves the same statements with the main theorems. Comparator builds both inside a
  sandbox, compares them, and replays the proofs through Lean's kernel.

  Install the three tools in user space (needs Go from go.dev and elan):
  ```
  git clone https://github.com/Zouuup/landrun && (cd landrun && git checkout 5e9a0d1 && go build -o landrun ./cmd/landrun)
  git clone --branch v4.32.0 https://github.com/leanprover/lean4export && (cd lean4export && lake build)
  git clone --branch v4.32.0 https://github.com/leanprover/comparator && (cd comparator && lake build)
  export PATH="$PWD/landrun:$PWD/lean4export/.lake/build/bin:$PATH"
  ```
  landrun is pinned because later landrun commits drop the `--` that comparator v4.32.0 passes to lean4export
  (comparator v4.33.0 adapts to them).

  Run it in a fresh clone of this repository, so that the proof is built only inside comparator's sandbox:
  ```
  lake exe cache get
  systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" --working-directory $(pwd) -- bash -c 'ulimit -s unlimited && lake env /path/to/comparator/.lake/build/bin/comparator comparator.json'
  ```
  `make comparator COMPARATOR=/path/to/comparator/.lake/build/bin/comparator` does the same. `systemd-run --user
  --pty` needs a user D-Bus session; desktop Linux has one, and on a minimal server install `dbus-user-session`.

  Cost, measured on one machine (90 cores, 3 November 2026): with Lean's kernel only (`"enable_nanoda": false` in
  `comparator.json`, as shipped), a run in a fresh copy of this repository took 4 h 56 min: 2 h 20 min for
  comparator's sandboxed build of the proof, then 2 h 36 min for the export, comparison and kernel replay. The whole
  sandbox peaked at 104 GB of RAM, including the build's parallel jobs.

  Success ends with `Your solution is okay!`. The theorems `NearCubicWires.wireExponent3_5_rowB_from_literature` and
  `NearCubicWires.wireExponent3_5_rowBCone_from_literature` in `Solution.lean` then
  1. prove the same statements as in `Challenge.lean`;
  2. use no axioms beyond `propext`, `Quot.sound` and `Classical.choice`;
  3. are accepted by the Lean kernel.

  What to read: `Challenge.lean`, `Statement_Wire_3_5.lean` and `Statement.lean` (2,525 lines, every definition the
  statements use, with the published statements last). Comparator's trusted import closure is `Statement`,
  `Statement_Wire_3_5` and Mathlib. You also trust `lakefile.toml`, the sandbox and the kernel.

License: Apache-2.0 ([LICENSE](LICENSE)), except `paper/`, which is CC BY 4.0. Quotations of other papers in
`SourceMapping/` and in docstrings are short quotations for verification and remain their authors'. How to cite:
[CITATION.cff](CITATION.cff).
