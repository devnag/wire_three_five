# Wire–correlation tradeoffs at exponent 7/2 for depth-two threshold circuits: a Lean proof of row B of Theorem 1.1

This repository contains a complete Lean 4 proof of row B of Theorem 1.1 of "Wire–Correlation Tradeoffs at Exponent
7/2 for Depth-Two Threshold Circuits" (Dev Nag; [doi:10.5281/zenodo.22774130](https://doi.org/10.5281/zenodo.22774130)).
[`paper/paper.tex`](paper/paper.tex) is version 1 (15 September 2026,
[doi:10.5281/zenodo.22774131](https://doi.org/10.5281/zenodo.22774131)), the version this proof was checked against.
Theorem 1.1 with the constants of row B of its Table 1 (c = 1/8, K_T = 11/2, K_S = 9/2) reads:

> There is a language F ∈ E^NP such that, for every pair of fixed constants A_T, A_S > 0, there is n_0 for which, for
> every n ≥ n_0, W(C) ≤ A_T n^{7/2}/L(n)^{11/2}, C ∈ THR∘THR ⟹ agr(F_n, C) < 1/2 + L(n)^{-1/8}, and
> W(C) ≤ A_S n^{7/2}/L(n)^{9/2}, C ∈ SYM∘THR ⟹ agr(F_n, C) < 1/2 + L(n)^{-1/8}.

The paper names this point as its formalization target (paper/paper.tex, lines 1082–1085). The proof assumes nine
published results, the same nine as the Lean proof of Theorem 2.5 of the author's earlier paper
([github.com/devnag/near-cubic-wires](https://github.com/devnag/near-cubic-wires)). Each is written in Lean as a
transcription of the published sentence, and Lean checks: those nine statements ⇒ row B, using only Lean's three
standard axioms.

## Verify it

1. Install Lean (Linux or macOS, one line):

   ```
   curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none && . ~/.elan/env
   ```

2. In this directory run `make`. It downloads prebuilt Mathlib (about 5 GB), builds the proof and runs
   `Check.lean`. It takes about 3 hours on a large machine (measured: 3 h 15 min on 90 cores). The build is limited
   by a long chain of dependent modules, so fewer cores add less time than you might expect. It needs about 60 GB of
   disk; 32 GB of RAM is recommended.
3. While it runs, check [`SourceMapping/theorem-tradeoff.md`](SourceMapping/theorem-tradeoff.md), which puts row B
   of Theorem 1.1 and every definition it uses beside the Lean statement, with a short list of what to check. The nine
   published statements are checked on the Theorem 2.5 repository's pages (table below).

## Reading the output

The run ends by printing (a) row B written out in Lean (`rowB`, `WireExponent3_5` and `WireExponent3_5Hard`), (b) the
main theorem, published statements ⇒ row B, (c) its axioms, which must be exactly
`[propext, Classical.choice, Quot.sound]` (an unfinished proof would show `sorryAx`), (d) one `assumes:` line per
hypothesis, and (e) `PASS` or `FAIL`. `PASS` means the hypotheses are exactly the nine below, in this order, and the
conclusion is `NearCubicWires.WireExponent3_5.rowB`.

## What is assumed

| # | Hypothesis | Published result | Used in the paper (paper/paper.tex) | Page |
|---|---|---|---|---|
| 1 | `CTW26_Lemma3_2` | Chen, Tal, Wang (ECCC TR26-039) Lemma 3.2, after Muroga, Toda, Takasu (1961) | lines 1567–1594 | [1](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/1-threshold-normalization.md) |
| 2 | `CW19_Proposition18_2_TM2` | Chen, Williams (CCC 2019) Proposition 18(2) | lines 1596–1621 | [2](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/2-decomposition.md) |
| 3 | `Williams14_Corollary4_4` | Williams (J. ACM 2014) Corollary 4.4 = C.2 | lines 1680–1687 | [3](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/3-matrix-product.md) |
| 4 | `HLW06_Theorem8_2` | Hoory, Linial, Wigderson (Bull. AMS 2006) Construction 8.1 / Theorem 8.2 | lines 1504–1506, 2083–2103 | [4](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/4-expander.md) |
| 5 | `RS62_Theorem4_eq314` | Rosser, Schoenfeld (1962) Theorem 4, (3.14) | lines 2574–2580, through Lemma A.7 of the earlier paper | [5](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/5-prime-theta.md) |
| 6 | `CLW20_Lemma3_10_TM2` | Chen, Lyu, Williams (ECCC TR20-150) Lemma 3.10, after Ben-Sasson, Viola | lines 3258–3267 | [6](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/6-pcp.md) |
| 7 | `CLW20_Lemma3_11_explicitEnc_TM2` | Chen, Lyu, Williams Lemma 3.11, after CW19 and VW20 | lines 3269–3281 | [6](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/6-pcp.md) |
| 8 | `CLW20_Theorem1_13` | Chen, Lyu, Williams Theorem 1.13 (formal version: Theorem 4.6), refuter with an NP oracle | lines 3283–3291 | [7](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/7-refuter.md) |
| 9 | `CLW20_Lemma3_9_TM2` | Chen, Lyu, Williams Lemma 3.9, after Sudan, Trevisan, Vadhan Theorem 24 | lines 3293–3302 | [8](https://github.com/devnag/near-cubic-wires/blob/main/SourceMapping/8-amplifier.md) |

Each hypothesis is defined in `Statement.lean`, with the sentence it transcribes and its PDF page. `Statement.lean` is
the Theorem 2.5 repository's file, byte for byte (SHA-256
`4c333884866c4da8958daea54f20ff2ec8220a32b750decdc1c334f0a5c260f2`), so its pages there apply unchanged. The classes
(literal; literal with a documented fix; algorithm stated in Mathlib's machine model) are listed in that repository's
README. Two results the paper uses are not assumed: CLW20 Lemma 3.8 (the XOR lemma, lines 3308–3346) is proved in
Lean, following CLW20 Appendix A, as in the Theorem 2.5 repository; and the matrix concentration bound the paper cites
for its sampler (Tropp, Theorem 1.6; lines 2812–2813) is replaced by a direct Lean proof of the fixed moment the
sampler needs.

## What to read

Read `Challenge.lean`, `Statement_Wire_3_5.lean`, `StatementChecks/` and `SourceMapping/`. `Statement_Wire_3_5.lean`
(71 lines) defines row B from the definitions of `Statement.lean`. `StatementChecks/` proves
that the statement is not trivially satisfiable (`Wire_3_5.lean`: no constant language satisfies it), that row B is the
instance c = 1/8, K_T = 11/2, K_S = 9/2 of the general statement and satisfies the theorem's conditions on c, K_T, K_S,
and that counting the THR∘THR top incidences of weight zero as well gives the same theorem (`Wire_3_5_Readings.lean`).
`Bindings/` and `Proof/` are checked by Lean; you need not read them. Comments in the Lean files cite the paper as
`P3:n`, meaning line n of `paper/paper.tex`, and name parts of the construction by short labels (line ranges of
`paper/paper.tex`):
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

## Caveats

- The published results are assumed, not formalized.
- Only row B is proved. `WireExponent3_5 c KT KS` is defined for all parameters, but the other rows of Table 1 and the
  general theorem are not formalized here.
- The paper says no statement in it is asserted to be Lean-checked (lines 1080–1081); this repository is the artifact
  its lines 1082–1085 describe for row B.
- Docstrings say "Tier 1" for the proof's own multitape machine model and "Tier 2" for Mathlib's `Turing.TM2` model,
  as in the Theorem 2.5 repository, whose README explains where each published algorithm is stated.
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
  states the main theorem from `Statement.lean`, `Statement_Wire_3_5.lean` and Mathlib alone: the nine published
  statements imply row B. Its proof is a deliberate `sorry`, the only one in the repository: it is the statement
  comparator checks the proof against. `Check.lean` does not import it. `Solution.lean` proves the same statement with
  the main theorem. Comparator builds both inside a sandbox, compares them, and replays the proof through Lean's
  kernel.

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

  Cost, measured on one machine (29 September 2026): the export, comparison and kernel replay take about 3¾ hours
  and 47 GB of RAM, after comparator's sandboxed build of the proof (in a fresh clone, add the build time above).

  Success ends with `Your solution is okay!`. The theorem `NearCubicWires.wireExponent3_5_rowB_from_literature` in
  `Solution.lean` then
  1. proves the same statement as in `Challenge.lean`;
  2. uses no axioms beyond `propext`, `Quot.sound` and `Classical.choice`;
  3. is accepted by the Lean kernel.

  What to read: `Challenge.lean` (27 lines), `Statement_Wire_3_5.lean` and `Statement.lean`
  (2,495 lines, every definition the statement uses, with the nine published statements last). Comparator's trusted
  import closure is `Statement`, `Statement_Wire_3_5` and Mathlib. You also trust `lakefile.toml`, the sandbox and the
  kernel.

License: Apache-2.0 ([LICENSE](LICENSE)), except `paper/`, which is CC BY 4.0. Quotations of other papers in docstrings
are short quotations for verification and remain their authors'. How to cite: [CITATION.cff](CITATION.cff).
