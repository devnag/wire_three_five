import Proof.Foundations.ProjectionSourceContract
import Statement

/-!
# Binding: CLW20 Lemma 3.10 (the projection PCP, from [BV14]) → `ProjectionPCPSource`

Source PDF: `CLW20_Chen_Lyu_Williams_AE_Circuit_Lower_Bounds_ECCC_TR20-150.pdf`,
PDF page 18 (printed p.17), §3.5, verbatim:

> Lemma 3.10 ([BV14]). Let M be an algorithm running in time T = T(n) ≥ n on inputs of the form
> (x, y) where |x| = n. Given x ∈ {0, 1}^n, one can output in poly(n, log T) time circuits
> Q: {0, 1}^r → {0, 1}^{rt} for t = poly(r) and R: {0, 1}^t → {0, 1} such that:
> • Proof length. 2^r ≤ T · polylogT.
> • Completeness. If there is a y ∈ {0, 1}^{T(n)} such that M(x, y) accepts then there is a map
>   π: {0, 1}^r → {0, 1} such that for all z ∈ {0, 1}^r, R(π(q1), . . . , π(qt)) = 1 where
>   (q1, . . . , qt) = Q(z).
> • Soundness. If no y ∈ {0, 1}^{T(n)} causes M(x, y) to accept, then for every map
>   π: {0, 1}^r → {0, 1}, at most 2^r/n^10 distinct z ∈ {0, 1}^r have R(π(q1), . . . , π(qt)) = 1
>   where (q1, . . . , qt) = Q(z).
> • Complexity. Q is a projection, i.e., each output bit of Q is a bit of input, the negation of a
>   bit, or a constant. R is a 3CNF.

The original is BV14 Theorem 1.1 (`BV14_Ben-Sasson_Viola_Short_PCPs_Projection_Queries_ECCC_TR14-017.pdf`,
PDF p.3). It has the same items, with the soundness written as "at most 1/n^10 fraction of the z".

## Deliverables

* `CLW20_Lemma3_10` : the literal. Its hypothesis is that M runs in time `T(n)` on EVERY input
  `(x, y)` with `|x| = n`, for every `y`.
* `CLW20_Lemma3_10_onWitnessLengthT` : the same statement, except that the time hypothesis is
  required only on the inputs the lemma talks about, `y ∈ {0,1}^{T(n)}`. That is the import's
  hypothesis. `clw20_lemma3_10_onWitnessLengthT_to_literal` proves that this version implies the
  literal (the easy direction: a stronger hypothesis is easier to meet).
* `clw20_lemma3_10_onWitnessLengthT_to_import :
  CLW20_Lemma3_10_onWitnessLengthT → ProjectionPCPSource` is PROVED.
* `clw20_lemma3_10_false_at_zero` and `clw20_lemma3_10_onWitnessLengthT_false_at_zero` : if the
  properties are also claimed at `n = 0`, both statements are FALSE. The verifier halts at once
  and `T(n) = n`. Then `T(0) = 0`, and "2^r ≤ T · polylog T" would say `2^r ≤ 0`.

## The gap between the printed hypothesis and the import

The import (`Proof/Foundations/ProjectionSourceContract.lean`) asks M to halt within `T(n)` steps
only when `|w| = T(n)`. The printed hypothesis "running in time T … on inputs of the form (x, y)"
covers every `y`. A verifier may halt on witnesses of length `T(n)` and loop on shorter ones. So
the literal applies to fewer verifiers than the import needs. The missing arrow
`CLW20_Lemma3_10 → CLW20_Lemma3_10_onWitnessLengthT` is a machine wrapper: run M, and reject as
soon as the witness end marker is read. In time `T(n)`, M never reads that marker when the
witness has length `T(n)`. The wrapper is `Bindings/CLW20_Lemma3_10_Wrapper.lean`.

## Differences between the printed lemma and the import, and how each is bridged by proof

1. **Quantifier order and constants.** Printed: `∀ M T`, then "one can output …" with hidden
   constants in "poly(n, log T)", "t = poly(r)" and "T · polylog T". We read every hidden
   constant as chosen after `M` and `T` (the weakest reading), with a separate `K, e` for each
   clause. The import also chooses its algorithm, degrees and coefficient inside the witness,
   after `verifier, T`. The adapter merges the three coefficients into one, `K₀ + K_t + K_p + 1`,
   and keeps the three exponents as the import's `PCPDegrees`.
2. **Soundness: a count against a fraction.** Printed: "at most 2^r/n^10 distinct z". The
   literal is `(#accepting z : ℝ) ≤ 2^r / n^10`. The import bounds `acceptanceFraction ≤ 1/n^10`,
   where `acceptanceFraction = #accepting z / |{0,1}^r|`. `card_bitInput` gives
   `|{0,1}^r| = 2^r`, and dividing by `2^r > 0` is `sound_fraction`.
3. **Projection outputs over the input z of Q.** Printed: `Q : {0,1}^r → {0,1}^{rt}`, with
   "(q1, …, qt) = Q(z)" and "each output bit of Q is a bit of input, the negation of a bit, or a
   constant". The literal has one `ProjectedRandomBit r` for each of the `r·t` output bits of Q.
   Each one is evaluated on Q's own input `z` (the randomness), not on `x`. `q_j` is the `j`-th
   block of `r` bits: output bit `r·j + i` (`blockIndex`). The import instead has
   `queryBits j i : ProjectedRandomBit width` evaluated on the randomness. `toRaw` re-indexes.
   `Circuits.word_eq` proves that the two descriptions list the same projections in the same
   order (`List.ofFn_mul'`).
4. **The proof as a map `{0,1}^r → {0,1}` against a table of `2^r` bits.** Printed: "a map
   π: {0,1}^r → {0,1}". The import's proof is `BitInput (2^r)`, addressed by `binaryAddress`.
   Soundness: every table `p` gives the map `π z = p (binaryAddress z)` with the same accepting
   set, by `rfl`. Completeness: the literal's `π` gives the table
   `a ↦ π (decodeAddress a)`, and `decodeAddress_binaryAddress` shows that the two agree on every
   query.
5. **t = poly(r).** Printed: "for t = poly(r)". The literal is `t ≤ K * (r + 1) ^ e`, the import's
   `queryBound`, for `n ≥ 1`.
6. **Proof length.** Printed: "2^r ≤ T · polylogT". The literal is `2^r ≤ K * T(n) * L(T(n))^e`,
   the import's `proofBound`, with `L = logScale`, the manuscript's `⌈log₂(·+2)⌉ ≥ 1`. Read with
   the plain `log₂`, `polylog T` would vanish at `T = 1`.
7. **Given x (and T(n)).** Printed: "Given x ∈ {0,1}^n, one can output in poly(n, log T) time".
   `T` is an arbitrary function with `T(n) ≥ n`. It is not assumed time-constructible. So the
   algorithm receives `T(n)` in binary with `x`, which is exactly the input whose length
   `poly(n, log T)` measures. With `x` alone the statement can fail, because a `T` that is hard
   to compute cannot then be read off. This is the import's input
   `frame x ++ frame (binary T(n))`. The budget is `K * (n + |binary T(n)| + 1) ^ e`
   (`natBitLength`). Tier 1: the algorithm is an `OrdinaryWordFunction`. Its output word lists
   `r`, `t`, the projection code of every output bit of Q, and R's clauses. It is total on every
   `x`, `n = 0` included, because the import's constructor is total.
8. **n ≥ 1.** The properties are claimed for `n ≥ 1`. At `n = 0` the printed soundness bound
   `2^r/0^10` divides by zero, and "2^r ≤ T · polylog T" is unsatisfiable when `T(0) = 0`
   (proved false above). The import also claims its properties only for `1 ≤ n`.
9. **M and "accepts".** M is the repo's `OrdinaryVerifier`: `x` framed on tape 0 and `y` framed
   on tape 1. "M(x, y) accepts" is `Verifier.accepts`, halting in an accepting control state.
   "If there is a y ∈ {0,1}^{T(n)} such that M(x, y) accepts" is, by definition, the import's
   `verifier.language T n x`.
-/

namespace NearCubicWires.Bindings.CLW20Lemma310

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

/-! ## The printed objects -/








/-! ## The literal -/

/-! ## The properties cannot also be claimed at `n = 0` -/

/-! ## Bridges -/

/-- The import's table proof, read back as a map on `{0,1}^r`. -/
def decodeAddress {r : ℕ} (a : Fin (2 ^ r)) : BitInput r :=
  fun i => a.val.testBit i.val

theorem decodeAddress_binaryAddress {r : ℕ} (b : BitInput r) :
    decodeAddress (binaryAddress b) = b := by
  have hval : (binaryAddress b).val = Nat.ofBits b := by
    unfold binaryAddress
    change encodeBitInput b % 2 ^ r = Nat.ofBits b
    rw [encodeBitInput_eq_ofBits]
    exact Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow b)
  funext i
  unfold decodeAddress
  rw [hval, Nat.testBit_ofBits_lt _ _ i.isLt]

/-! ## The adapter -/


end NearCubicWires.Bindings.CLW20Lemma310
