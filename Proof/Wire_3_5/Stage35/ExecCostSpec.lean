import Proof.Wire_3_5.Stage35.Exec
import W3.Recovery3.Case2Cost

/-!
# The Case-2 execution's cost class: the statements

Paper v2, §H.6: "There are at most `2^{O(q)}` SAT queries and local work, in addition to `poly(T(N_a)) = 2^{O(q)}`
refuter work. Since `q = O(n)`, this is `2^{O(n)}` overall." For the Case-2 execution `Stage35.Exec.htwo` at the
near-cubic-wires Case-2 source block `blockV h2 a` and its kit instances `KI mw SV a d` (a Case-2 source input `z` at a
live index `ν`, the selected pair `B* = (B*_src, B*_pf)`, `q = q(2^ν)`), two facts:

* **`FoldNeedCap`**: one capacity exponent `e₄` covers the fold's bank need at every address length `n ≥ ν` whose
  copies fit;
* **`HtwoCostPoly`**: for fixed parameter-core exponents `e₁ e₂ e₃` and `e₄`, the execution's step bound `htwoCost` is
  at most `C·(2^n+1)^E` at every address length `n ≥ ν` whose `t+1` blocks fit, at the width `q = q(2^S)`.

Their consumer is the Case-2 kit (`Stage35.KitMain`).
-/

set_option autoImplicit false

namespace Stage35.ExecCost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Transfer.CertPrefixBounds
open W3.NearCubicWires.RepairSource.Outer3 W3.NearCubicWires.RepairSource.Outer3.Case2
open Stage35.Fold Stage35.Exec
open _root_.NearCubicGates.Close

variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
  (SV : Outer.SuccinctVerifier H L) (a : PointwisePCPPAlgorithm) (d D : ℕ)

/-- **The fold's bank need is covered by one capacity `2^{e₄ n + e₄}`.** -/
def FoldNeedCap : Prop :=
  ∃ e4 : ℕ, ∀ (x : KI mw SV a d) {n : ℕ} (point : BitInput n) (c : ℕ),
    (a.output x.i.req).clauseBits ≤ capOf (blockV h2 a) D x.i →
    c * widthOf (blockV h2 a) D x.i ≤ n → x.ν ≤ n →
    foldNeed (blockV h2 a) D x.i point c ≤ CloseoutCapacity.capacity e4 e4 n

/-- **The Case-2 execution runs in `2^{O(n)}`**, at the parameter core's exponents `e₁ e₂ e₃`, the capacity exponent
`e₄`, the clock exponent `k`, `A_pad = A` and `ζ = u/v`. -/
def HtwoCostPoly (k A u v e1 e2 e3 e4 : ℕ) : Prop :=
  ∃ C E : ℕ, ∀ (x : KI mw SV a d) {n : ℕ} (point : BitInput n),
    (a.output x.i.req).clauseBits ≤ capOf (blockV h2 a) D x.i →
    x.q = widthAt k A (CertPrefix.prefixS k A u v D n) →
    (candT k A u v (CertPrefix.prefixS k A u v D n) ((v - u) ^ 16) (v ^ 16) n + 1) *
      widthOf (blockV h2 a) D x.i ≤ n →
    x.ν ≤ n →
    scanRoundBound k A v D n n ((v - u) ^ 16) (v ^ 16) (pcap e1 n) (pcap e2 n) n + 1 ≤ pcap e3 n →
    htwoCost (blockV h2 a) k D x.i A u v e1 e2 e3 e4 x.cap x.q x.B.pf point
      (candT k A u v (CertPrefix.prefixS k A u v D n) ((v - u) ^ 16) (v ^ 16) n + 1) ≤ C * (2 ^ n + 1) ^ E

end Stage35.ExecCost
