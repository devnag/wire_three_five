import Proof.Wire_3_5.Recovery.CaseTwoCost

/-! # The hybrid Case-2 execution at the hierarchy's normalized PCP (P3:3763-3771; D1.6 A4a)

Realizes "In the yes case, prefix self-reduction recovers the first eligible description, after which each honest
proof bit is computed by the deterministic PCPP algorithm" (P3:3763-3765) within "`2^{O(n)}` overall" (P3:3769-3771)
for the hybrid Case 2, stated for an arbitrary projection PCP `p` whose request is the padded substituted request
`request a (castCircuit (compactSubstituted O (p.queryAddressBits x) (p.decision x ·)))`, exactly as base's
`CloseoutCaseTwo.Selected.receipt` does for the Theorem 2.5 repository's Case 2:
* **`HReceipt … r p`**: from the five cold words at `r` (the hierarchy word, the canonical description of the oracle,
  the framed address, `1^R`, `1^B`) the hybrid machine `CaseTwoExec.htwo` writes, within `C·(2^n+1)^E` steps, the
  framed bit `padCore (xorPower (paddedUnsigned (a.output req) hcb) copies) hfit x` of the padded request `req` at the
  width `q = q(2^S)` (`S = prefixS … n`), for every clause width `cb = ⌈D log₂(q+2)⌉` and copy count `copies = t + 1`
  given as equations (so a consumer passes its own `req`, `cb`, `copies`);
* **`hnormalized_run`**: one choice of the capacity exponents and of `C, E` makes `HReceipt` hold at every `r` for base's
  `hierarchyNormalized` PCP (A3c's `htwo_run`, A3d's `foldNeed_cap` and `htwoCost_poly`, `prefix_caps`, and base's
  `normalized_hierarchy`, as in base's `Selected.normalized_polynomial_run`);
* **`hselected_run`** (`HSelRun`): the same run stated at base's selected PCP for the union setup's padded request
  `unionRequest (padProjectionPCP pcp wf hw) a x (castCircuit O)` at any padded width `wf ≥ R` (`unionRequest_pad`
  and base's compaction idempotence `compact_sub`).

Paper quantity of the main type (`HReceipt`): the hybrid Case-2 bit of the padded request, within `2^{O(n)}` steps. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoReceipt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)
open NearCubicWires.RecoveryPipeline (padCore)
open NearCubicWires.RepairSource.CloseoutLanguage (paddedUnsigned clauseWidth)
open NearCubicWires.WireExponent3_5.Transfer.CertPrefixBounds
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadWhole NearCubicWires.WireExponent3_5.Transfer.CaseTwoFold
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoFoldRun NearCubicWires.WireExponent3_5.Transfer.CaseTwoExec
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoCost

noncomputable section

/-- The padded core bit depends only on the request, the clause width and the copy count (not on the proofs). -/
theorem core_congr (a : PointwisePCPPAlgorithm) {req req' : PCPPRequest a.minimumArity} (hr : req = req')
    {cb cb' c c' n : ℕ} (hcb : cb = cb') (hc : c = c') (h1 : (a.output req).clauseBits ≤ cb)
    (h1' : (a.output req').clauseBits ≤ cb') (f1 : c * (req.arity + cb + 1) ≤ n)
    (f1' : c' * (req'.arity + cb' + 1) ≤ n) (point : BitInput n) :
    padCore (xorPower (paddedUnsigned (a.output req) h1) c) f1 point =
      padCore (xorPower (paddedUnsigned (a.output req') h1') c') f1' point := by
  subst hr hcb hc
  rfl

/-- Compacting an already compacted formula changes nothing (base's `compact_request`, at the circuit). -/
theorem compact_sub {n r q : ℕ} (oracle : BooleanCircuit n) (projections : Fin q → Fin n → ProjectedRandomBit r)
    (formula : ThreeCNF q) :
    PCPPSubstitution.compactSubstituted oracle projections (compactThreeCNF formula) =
      PCPPSubstitution.compactSubstituted oracle projections formula := by
  simp only [PCPPSubstitution.compactSubstituted, compactThreeCNF, List.dedup_idem]

section Receipt
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
  {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ)

/-- **The hybrid Case-2 receipt at a projection PCP `p`** and a source request `r`: the hybrid machine's run on the five
cold words and its framed output bit, for the padded request `req` of any small oracle, at `q = q(2^S)`. -/
def HReceipt (A u v e1 e2 e3 e4 degree D C E : ℕ) (r : InputRequest) {M : TimedDecisionMachine} {T : ℕ → ℕ}
    (p : ProjectionPCP M T) : Prop :=
  ∀ (oracle : BooleanCircuit (p.nativeWidth r.1)), oracle.size ≤ oracleSizeBound degree (p.nativeWidth r.1) →
  ∀ (R : ℕ), R = p.nativeWidth r.1 →
  ∀ (q : ℕ) (hq : p.nativeWidth r.1 ≤ q) {N : ℕ} (point : BitInput N),
    q = widthAt k A (CertPrefix.prefixS k A u v D N) → a.minimumArity ≤ q → r.1 ≤ 2 ^ N →
  ∀ (req : PCPPRequest a.minimumArity), req = PCPPRequestBoundary.request a (castCircuit hq
      (PCPPSubstitution.compactSubstituted oracle (p.queryAddressBits r.2) (p.decision r.2 fun _ => false))) →
  ∀ (cb copies : ℕ), cb = clauseWidth D q →
    copies = candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1 →
  ∀ (hcb : (a.output req).clauseBits ≤ cb) (hfit : copies * (req.arity + cb + 1) ≤ N),
  ∃ out, ClockJoin.ReadyRun (htwo source a k D A u v e1 e2 e3 e4 H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (C * (2 ^ N + 1) ^ E)
      (htwoIn source a k D (HierarchySourceInput.hierarchyInput H r)
        (RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription (oracleSizeBound degree R) oracle))
        (RepairOrdinary.frame (List.ofFn point)) R (oracleSizeBound degree R)) out ∧
    out (outSlot source a k D 1) =
      RepairOrdinary.frame (padCore (xorPower (paddedUnsigned (a.output req) hcb) copies) hfit point).toNat.bits

/-- **The hybrid Case-2 receipt holds at the hierarchy's normalized PCP** for one choice of the capacity exponents and
of `C, E`, at every source request. -/
theorem hnormalized_run (hcoeff : H.coefficient ≤ Cpad) (hpad : k + 3 ≤ Cpad) {D : ℕ} (hD : 1 ≤ D)
    (A u v degree : ℕ) (huv : 2 * u < v) :
    ∃ e1 e2 e3 e4 C E : ℕ, ∀ r : InputRequest,
      HReceipt source a H Cpad A u v e1 e2 e3 e4 degree D C E r
        (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r) := by
  obtain ⟨e1, e2, e3, hcaps⟩ := prefix_caps k A u v D huv
  obtain ⟨e4, hneed⟩ := foldNeed_cap source a H Cpad hpad hcoeff degree D
  obtain ⟨C, E, hcost⟩ := htwoCost_poly source a H Cpad hpad hcoeff A u v e1 e2 e3 e4 degree D
  refine ⟨e1, e2, e3, e4, C, E, fun r => ?_⟩
  have actual : HReceipt source a H Cpad A u v e1 e2 e3 e4 degree D C E r
      (RecoveryPCPFormulaResumeHierarchy.normalized source k H.coefficient Cpad (VerifierEncoding.code H.verifier)
        (List.ofFn r.2) hpad) := by
    intro oracle horacle R hR q hq N point hqS hmin hr req hreq cb copies hcbeq hcop hcb hfit
    subst hR hreq hcbeq hcop
    have harity : (wrequest source a H Cpad hpad r oracle q hq).arity = q := max_eq_left hmin
    have hcap : capOf source a H Cpad hpad r oracle q hq D = clauseWidth D q := by
      show clauseWidth D (wrequest source a H Cpad hpad r oracle q hq).arity = _
      rw [harity]
    have hcb' : (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits ≤
        capOf source a H Cpad hpad r oracle q hq D := by
      rw [hcap]; exact hcb
    have hwid : widthOf source a H Cpad hpad r oracle q hq D =
        (wrequest source a H Cpad hpad r oracle q hq).arity + clauseWidth D q + 1 := by
      show _ + capOf source a H Cpad hpad r oracle q hq D + 1 = _
      rw [hcap]
    have hfit' : (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1) *
        widthOf source a H Cpad hpad r oracle q hq D ≤ N := by
      rw [hwid]; exact hfit
    have hqN : q ≤ N := by
      have h1 : widthOf source a H Cpad hpad r oracle q hq D ≤
          (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1) *
            widthOf source a H Cpad hpad r oracle q hq D := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have htotal := hneed r oracle q hq point _ horacle hcb' hfit' hqN hr
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcaps N
    obtain ⟨out, hrun, hout⟩ := htwo_run source a D H Cpad hpad r oracle q hq A u v e1 e2 e3 e4 hcoeff hD horacle
      point hqS hmin hcb' hfit' htotal c1 c2 c3 c4 c5 c6
    have hc := hcost r oracle q hq point horacle hmin hqS hcb' hfit' hr c6
    have hrun2 := ClockJoin.enlarge _ _ _ _ _ hrun hc
    refine ⟨out, hrun2, ?_⟩
    have hcc := core_congr a (rfl : wrequest source a H Cpad hpad r oracle q hq =
      wrequest source a H Cpad hpad r oracle q hq) hcap rfl hcb' hcb hfit' hfit point
    rw [hout, hcc]
    rfl
  rw [RecoveryPCPFormulaResumeHierarchy.normalized_hierarchy source H Cpad hpad r] at actual
  exact actual

/-- **The hybrid Case-2 run at the selected PCP** (the property): for every padded width `wf ≥ R` and every small
oracle `O` at the source word `x` at `2^s`, the hybrid machine writes the Case-2 bit of the union setup's padded request
`unionRequest (padProjectionPCP pcp wf hw) a x (castCircuit O)` within `C·(2^N+1)^E`, at any `pcp` equal to base's
selected PCP. -/
def HSelRun (hpad : k + 3 ≤ Cpad) (A u v e1 e2 e3 e4 degree D C E : ℕ) : Prop :=
  ∀ (pcp : type_of% (CloseoutCaseTwo.Selected.pcp source H Cpad hpad)),
    pcp = CloseoutCaseTwo.Selected.pcp source H Cpad hpad → ∀ (s : ℕ) (x : BitInput (2 ^ s))
    (oracle : BooleanCircuit (pcp.nativeWidth (2 ^ s))),
    oracle.size ≤ oracleSizeBound degree (pcp.nativeWidth (2 ^ s)) →
    ∀ (wf : ℕ → ℕ) (hw : ∀ m, pcp.nativeWidth m ≤ wf m)
      {N : ℕ} (point : BitInput N),
    wf (2 ^ s) = widthAt k A (CertPrefix.prefixS k A u v D N) → a.minimumArity ≤ wf (2 ^ s) → s ≤ N →
    ∀ (cb copies : ℕ), cb = clauseWidth D (wf (2 ^ s)) →
      copies = candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1 →
    ∀ (hcb : (a.output (unionRequest (ProjectionPCPPadding.padProjectionPCP
        pcp wf hw) a x (castCircuit (hw (2 ^ s)) oracle))).clauseBits ≤ cb)
      (hfit : copies * ((unionRequest (ProjectionPCPPadding.padProjectionPCP
        pcp wf hw) a x (castCircuit (hw (2 ^ s)) oracle)).arity +
          cb + 1) ≤ N),
    ∃ out, ClockJoin.ReadyRun
        (htwo source a k D A u v e1 e2 e3 e4 H.coefficient Cpad (VerifierEncoding.code H.verifier))
        (C * (2 ^ N + 1) ^ E)
        (htwoIn source a k D (HierarchySourceInput.hierarchyInput H ⟨2 ^ s, x⟩)
          (RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription
            (oracleSizeBound degree (pcp.nativeWidth (2 ^ s))) oracle))
          (RepairOrdinary.frame (List.ofFn point)) (pcp.nativeWidth (2 ^ s))
          (oracleSizeBound degree (pcp.nativeWidth (2 ^ s)))) out ∧
      out (outSlot source a k D 1) =
        RepairOrdinary.frame (padCore (xorPower (paddedUnsigned (a.output (unionRequest
          (ProjectionPCPPadding.padProjectionPCP pcp wf hw) a x
            (castCircuit (hw (2 ^ s)) oracle))) hcb) copies) hfit point).toNat.bits

/-- **The hybrid Case-2 run holds at the selected PCP** for one choice of the exponents and of `C, E` (`unionRequest_pad` and base's compaction idempotence identify the union request with the receipt's request). -/
theorem hselected_run (hcoeff : H.coefficient ≤ Cpad) (hpad : k + 3 ≤ Cpad) {D : ℕ} (hD : 1 ≤ D)
    (A u v degree : ℕ) (huv : 2 * u < v) :
    ∃ e1 e2 e3 e4 C E : ℕ, HSelRun source a H Cpad hpad A u v e1 e2 e3 e4 degree D C E := by
  obtain ⟨e1, e2, e3, e4, C, E, hrecv⟩ := hnormalized_run source a H Cpad hcoeff hpad hD A u v degree huv
  refine ⟨e1, e2, e3, e4, C, E, fun pcp hpcp s x oracle horacle wf hw N point hqS hmin hsN cb copies hcbeq hcop hcb
    hfit => ?_⟩
  subst hpcp
  have e : (CloseoutCaseTwo.Selected.pcp source H Cpad hpad).nativeWidth (2 ^ s) =
      (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad ⟨2 ^ s, x⟩).nativeWidth (2 ^ s) := rfl
  have hq' : (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad ⟨2 ^ s, x⟩).nativeWidth (2 ^ s) ≤
      wf (2 ^ s) := by rw [← e]; exact hw (2 ^ s)
  have hcs : PCPPSubstitution.compactSubstituted oracle
      ((CloseoutCaseTwo.Selected.pcp source H Cpad hpad).queryAddressBits x)
      ((CloseoutCaseTwo.Selected.pcp source H Cpad hpad).decision x fun _ => false) =
      @PCPPSubstitution.compactSubstituted
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad ⟨2 ^ s, x⟩).nativeWidth (2 ^ s))
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad ⟨2 ^ s, x⟩).nativeWidth (2 ^ s))
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad ⟨2 ^ s, x⟩).queryCount (2 ^ s))
        oracle
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad ⟨2 ^ s, x⟩).queryAddressBits x)
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad ⟨2 ^ s, x⟩).decision x
          fun _ => false) :=
    compact_sub _ _ _
  have hreq : unionRequest (ProjectionPCPPadding.padProjectionPCP (CloseoutCaseTwo.Selected.pcp source H Cpad hpad) wf hw)
      a x (castCircuit (hw (2 ^ s)) oracle) = PCPPRequestBoundary.request a (castCircuit hq'
        (@PCPPSubstitution.compactSubstituted
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad ⟨2 ^ s, x⟩).nativeWidth (2 ^ s))
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad ⟨2 ^ s, x⟩).nativeWidth (2 ^ s))
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad ⟨2 ^ s, x⟩).queryCount (2 ^ s))
        oracle
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad ⟨2 ^ s, x⟩).queryAddressBits x)
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad ⟨2 ^ s, x⟩).decision x
          fun _ => false))) := by
    rw [unionRequest_pad (CloseoutCaseTwo.Selected.pcp source H Cpad hpad) wf hw a x oracle, hcs]
    rfl
  have h := hrecv ⟨2 ^ s, x⟩ oracle horacle ((CloseoutCaseTwo.Selected.pcp source H Cpad hpad).nativeWidth (2 ^ s)) e
    (wf (2 ^ s)) hq' point hqS hmin (Nat.pow_le_pow_right (by norm_num) hsN) _ hreq cb copies hcbeq hcop hcb hfit
  exact h

end Receipt

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoReceipt
