import Proof.Wire_3_5.Recovery.HybridProgSource

/-! # The hybrid `E^NP` program: the selected slice (P3:3738-3741, 3758-3759; D1.6 C)

Realizes "For source lengths `N_a = 2^a`, put `m_a = t(q(N_a))q_0(N_a)`. Choose the largest `a` such that
`m_a ≤ n/2`" (P3:3738-3740) and "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on the
source length `N_{a(n)}`" (P3:3758-3759) as the target of the hybrid program: at input length `n` the source index is
the prefix's scan index (`index = prefixS … n`), the refuter's word at `2^{index}` is the selected word, and the
slice is the hybrid core (`hybridCore`) with `t(q)+1` copies and the clause width at `q = q(2^{index})`;
lengths with `2^{index}` below the onset print `false`. Replaces base's `CommonProgramSelected` (the Theorem 2.5 repository's schedule index
and fixed-copies `core`).

The Case-1 docking lemma `case_one_header_at` is base's `selected_case_one_header_live` with its schedule facts
(`case_one_live_fits`, stated for the Theorem 2.5 repository's index) taken as hypotheses; they are discharged for the hybrid index by the
suppliers.

Paper quantity of the main type (`target`, `active_target`): the hybrid slice at `N_{a(n)}`. -/

set_option autoImplicit false

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces CloseoutLanguage
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Schedule NearCubicWires.WireExponent3_5.Ledger
open SelectedRecoveryIntegration RecoveryScheduleEnvelope ProjectionNormalization
noncomputable section

/-- **The source index `a(n)`**, computed by the prefix's scan. -/
def index (p : Parameters) (n : ℕ) : ℕ := CertPrefix.prefixS p.k p.A p.u p.v p.D n
/-- The source length `N_{a(n)} = 2^{a(n)}`. -/
def length (p : Parameters) (n : ℕ) : ℕ := 2 ^ index p n
def selectedWord (p : Parameters) (M : OrdinaryWeakMachine) (n : ℕ) :=
  (p.sources.hierarchy (fun n => n ^ (p.k + 2)) p.clock).output M (2 ^ index p n)
/-- The padded width `q = q(2^{a(n)})`. -/
def qAt (p : Parameters) (n : ℕ) : ℕ := widthAt p.kclk p.A (index p n)
/-- The copies `t(q) + 1`. -/
def copiesAt (p : Parameters) (n : ℕ) : ℕ :=
  sched (gateCParams1 p.l).ζ (gateZeta_pos p.l) (gateZeta_lt p.l) (Lq (qAt p n)) + 1
/-- The clause width at `q`. -/
def clauseAt (p : Parameters) (n : ℕ) : ℕ := clauseWidth p.D (qAt p n)
/-- The hybrid slice at `n`. -/
def hcore (p : Parameters) (M : OrdinaryWeakMachine) (n : ℕ) : BoolFunction n :=
  hybridCore (recPCP p.l p.kclk).pcp (paddedWidth p.l p.G (refH p.l p.kclk)) (fun _ => le_max_left _ _) (gatePCPP p.l)
    (selectedAmplifier p.l.eightSources.amplification (recOracleDeg p.l)) (selectedWord p M n) (copiesAt p n)
    (clauseAt p n) n
/-- **The hybrid program's target language.** -/
def target (p : Parameters) (M : OrdinaryWeakMachine) : Language :=
  fun n => if p.onset ≤ length p n then hcore p M n else fun _ => false

theorem inactive_target (p : Parameters) (M : OrdinaryWeakMachine) (n : ℕ) (x : BitInput n)
    (inactive : ¬p.onset ≤ length p n) : target p M n x = false := by
  simp only [target, if_neg inactive]

theorem active_target (p : Parameters) (M : OrdinaryWeakMachine) (n : ℕ) (x : BitInput n)
    (live : p.onset ≤ length p n) : target p M n x = hcore p M n x := by
  simp only [target, if_pos live]

/-- **Case 1 at the hybrid index** (base's `selected_case_one_header_live` with its schedule facts as hypotheses). -/
theorem case_one_header_at (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (degree copies cb s : ℕ)
    {n : ℕ} (address : BitInput n) (input : BitInput (2 ^ s)) :
    let source := fixedProjection sources
    let H := (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy
    let amplifier := selectedAmplifier sources.amplification degree
    let pcp := (outer sources k clock).result.pcp
    1 ≤ n → 2 ^ s ≤ 2 ^ n → HierarchyProjection.width source H (padding sources k clock) (2 ^ s) ≤ n →
    (amplifier.output (RecoveryCaseOneRequest.request pcp input).inputArity
        (RecoveryCaseOneRequest.request pcp input).function).arity ≤ n →
      ¬RecoveryChoice.SmallOracle pcp degree input →
      ∃ cost ≤ CloseoutCaseOne.directCoefficient source H (padding sources k clock) *
          (2 ^ n + 1) ^ CloseoutCaseOne.directExponent source k amplifier.constructionExponent,
        ∃ out, OrdinaryOracleCompose.Ready RecoveryOracle.correctedSat
          (RecoveryCaseOnePaddedBit.program source amplifier.constructor.program k H.coefficient
            (padding sources k clock) (VerifierEncoding.code H.verifier)) cost
          (RecoveryCaseOnePaddedBit.input source amplifier.constructor.program k
            (HierarchySourceInput.hierarchyInput H ⟨2 ^ s, input⟩) (List.ofFn address)) out ∧
        out (RecoveryCaseOnePaddedBit.ports source amplifier.constructor.program k).outputTape =
          frame (core pcp (selectedPCPP sources) amplifier input copies cb n address).toNat.bits := by
  intro source H amplifier pcp hn hN hR hfit hsmall
  obtain ⟨cost, hcost, out, hrun, hout⟩ := RecoveryCaseOnePaddedBit.bit_ready source amplifier H
    (padding sources k clock) (Nat.le_max_right _ _) ⟨2 ^ s, input⟩ hfit address
  have hb := CloseoutCaseOne.direct_budget_bound source amplifier H (padding sources k clock)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) ⟨2 ^ s, input⟩ hn hN hR hfit address
  have hle : RecoveryCaseOnePaddedBit.budget source amplifier H (padding sources k clock)
      (Nat.le_max_right _ _) ⟨2 ^ s, input⟩ hfit address ≤
      CloseoutCaseOneDirect.budget source amplifier H (padding sources k clock)
        (Nat.le_max_right _ _) ⟨2 ^ s, input⟩ hfit address := Nat.le_add_left _ _
  refine ⟨cost, hcost.trans (hle.trans hb), out, hrun, ?_⟩
  rw [core_case_one pcp (selectedPCPP sources) amplifier input copies cb n hsmall hfit]
  exact hout

end

end NearCubicWires.RepairSource.HybridProgram
