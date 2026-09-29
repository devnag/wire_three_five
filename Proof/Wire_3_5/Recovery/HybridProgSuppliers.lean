import Proof.Wire_3_5.Recovery.HybridProgSelected
import Proof.Wire_3_5.Recovery.HybridProgSourceBounds

/-! # The hybrid `E^NP` program: its suppliers (P3:3738-3741, 3758-3759; D1.6 C)

Realizes, as local interfaces, the facts behind "The resulting slice is computable in `E^NP`. Run the fixed refuter
[...] on the source length `N_{a(n)}`" (P3:3758-3759) for the hybrid program: the prefix computes the onset flag and
the recovery's shared words at `N_{a(n)} = 2^{a(n)}` (`PrefixRuns`), the hybrid Case-2 machine prints the hybrid
core's Case-2 bit (`TwoRuns`, `two_runs`), and every live length satisfies Case 1's fits (`CaseOneFits`, the
schedule's `m_a ≤ n/2`, P3:3738-3740). The recovery budget, capacity and query suppliers are base's, unchanged.
Replaces base's `CommonProgramSuppliers` (the Theorem 2.5 repository's index and fixed copies).

Paper quantity of the main type (`Suppliers`): the hybrid program's resource facts. -/

set_option autoImplicit false

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces CloseoutLanguage OrdinaryOracleCompose
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
noncomputable section

def selectedRequest (p : Parameters) (M : OrdinaryWeakMachine) (n : ℕ) : InputRequest :=
  ⟨2 ^ index p n, selectedWord p M n⟩
def prefixFlagPort (p : Parameters) := CloseoutCommonPrefix.firstSlots (work p) p.refuter p.k
  (CloseoutRetainedRefuter.old p.refuter (CloseoutSchedule.RefuterPrefix.flagPort (work p)))

def PrefixRuns (p : Parameters) (M : OrdinaryWeakMachine) (C E : ℕ) : Prop :=
  ∀ bits : List Bool, ∃ fuel ≤ C * (2 ^ bits.length + 1) ^ E, ∃ out,
    Ready RecoveryOracle.correctedSat (prefixProgram p) fuel
      (CloseoutCommonPrefix.input (work p) p.refuter p.k bits) out ∧
    out ⟨0, (prefixProgram p).base.twoTapes.trans_lt' (by decide)⟩ = frame bits ∧
    readTapeBit (out (prefixFlagPort p)) 0 = decide (p.onset ≤ length p bits.length) ∧
    (p.onset ≤ length p bits.length → ∃ padding ≤ C * (2 ^ bits.length + 1) ^ E,
      ∀ j, out (prefixRecoveryFields p j) = RecoveryBoundedCold.sharedWords
        (hierarchyWord p (selectedRequest p M bits.length))
        (CloseoutCapacity.capacity p.Aw p.Bw bits.length) padding j)

def TwoRuns (p : Parameters) (C E : ℕ) : Prop :=
  ∀ n (point : BitInput n) (x : BitInput (2 ^ index p n)), p.onset ≤ 2 ^ index p n →
    RecoveryChoice.SmallOracle (globalPCP p) p.degree x →
    let r : InputRequest := ⟨2 ^ index p n, x⟩
    ∃ out, ClockJoin.ReadyRun (two p) (C * (2 ^ n + 1) ^ E)
      (twoInput p (hierarchyWord p r) (recoveryDescription p r) (frame (List.ofFn point)) (R p r) (B p r)) out ∧
      out (twoLocal p 5) = frame
        (hybridCore (recPCP p.l p.kclk).pcp (paddedWidth p.l p.G (refH p.l p.kclk)) (fun _ => le_max_left _ _)
          (gatePCPP p.l) (selectedAmplifier p.l.eightSources.amplification (recOracleDeg p.l)) x (copiesAt p n)
          (clauseAt p n) n point).toNat.bits

/-- Case 1's fits at every live length (base's `case_one_live_fits`, for the hybrid index). -/
def CaseOneFits (p : Parameters) : Prop :=
  ∀ n (x : BitInput (2 ^ index p n)), p.onset ≤ 2 ^ index p n →
    1 ≤ n ∧ 2 ^ index p n ≤ 2 ^ n ∧ R p ⟨2 ^ index p n, x⟩ ≤ n ∧
    ((selectedAmplifier p.sources.amplification p.degree).output
        (RecoveryCaseOneRequest.request (globalPCP p) x).inputArity
        (RecoveryCaseOneRequest.request (globalPCP p) x).function).arity ≤ n

structure Constants where
  prefixC : ℕ
  prefixE : ℕ
  recoveryC : ℕ
  recoveryE : ℕ
  twoC : ℕ
  twoE : ℕ

structure Suppliers (p : Parameters) (M : OrdinaryWeakMachine) (c : Constants) : Prop where
  onset : 1 ≤ p.onset
  prefixRuns : PrefixRuns p M c.prefixC c.prefixE
  two : TwoRuns p c.twoC c.twoE
  caseOne : CaseOneFits p
  fits : ∀ n (r : InputRequest), r.1 ≤ 2 ^ n → R p r ≤ n →
    Fits p r (CloseoutCapacity.capacity p.Aw p.Bw n)
  budget : ∀ (r : InputRequest) (W : ℕ), Fits p r W →
    recoveryBudget p r W ≤ c.recoveryC * (W + 1) ^ c.recoveryE
  query : ∀ n, max (c.prefixC * (2 ^ n + 1) ^ c.prefixE)
    (c.recoveryC * (CloseoutCapacity.capacity p.Aw p.Bw n + 1) ^ c.recoveryE) ≤
      CloseoutCapacity.capacity p.Aq p.Bq n

def oneCoefficient (p : Parameters) := CloseoutCaseOne.directCoefficient (source p) (hierarchy p) (pad p)
def oneExponent (p : Parameters) := CloseoutCaseOne.directExponent (source p) p.k
  (selectedAmplifier p.sources.amplification p.degree).constructionExponent
def runBudget (p : Parameters) (c : Constants) (bits : List Bool) :=
  c.prefixC * (2 ^ bits.length + 1) ^ c.prefixE +
  c.recoveryC * (CloseoutCapacity.capacity p.Aw p.Bw bits.length + 1) ^ c.recoveryE +
  CloseoutCommonQueryClear.budget p.Aq p.Bq bits +
  oneCoefficient p * (2 ^ bits.length + 1) ^ oneExponent p + c.twoC * (2 ^ bits.length + 1) ^ c.twoE + 10

end

end NearCubicWires.RepairSource.HybridProgram
