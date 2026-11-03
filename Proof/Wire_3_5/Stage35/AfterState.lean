import Proof.Wire_3_5.Stage35.AfterProg
import Proof.Wire_3_5.Stage35.Bundle

-- Port of W3 Recovery3/AfterState.lean with the copies schedule (Stage35.WQ).

/-!
# The recovery after the refuter: run segments

The near-cubic-gates paper's uniform recovery (sec:all-lengths), the three stages and the two branches, as segments of one run of `After.prog`
(Recovery/AfterProg.lean). `start K c k A` is the graph's configuration entering piece `k` on the ambient tapes `A`.
A live index (`Live`) is one the after-prefix program is run on (`Recovery3.AfterRun.run`: `1 ≤ ν`, the cutoff, and
`m(q(N_ν)) ≤ n/2`). `StageBudgetAt d A B` is `StageBudget d` at the capacity parameters `(A, B)` of the
configuration. `TailRuns K c`: the segment after stage 2 found the first honest oracle `O*` (the near-cubic-gates paper's uniform recovery: "Third, a
formula over the description of `B_pf` … finds the first `B*_pf`, or shows that there is none, in which case the table
is `Ô*`"; then Case 1 (iii) or Case 2), from piece 24 to the stop, with the gate core on the output tape.
-/

set_option autoImplicit false


namespace NearCubicGates.Close.Recovery3.After

open Stage35 _root_.NearCubicGates.Close _root_.NearCubicGates.Close.Recovery3 _root_.NearCubicGates.Close.Recovery3.After

open W3.Recovery3 NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

section

variable {s : WS35} {P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm} {g : WQ}

/-- The graph's configuration entering piece `k` on the ambient tapes `A`. -/
noncomputable def start (K : Kit s P g) (c : Cfg) (k : Fin 31) (A : Fin (T K) → List Bool) : (prog K c).Config :=
  controlConfig (RecoveryCalls.code (fun j => (pieces K c j).states) k) (initialConfiguration (pieces K c k).machine A)

/-- The graph's stopped configuration with the tapes `A` (every head at `0`). -/
noncomputable def stopAt (K : Kit s P g) (c : Cfg) (A : Fin (T K) → List Bool) : (prog K c).Config :=
  RecoveryCalls.stopped (fun j => (pieces K c j).states) (fun _ => 0) A

end

/-- A live source index for the final length `n` (what `Recovery3.AfterRun.run` grants, with the cutoff read as the
succinct verifier's onset). -/
structure Live (s : WS35) (g : WQ) (n ν : ℕ) : Prop where
  pos : 1 ≤ ν
  arity : g.coreArity s ν ≤ n / 2
  onset : s.SV.onset ≤ ν
  amp : 1 ≤ g.copies (g.width s ν)
  ampLarge : g.amp.arityCoefficient ≤ g.copies (g.width s ν)
  sel : ν = g.sel n

/-- At a live index, `ν < q ≤ m(q) ≤ n/2` (`copies(q) ≥ 1`). -/
theorem Live.width_le {s : WS35} {g : WQ} {n ν : ℕ} (h : Live s g n ν) :
    ν < g.width s ν ∧ g.width s ν ≤ g.coreArity s ν ∧ g.coreArity s ν ≤ n / 2 := by
  refine ⟨g.nu_lt_width s ν, ?_, h.arity⟩
  unfold WQ.coreArity WQ.tableArity
  have := h.amp
  nlinarith

/-- `StageBudget d` at the capacity parameters `(A, B)` and the cost constants `(C, E)`. -/
def StageBudgetAt (d A B C E : ℕ) : Prop :=
  ∀ (n w R : ℕ) (vals : List Bool) (hw : w ≤ R) {m : ℕ} (x : BitInput m),
    R ≤ n → vals.length = 2 ^ w →
    originalWorkspace R (oracleSizeBound d R) vals.length vals.length ≤ CloseoutCapacity.capacity A B n ∧
    (DedupBytes.fields (ENP.unitPCP w vals)).length ≤ CloseoutCapacity.capacity A B n ∧
    2 ^ R ≤ CloseoutCapacity.capacity A B n ∧
    (0 < oracleSizeBound d R →
      ENP.UStage.cost d w R (CloseoutCapacity.capacity A B n) vals hw x ≤ C * (2 ^ n + 1) ^ E)

/-- **The tail after stage 2** (the near-cubic-gates paper's uniform recovery, stage 3 and the two last branches): entering piece 24 (the copies of
`frame O*`) with stage 2's table `O*` on its table tape and the words of the preparation on the shared tapes, the
program stops with the gate core's bit on the output tape, within `C (2^n + 1)^E`. -/
def TailRuns {s : WS35} {P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm} {g : WQ} (K : Kit s P g) (c : Cfg) : Prop :=
  ∀ C0 E0 : ℕ, StageBudgetAt g.degree c.A c.B C0 E0 →
  ∃ C E : ℕ, ∀ (n : ℕ) (point : BitInput n) (ν : ℕ) (z : BitInput (2 ^ ν)) (A : Fin (T K) → List Bool)
    (h1 : g.SrcExists s ν z) (h2 : g.AcceptedOracle s ν z h1),
    Live s g n ν → K.ht.cutoff ≤ 2 ^ ν →
    A (tbl K) = RepairOrdinary.frame (List.ofFn (Classical.choice (existsFirstTable _ h2)).table) →
    A (sh K 1) = RepairOrdinary.frame (List.ofFn point) →
    (A (sh K 3)).length ≤ CloseoutCapacity.capacity c.Aq c.Bq n →
    A (sh K 9) = List.replicate ν true →
    A (sh K 10) = List.replicate (g.width s ν) true →
    A (sh K 11) = List.replicate (CloseoutCapacity.capacity c.A c.B n) true →
    A (sh K 12) = List.replicate (g.width s ν) true →
    A (sh K 13) = List.replicate (g.bound s ν) true →
    A (sh K 15) = List.replicate (CloseoutCapacity.capacity c.Aq c.Bq n) true →
    A (sh K 17) = PCPPNative.descriptor (g.firstSrc s ν z h1) →
    A (sh K 2) = [] → A (sh K 21) = [] → A (sh K 22) = [] → A (sh K 23) = [] → A (sh K 24) = [] →
    A (sh K 31) = [] →
    (∀ x : Fin (T K), off K 24 ≤ x.val → A x = []) →
    ∃ cost, cost ≤ C * (2 ^ n + 1) ^ E ∧ ∃ B : Fin (T K) → List Bool,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 24 A) (stopAt K c B) ∧
      B (sh K 2) = RepairOrdinary.frame (g.gateCore s P g.amp ν z
        (CloseoutLanguage.clauseWidth g.clauseDegree (g.width s ν)) g.positionLog n point).toNat.bits

/-- The clear driver covers stage 2's query: the cost bound of `ENP.TStage` on the word of `C_{⟨B⟩_ν}` that the A-run
returns for a source circuit `B` within the `q^G` cap (its descriptor is at most `39 (q + B + 5)^2` long,
`PCPPNative.descriptor_cap`; the word is at most the A-run's inputs plus its fuel long, `CheckedPCPP.Dock.ready_len`;
`ℓ ≤ q`, `Outer.ell_le_width`) is at most the clear capacity `2^{Aq n + Bq}`. -/
def QFits {s : WS35} {P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm} {g : WQ} (K : Kit s P g) (c : Cfg) : Prop :=
  ∀ n ν : ℕ, Live s g n ν →
    K.ts.K * (2 ^ g.width s ν + (39 * (g.width s ν + g.bound s ν + 5) ^ 2 + ν +
      (aR s g).K * (ν + 1) ^ (aR s g).e) + 1) ^ K.ts.e ≤ CloseoutCapacity.capacity c.Aq c.Bq n

/-- **The middle segment** (the near-cubic-gates paper's uniform recovery: "Second, the algorithm of imp:short-pcp is run deterministically on
`⟨B*_src⟩_ν` …; a formula with one variable per oracle address … finds the first oracle `O*` … If no oracle `O*`
exists at an exceptional initial source length, the second stage detects that case"): entering piece 18 (the query
clear) after stage 1 found `B*_src`, the program clears the query, converts stage 1's canonical description of `B*_src`
to its native descriptor (proof 1's converter, then `unframe`), runs the A-run and stage 2, and enters piece 24 with
`O*` on stage 2's table tape when an honest oracle exists, piece 23 (`false`) otherwise; the shared tapes other than
`3, 7, 8, 16, 17, 18` are kept, DESC (`17`) holds the native descriptor of `B*_src`, the query is at most the clear
capacity long, and the blocks from piece 23 on are still blank. -/
def MidRuns {s : WS35} {P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm} {g : WQ} (K : Kit s P g) (c : Cfg) : Prop :=
  QFits K c →
  ∃ C E : ℕ, ∀ (n : ℕ) (ν : ℕ) (z : BitInput (2 ^ ν)) (A : Fin (T K) → List Bool) (h1 : g.SrcExists s ν z),
    Live s g n ν →
    A (sh K 14) = RepairOrdinary.frame
      (OuterPCPRecovery.canonicalBoundedCircuitDescription (g.bound s ν) (g.firstSrc s ν z h1)) →
    (A (sh K 3)).length ≤ CloseoutCapacity.capacity c.Aq c.Bq n →
    A (sh K 15) = List.replicate (CloseoutCapacity.capacity c.Aq c.Bq n) true →
    A (sh K 7) = List.replicate (g.width s ν) true →
    A (sh K 8) = List.replicate (g.bound s ν) true →
    A (sh K 9) = List.replicate ν true →
    A (sh K 16) = [] → A (sh K 17) = [] → A (sh K 18) = [] →
    (∀ x : Fin (T K), off K 18 ≤ x.val → A x = []) →
    ∃ cost, cost ≤ C * (2 ^ n + 1) ^ E ∧ ∃ A' : Fin (T K) → List Bool,
      (∀ i : Fin 32, i ∉ [3, 7, 8, 16, 17, 18] → A' (sh K i) = A (sh K i)) ∧
      A' (sh K 17) = PCPPNative.descriptor (g.firstSrc s ν z h1) ∧
      (A' (sh K 3)).length ≤ CloseoutCapacity.capacity c.Aq c.Bq n ∧
      (∀ x : Fin (T K), off K 23 ≤ x.val → A' x = []) ∧
      (∀ h2 : g.AcceptedOracle s ν z h1,
        OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 18 A) (start K c 24 A') ∧
        A' (tbl K) = RepairOrdinary.frame (List.ofFn (Classical.choice (existsFirstTable _ h2)).table)) ∧
      ((¬ g.AcceptedOracle s ν z h1) →
        OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 18 A) (start K c 23 A'))

/-- The after-prefix program's entry bank: `frame z ++ post` on shared `0`, `frame point` on shared `1`. -/
noncomputable def entry {s : WS35} {P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm} {g : WQ} (K : Kit s P g) {n ν : ℕ}
    (point : BitInput n) (z : BitInput (2 ^ ν)) (post : List Bool) : Fin (T K) → List Bool :=
  afterBank (sh K 0) (sh K 1) (RepairOrdinary.frame (List.ofFn z) ++ post) (RepairOrdinary.frame (List.ofFn point))

/-- **The head segment** (the near-cubic-gates paper's uniform recovery: "First, a formula over the description of `B_src` with the `N` constraints
(eq:source-check) … finds the first source circuit `B*_src`, or shows that there is none, in which case the table is
`X_z`"): from the entry bank, the preparation (pieces 0–15: `frame z` copies, `1^q` ×4, `1^ν`, `1^W` ×2, the clear
driver `1^{2^{Aq n + Bq}}`, `1^B` ×2) and stage 1 (piece 16) enter piece 18 when `B*_src` exists (its canonical
description on DS1, shared `14`), piece 17 (Case 1 (i)) otherwise. The query is at most stage 1's cost bound
`C0 (2^n + 1)^E0` long; the blocks from piece 17 on are still blank. -/
def HeadRuns {s : WS35} {P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm} {g : WQ} (K : Kit s P g) (c : Cfg) : Prop :=
  ∀ C0 E0 : ℕ, StageBudgetAt g.degree c.A c.B C0 E0 →
  ∃ C E : ℕ, ∀ (n : ℕ) (point : BitInput n) (ν : ℕ) (z : BitInput (2 ^ ν)) (post : List Bool),
    Live s g n ν →
    ∃ cost, cost ≤ C * (2 ^ n + 1) ^ E ∧ ∃ A' : Fin (T K) → List Bool,
      A' (sh K 0) = RepairOrdinary.frame (List.ofFn z) ++ post ∧
      A' (sh K 1) = RepairOrdinary.frame (List.ofFn point) ∧
      A' (sh K 2) = [] ∧
      (A' (sh K 3)).length ≤ C0 * (2 ^ n + 1) ^ E0 ∧
      A' (sh K 7) = List.replicate (g.width s ν) true ∧
      A' (sh K 8) = List.replicate (g.bound s ν) true ∧
      A' (sh K 9) = List.replicate ν true ∧
      A' (sh K 10) = List.replicate (g.width s ν) true ∧
      A' (sh K 11) = List.replicate (CloseoutCapacity.capacity c.A c.B n) true ∧
      A' (sh K 12) = List.replicate (g.width s ν) true ∧
      A' (sh K 13) = List.replicate (g.bound s ν) true ∧
      A' (sh K 15) = List.replicate (CloseoutCapacity.capacity c.Aq c.Bq n) true ∧
      A' (sh K 16) = [] ∧ A' (sh K 17) = [] ∧ A' (sh K 18) = [] ∧ A' (sh K 21) = [] ∧ A' (sh K 22) = [] ∧
      A' (sh K 23) = [] ∧ A' (sh K 24) = [] ∧ A' (sh K 31) = [] ∧
      (∀ x : Fin (T K), off K 17 ≤ x.val → A' x = []) ∧
      (∀ h1 : g.SrcExists s ν z,
        OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 0 (entry K point z post))
          (start K c 18 A') ∧
        A' (sh K 14) = RepairOrdinary.frame
          (OuterPCPRecovery.canonicalBoundedCircuitDescription (g.bound s ν) (g.firstSrc s ν z h1))) ∧
      (¬ g.SrcExists s ν z →
        OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 0 (entry K point z post))
          (start K c 17 A'))

/-- **The second half of the head** (pieces 11–16: the capacities `1^W` ×2 and the clear driver, the caps `1^B` ×2,
stage 1): entering piece 11 with the first half's words (`frame z` on X1, `1^q` on Q1, QC, Q3, Q4, `1^ν` on NU), the
conclusion of `HeadRuns` holds from `start K c 11 A`. -/
def HeadTwoRuns {s : WS35} {P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm} {g : WQ} (K : Kit s P g) (c : Cfg) : Prop :=
  ∀ C0 E0 : ℕ, StageBudgetAt g.degree c.A c.B C0 E0 →
  ∃ C E : ℕ, ∀ (n : ℕ) (point : BitInput n) (ν : ℕ) (z : BitInput (2 ^ ν)) (post : List Bool)
    (A : Fin (T K) → List Bool), Live s g n ν →
    A (sh K 0) = RepairOrdinary.frame (List.ofFn z) ++ post →
    A (sh K 1) = RepairOrdinary.frame (List.ofFn point) →
    A (sh K 4) = RepairOrdinary.frame (List.ofFn z) →
    A (sh K 5) = List.replicate (g.width s ν) true →
    A (sh K 7) = List.replicate (g.width s ν) true →
    A (sh K 9) = List.replicate ν true →
    A (sh K 10) = List.replicate (g.width s ν) true →
    A (sh K 12) = List.replicate (g.width s ν) true →
    (∀ i : Fin 32, i ∈ [2, 3, 6, 8, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 31] → A (sh K i) = []) →
    (∀ x : Fin (T K), off K 11 ≤ x.val → A x = []) →
    ∃ cost, cost ≤ C * (2 ^ n + 1) ^ E ∧ ∃ A' : Fin (T K) → List Bool,
      A' (sh K 0) = RepairOrdinary.frame (List.ofFn z) ++ post ∧
      A' (sh K 1) = RepairOrdinary.frame (List.ofFn point) ∧
      A' (sh K 2) = [] ∧
      (A' (sh K 3)).length ≤ C0 * (2 ^ n + 1) ^ E0 ∧
      A' (sh K 7) = List.replicate (g.width s ν) true ∧
      A' (sh K 8) = List.replicate (g.bound s ν) true ∧
      A' (sh K 9) = List.replicate ν true ∧
      A' (sh K 10) = List.replicate (g.width s ν) true ∧
      A' (sh K 11) = List.replicate (CloseoutCapacity.capacity c.A c.B n) true ∧
      A' (sh K 12) = List.replicate (g.width s ν) true ∧
      A' (sh K 13) = List.replicate (g.bound s ν) true ∧
      A' (sh K 15) = List.replicate (CloseoutCapacity.capacity c.Aq c.Bq n) true ∧
      A' (sh K 16) = [] ∧ A' (sh K 17) = [] ∧ A' (sh K 18) = [] ∧ A' (sh K 21) = [] ∧ A' (sh K 22) = [] ∧
      A' (sh K 23) = [] ∧ A' (sh K 24) = [] ∧ A' (sh K 31) = [] ∧
      (∀ x : Fin (T K), off K 17 ≤ x.val → A' x = []) ∧
      (∀ h1 : g.SrcExists s ν z,
        OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 11 A) (start K c 18 A') ∧
        A' (sh K 14) = RepairOrdinary.frame
          (OuterPCPRecovery.canonicalBoundedCircuitDescription (g.bound s ν) (g.firstSrc s ν z h1))) ∧
      (¬ g.SrcExists s ν z →
        OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 11 A) (start K c 17 A'))

end NearCubicGates.Close.Recovery3.After

