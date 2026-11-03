import W3.Joins.Front
import Worker.Format
import W3.Proof.CaseAnalysis.WitnessSourcePolicyCall
import Proof.PCP.PCPPQueryIndexPadding
import Outer.Apply
import Proof.CaseAnalysis.WitnessSoundness
import Proof.Foundations.SourceCore
import Proof.Hierarchy.CompetitorSourceAverage
import W3.Aliases
import W3.Joins.Cases
import W3.Proof.CaseAnalysis.Language

/-!
# The worker's cold-native front end `ColdNativeW`

The near-cubic-wires paper (the machine on one input length): "It rejects without guessing unless n = N_ν … guesses three things …
The source circuit B_src … The proof circuit B_pf … It deterministically rejects a branch if any description … is
malformed … fails the fixed general-circuit size bound q^G or, for B_src, the description-length bound λ_ν. It then
checks (C.10.0) … runs the algorithm of Fact C.1 … substitutes … and applies Fact C.2 to H_B" (C.10;
D6: the oracle field is `natWord ⟨B_src⟩ ++ natWord ⟨B_pf⟩`, gates `Worker.Decodes`).

**Why a waist.** The old worker's cold front end (`ColdOracle`, `SelectedOracle`, `SelectedStreams`, `NativeCache`,
`HierarchySelectedSource`, `PCPPNativeHierarchy*`; 63 modules / 4.9k lines, all typed by the CLW 3.10 projection source)
is dropped. Everything above it (ColdLegal, ColdFamily, BoundedFamily, FinalCache*, FinalAdmittedEntry, …)
reads it ONLY through `ColdNative.{tapes, machine, input, budget, bound, passed, request, cacheSlots, lengthSlot,
flagSlot, originalTape, project, native_run(_with_originals)}` plus layout disjointness. `ColdNativeW` is exactly that
API as data + properties (consumer-backward), with the request at the substituted outer verifier (`requestAt`) and
the guard predicate `Passes` of the paper. Producer (separate obligation): cold prefix (guards, width donor, D6 split +
proof 1's cold decoder ×2, size caps) → `F.M` (`FrontSpecD`, JF) → gate on `Guard` → `NativeSourceDock` → policy call.
-/

set_option autoImplicit false

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close

namespace W3.NearCubicWires.RepairSource.Outer3

/-- The guards of the cold-native front end at input `x` and oracle field `raw` (the near-cubic-wires paper + (C.10.0)): `n` is
dyadic and its index is past the cutoff and the producer's onset, the field decodes to a pair `B` on `q(n)` inputs
(D6), both circuits within `q^G` gates, `B_src` within `λ_ν` bits and passing the check. -/
def Passes (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
    (SV : Outer.SuccinctVerifier H L) (cutoff onset degree : ℕ) {n : ℕ} (x : BitInput n) (raw : List Bool) : Prop :=
  n = 2 ^ Nat.log 2 n ∧ cutoff ≤ Nat.log 2 n ∧ onset ≤ Nat.log 2 n ∧ SV.onset ≤ Nat.log 2 n ∧
  ∃ B : Outer.OuterGuess (Outer.width mw SV n), Worker.Decodes (Outer.width mw SV n) raw B ∧
    B.src.size ≤ oracleSizeBound degree (Outer.width mw SV n) ∧
    B.pf.size ≤ oracleSizeBound degree (Outer.width mw SV n) ∧
    Outer.SrcFits L (Nat.log 2 n) B.src ∧ Outer.CheckAt (Nat.log 2 n) x B.src

/-- The one-time policy fields (old `SourcePolicy.Call.Fields`), read at the slots `policySlots` of the front end's own
bank (old `ColdLegal.sourceSlots` = `ColdNative.slots ∘ NativePipeline.localSlots ∘ NativePolicy.policySlots`). -/
structure PolicyAt (D copies : ℕ) (delta : ℚ) {t n0 s : ℕ}
    (policySlots : Fin (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.tapes D) → Fin t)
    (r : PCPPRequest n0) (p : NearCubicWires.SourceInterfaces.PointwisePCPP r.circuit) (cfg : Configuration t s) :
    Prop where
  count : cfg.tapes (policySlots (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.countSlots D 40)) =
    List.replicate (p.systematicBits + p.auxiliaryBits) true
  clause : cfg.tapes (policySlots (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.countSlots D 38)) =
    List.replicate p.clauseBits true
  q0 : cfg.tapes (policySlots (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.q0Slot D)) =
    List.replicate (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.CorePolicy.q0 D r.arity) true
  cap : cfg.tapes (policySlots (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.capSlot D)) =
    List.replicate (natBitLength (_root_.NearCubicWires.RepairSource.CloseoutXor.cap delta
      (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.CorePolicy.q0 D r.arity) copies * max 1 (2 * 2 ^ p.clauseBits)))
      true
  cursor : ∀ i, cfg.heads (policySlots i) = W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.heads D i

/-- **`ColdNativeW`**: the worker's cold-native front end at `mw SV`, Fact C.2's algorithm `a`, cutoff,
policy parameters `D copies delta`, oracle exponent `degree`. -/
structure ColdNativeW (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
    (SV : Outer.SuccinctVerifier H L) (a : PointwisePCPPAlgorithm) (cutoff D degree copies : ℕ) (delta : ℚ) where
  tapes : ℕ
  st : ℕ
  machine : Machine tapes st
  input : List Bool → List Bool → Fin tapes → List Bool
  budget : (n : ℕ) → BitInput n → List Bool → ℕ
  lengthSlot : Fin tapes
  flagSlot : Fin tapes
  originalTape : Fin tapes
  cacheSlots : Fin 19 → Fin tapes
  policySlots : Fin (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.tapes D) → Fin tapes
  onset : ℕ
  passed : List Bool → List Bool → Bool
  passed_iff : ∀ {n : ℕ} (x : BitInput n) (raw : List Bool),
    passed (List.ofFn x) raw = true ↔ Passes mw SV cutoff onset degree x raw
  /-- old `ColdNative.native_run_with_originals` -/
  run : ∀ {n : ℕ} (x : BitInput n) (raw : List Bool), 16 * raw.length ≤ n →
    ∃ actual : ExecutionReceipt tapes st,
      (passed (List.ofFn x) raw = true → actual.final.tapes originalTape = frame (List.ofFn x)) ∧
      run machine (budget n x raw) (input (List.ofFn x) raw) = some actual ∧
      actual.steps ≤ budget n x raw ∧
      actual.final.tapes lengthSlot = List.replicate n true ∧ actual.final.heads lengthSlot = 0 ∧
      actual.final.heads flagSlot = 0 ∧
      readTapeBit (actual.final.tapes flagSlot) 0 = passed (List.ofFn x) raw ∧
      ∀ B : Outer.OuterGuess (Outer.width mw SV n), passed (List.ofFn x) raw = true →
        Worker.Decodes (Outer.width mw SV n) raw B →
        let r := requestAt mw SV a (Nat.log 2 n) B
        (∀ j : Fin 19, actual.final.tapes (cacheSlots j) =
          PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
            (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) [] j) ∧
        (∀ j : Fin 19, actual.final.heads (cacheSlots j) = PCPPQueryClauseReuse.heads j) ∧
        PolicyAt D copies delta policySlots r (a.output r) actual.final
  /-- old `ColdNative.bound(_polynomial)`, in the paper's form (l.5602–5619): `N^{d_chk} · q^{O(1)}` with `d_chk = 2`
  (JF's cost class; the runtime ledger WORKa turns it into `RuntimeSplit`). -/
  budget_bound : ∃ C e : ℕ, ∀ (n : ℕ) (x : BitInput n) (raw : List Bool), 16 * raw.length ≤ n →
    budget n x raw ≤ C * (n + 1) ^ 2 * (Outer.width mw SV n + 1) ^ e
  cache_injective : Function.Injective cacheSlots
  cache_ne_original : ∀ j, cacheSlots j ≠ originalTape
  cache_ne_length : ∀ j, cacheSlots j ≠ lengthSlot
  cache_ne_flag : ∀ j, cacheSlots j ≠ flagSlot
  length_ne_flag : lengthSlot ≠ flagSlot
  original_ne_length : originalTape ≠ lengthSlot
  original_ne_flag : originalTape ≠ flagSlot
  policy_injective : Function.Injective policySlots
  /-- the policy reads its two inputs from cache slots 0 (`pcppOutput`) and 13 (the arity template); every other
  policy slot is fresh (old `ColdLegal.local_cache`, `domain_slot`). -/
  policy_cache : ∀ i j, policySlots i = cacheSlots j →
    (i.val = 0 ∧ j = 0) ∨ (i = W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.coreSlot D ∧ j = 13)
  policy_core : policySlots (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.coreSlot D) = cacheSlots 13
  policy_ne_original : ∀ i, policySlots i ≠ originalTape
  policy_ne_length : ∀ i, policySlots i ≠ lengthSlot
  policy_ne_flag : ∀ i, policySlots i ≠ flagSlot
  /-- the input bank (old `ColdInput.oracle_input`): `frame x` on tape 2, the oracle field `frame raw` on `oracleIndex`,
  every other tape blank (the entry contract of the layer above). -/
  oracleIndex : ℕ
  two_lt : 2 < oracleIndex
  oracle_lt : oracleIndex < tapes
  input_eq : ∀ (x raw : List Bool) (i : Fin tapes),
    input x raw i = if i.val = oracleIndex then frame raw else if i.val = 2 then frame x else []

/-! ## Consumer docks -/

end W3.NearCubicWires.RepairSource.Outer3
