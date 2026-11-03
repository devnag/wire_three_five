import Lean
import Proof.Wire_3_5.UnionMachine.PlanW2
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Assembly.Free
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.UnionCodec
import Proof.Wire_3_5.UnionMachine.UnionEventual
import Proof.Wire_3_5.UnionMachine.Plan
import Proof.Wire_3_5.UnionMachine.Slack
import Proof.Wire_3_5.UnionMachine.PlanW2Base


noncomputable section


/-! # C6: leaf U's enclosing application with the paper's atom test

"The weak machine guesses the two circuits `Γ_src` and `Γ_pf` above, a class tag, and one sparse grid sum for each
distinct PCPP variable. It rejects malformed descriptions, oversized atoms, and coefficients outside the fixed grid, and
it rejects unless `Γ_src` passes the source check" (paper v2, §H.5).
The plan of `WireExponent3_5UnionMachinePlanW2` with ONE correction to the worker's meaning: past its onset the
union machine accepts a witness only if EVERY decoded atom is within the description envelope the paper fixes
(**`atomsOk`**: `descriptionBits ≤ (q+1)^descDeg`, the envelope of `PrimitiveInputs.Call`), before it selects the common
star translation. Without it the selection's input (every positive-weight variable's carrier, zero-sign atoms included)
is unbounded while C1's contract takes inputs of size `≤ (q+1)^d` for one `d` fixed before the witness (the F1
finding: an auxiliary variable met only in all-positive clauses with all signs `0` is named by no scheduled call).
Soundness is unaffected (the conjunct only restricts acceptance); completeness reads one more residual,
**`AtomsHonest S P`**: eventually, every accepting guess has an accepting guess with every atom in the envelope.

* **`AtomsOkG`**, **`atomsOk`**, **`workerMeaning2`**; **`WorkerAt3`** (`WorkerAt` at `workerMeaning2`), its
  `soundForSlack`, `oneSided`, **`complete`** (from `AtomsHonest`), `split`;
* the leaf from workers at margin `e` (`WorkersFE3`, `leafAtPosE3`, `unionLeafF_of_workersE3`; the coefficient-`0`
  branch is `PlanW2.leafAtZeroE`);
* **`FrontAtW3`** (`FrontAtW` with `sem ↔ workerMeaning2`), `FrontsFWE3`, the worker's assembly and time (PlanW's, at
  `FrontAtW3`), **`union_planW3 c1 dec fronts count acc facts atoms : ∀ l, UnionLeafF l`**.

Paper quantity of the main type: `UnionLeafF l`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.PlanW3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.ExtDecompositionBatch NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.Bindings.CLW20Theorem113
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW NearCubicWires.WireExponent3_5.UnionMachine.PlanW2 Filter
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)

/-! ## The worker's meaning with the atom test -/

section Worker
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- **The paper's atom test on a guess** (P3:3670): every grid atom within the description envelope of
`PrimitiveInputs.Call`, `descriptionBits ≤ (q+1)^descDeg`. -/
def AtomsOkG {S : UnionSetup I} {N : ℕ} {z : BitInput N} (g : UnionGuess S z) : Prop :=
  ∀ X a, g.mode.descriptionBits (g.atom X a) ≤ (g.q + 1) ^ I.descDeg

/-- **The atom test on a witness**: the decoded guess (if any) passes `AtomsOkG`. -/
def atomsOk (S : UnionSetup I) {N : ℕ} (z : BitInput N) (w : List Bool) : Prop :=
  ∀ g, decodeGuess S z w = some g → AtomsOkG g

/-- **The worker's meaning** (P3:3669-3691): past its onset, every atom within the envelope and
the union machine's slack run on the witness; below the onset the machine rejects outright (P3:3675-3680). -/
def workerMeaning2 (S : UnionSetup I) (P : FusedPrimitive I) (onset : ℕ) (callOk : PrimRequest → Bool) :
    (n : ℕ) → BitInput n → List Bool → Prop :=
  fun n x w => onset ≤ n ∧ atomsOk S x w ∧ unionSlackRun S x UnionGuess.translation callOk P unionBits w = true

/-- **The union worker with the atom test**: `Plan.WorkerAt` at `workerMeaning2`. -/
structure WorkerAt3 (S : UnionSetup I) (P : FusedPrimitive I) where
  t : ℕ
  s : ℕ
  p : Machine t s
  ht : 2 ≤ t
  result : Fin t
  fuel : ℕ → ℕ
  onset : ℕ
  callOk : PrimRequest → Bool
  run : WitnessRun p ht result fuel (workerMeaning2 S P onset callOk)
  hok : ∀ N, onset ≤ N → ∀ (z : BitInput N) (g : UnionGuess S z), ∀ r ∈ (g.checkData g.translation).schedule,
    callOk r = true ↔ I.Call r
  time : ∀ N, B.onset ≤ N → fuel N + 2 ≤ B.A * (N + 1) ^ B.a + B.q N ^ E.callDeg * B.callBudget (B.q N)

variable {S : UnionSetup I} {P : FusedPrimitive I}

namespace WorkerAt3

/-- The worker's weak machine. -/
noncomputable def machine (W : WorkerAt3 S P) : OrdinaryWeakMachine := weakOf W.p W.ht W.result W.fuel _ W.run

/-- **Slack soundness** of the worker's machine (the atom test only restricts acceptance). -/
theorem soundForSlack (W : WorkerAt3 S P) : SoundForSlack S P unionBits W.machine := by
  intro N z hacc
  obtain ⟨w, hon, -, hrun⟩ := (weakOf_accepts W.p W.ht W.result W.fuel _ W.run N z).1 hacc
  exact unionSlackRun_sound P unionBits W.callOk (W.hok N hon z) _ hrun

/-- **`tr:soundness`**: the worker's machine is one-sided for the setup's language. -/
theorem oneSided (W : WorkerAt3 S P) {L : Language} (hF : SetupFacts S L) : OneSided W.machine L := by
  have h := oneSided_of_soundForSlack S P unionBits W.machine W.soundForSlack hF.hw hF.hD
  rwa [hF.lang] at h

/-- **`tr:time`**: the worker's machine meets the ledger's split. -/
theorem split (W : WorkerAt3 S P) : B.Split W.machine := fun N hN => W.time N hN

end WorkerAt3

end Worker

/-! ## Layer A at margin `e` -/

section Leaf
variable (l : Literals)

/-- **Workers with the atom test** for every positive coefficient, primitive and language, with one source-work
constant `A ≥ 3` chosen before the coefficient. -/
def WorkersFE3 (e : ℕ) (F : GateFree l) : Type :=
  Σ A : ℕ, Σ' _ : 3 ≤ A, ∀ (coef : ℕ), 1 ≤ coef → ∀ (P : FusedPrimitive (IUE l F e coef A)) (L : Language)
    (hL : InNTIME (fun n => n ^ (kE l e + 2)) L), WorkerAt3 (SUE l F e coef A L hL) P

end Leaf

/-! ## Residual U0–U5: the front with the atom test -/

section Front
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}
variable (P : FusedPrimitive I)

/-- **Residual U0–U5, the front** (`PlanW.FrontAtW`) whose semantics is the worker's meaning with the atom test. -/
structure FrontAtW3 (S : UnionSetup I) {d : ℕ} (c1 : C1At d) (Af Kf N₀ : ℕ) where
  tf : ℕ
  sf : ℕ
  M : Machine (NW P tf) sf
  cost : ℕ → ℕ
  onset : ℕ
  honset : N₀ ≤ onset
  callOk : PrimRequest → Bool
  hok : ∀ N, onset ≤ N → ∀ (z : BitInput N) (g : UnionGuess S z), ∀ r ∈ (g.checkData g.translation).schedule,
    callOk r = true ↔ I.Call r
  out : (N : ℕ) → BitInput N → List Bool → FrontOut I
  run : ∀ N (x : BitInput N) (w : List Bool), w.length = N / 16 → ∃ (Hf : Fin (NW P tf) → ℕ) (Af' : Fin (NW P tf) → List Bool),
    Step M (cost N) (fun _ => 0) (entryA x w) Hf Af' ∧
    (∀ i, Hf (lp P tf i) = bankH P ((out N x w).kept P) i) ∧
    (∀ i, Af' (lp P tf i) =
      bankA P (out N x w).cap (out N x w).R (out N x w).Lg ((out N x w).kept P) i)
  loop : ∀ N (x : BitInput N) (w : List Bool), w.length = N / 16 → (out N x w).table ≠ [] →
    LoopHyps (out N x w).cap (out N x w).R (out N x w).Lg (out N x w).p (B.q N) (out N x w).Mm (out N x w).Wm
      (out N x w).acc0 (out N x w).table
  capPos : ∀ N (x : BitInput N) (w : List Bool), w.length = N / 16 → 1 ≤ (out N x w).cap
  accFit : ∀ N (x : BitInput N) (w : List Bool), w.length = N / 16 → ∀ i,
    ((out N x w).keptEnd P).acc i ≤ (out N x w).cap
  sem : ∀ N (x : BitInput N) (w : List Bool), w.length = N / 16 →
    (decisionOf ((out N x w).keptEnd P).acc = true ↔ workerMeaning2 S P onset callOk N x w)
  rej : ∀ N (x : BitInput N) (w : List Bool), w.length = N / 16 → N < onset → (out N x w).table = [] ∧ (out N x w).cap = 1
  costRej : ∀ N, B.onset ≤ N → N < onset → cost N ≤ Af * (N + 1) ^ B.a
  costAcc : ∀ N, B.onset ≤ N → onset ≤ N → cost N ≤ Af * (N + 1) ^ B.a +
    Kf * (B.q N + 1) ^ (callDegMargin - 1) * (B.callBudget (B.q N) + c1.budgetAt B (B.q N))
  len : ∀ N (x : BitInput N) (w : List Bool), w.length = N / 16 → onset ≤ N → (out N x w).table ≠ [] → ∃ g : UnionGuess S x,
    UnionGuards S x g ∧
      (out N x w).table.length ≤ (g.checkData g.translation).schedule.length
  perCall : ∀ N (x : BitInput N) (w : List Bool), w.length = N / 16 → onset ≤ N → (out N x w).table ≠ [] →
    Sched.loopCost (out N x w).Mm (out N x w).Wm (B.callBudget (B.q N)) (out N x w).p (out N x w).R + 2 ≤
      Kf * (B.q N + 1) ^ (callDegMargin - 1) * B.callBudget (B.q N)
  capAcc : ∀ N (x : BitInput N) (w : List Bool), w.length = N / 16 → onset ≤ N →
    (out N x w).cap + 1 ≤ Kf * (B.q N + 1) ^ (callDegMargin - 1) * B.callBudget (B.q N)

end Front

/-- **Residual U0–U5 with the atom test** at the gate (`PlanW2.FrontsFWE` at `FrontAtW3`). -/
def FrontsFWE3 (e : ℕ) (l : Literals) (F : GateFree l) : Type :=
  Σ Af : ℕ, ∀ (coef : ℕ), 1 ≤ coef → ∀ (A : ℕ) (P : FusedPrimitive (IUE l F e coef A)) (L : Language)
    (hL : InNTIME (fun n => n ^ (kE l e + 2)) L), Σ d : ℕ, ∀ c1 : C1At d, Σ Kf : ℕ, ∀ N₀ : ℕ,
      FrontAtW3 P (SUE l F e coef A L hL) c1 Af Kf N₀

/-! ## The worker: front, loop, decision (PlanW's assembly at `FrontAtW3`) -/

section Assembly
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {P : FusedPrimitive I}
  {S : UnionSetup I} {d₁ : ℕ} {c1 : C1At d₁} {Af Kf N₀ Kd : ℕ}

/-- **The worker's machine**: the front, then the schedule loop docked at the bank's slots, then the decision. -/
noncomputable def workerMachineW3 (fr : FrontAtW3 P S c1 Af Kf N₀) (dc : DecideAt P Kd) :=
  Composition.machine fr.M (Composition.machine (RecoveryFocus.machine (lp P fr.tf) (Sched.loopM P))
    (RecoveryFocus.machine (lp P fr.tf) dc.M))

/-- **The worker's run on one input and witness**: front, loop, decision, with the decision on the result cell. -/
theorem worker_stepW3 (fr : FrontAtW3 P S c1 Af Kf N₀) (dc : DecideAt P Kd) (N : ℕ) (x : BitInput N) (w : List Bool)
    (hw : w.length = N / 16) :
    ∃ (Hend : Fin (NW P fr.tf) → ℕ) (Aend : Fin (NW P fr.tf) → List Bool),
      Step (workerMachineW3 fr dc) (fr.cost N + 1 + ((fr.out N x w).loopSteps (B.q N) + 1 +
        dc.cost (fr.out N x w).cap)) (fun _ => 0) (entryA x w) Hend Aend ∧
      readTapeBit (Aend (lp P fr.tf (cellSlot P))) (Hend (lp P fr.tf (cellSlot P))) =
        decisionOf ((fr.out N x w).keptEnd P).acc := by
  obtain ⟨Hf, Af', hfront, hH, hA⟩ := fr.run N x w hw
  set o := fr.out N x w with ho
  have hinj := lp_inj P fr.tf
  have hloop := (loop_step o (B.q N) (fr.loop N x w hw)).dock (lp P fr.tf) hinj Hf Af' hH hA
  obtain ⟨Hd, Ad, hdec, hbit⟩ := dc.run o.cap o.R o.Lg (o.keptEnd P) (fr.capPos N x w hw) (fr.accFit N x w hw)
  have hdecD := hdec.dock (lp P fr.tf) hinj
    (dockH (lp P fr.tf) Hf (bankH P (o.keptEnd P))) (install (lp P fr.tf) Af' (bankA P o.cap o.R o.Lg (o.keptEnd P)))
    (fun j => dockH_slot (lp P fr.tf) hinj _ _ j) (fun j => install_slot (lp P fr.tf) hinj _ _ j)
  refine ⟨_, _, hfront.seq (hloop.seq hdecD), ?_⟩
  rw [dockH_slot (lp P fr.tf) hinj, install_slot (lp P fr.tf) hinj]
  exact hbit

/-- The per-witness tail of the worker's run: the loop and the decision. -/
def tailStepsW3 (fr : FrontAtW3 P S c1 Af Kf N₀) (dc : DecideAt P Kd) (N : ℕ) (x : BitInput N) (w : List Bool) : ℕ :=
  (fr.out N x w).loopSteps (B.q N) + 1 + dc.cost (fr.out N x w).cap

/-- **The worker's fuel**: the front, then the longest tail over the inputs and `⌊N/16⌋`-bit witnesses. -/
noncomputable def workerFuelW3 (fr : FrontAtW3 P S c1 Af Kf N₀) (dc : DecideAt P Kd) (N : ℕ) : ℕ :=
  fr.cost N + 1 + Finset.univ.sup (fun xw : BitInput N × BitInput (N / 16) => tailStepsW3 fr dc N xw.1 (List.ofFn xw.2))

/-- **The worker realizes its meaning** on every input and witness (the result cell is the loop bank's cell). -/
theorem worker_runW3 (fr : FrontAtW3 P S c1 Af Kf N₀) (dc : DecideAt P Kd) :
    WitnessRun (workerMachineW3 fr dc) (two_le_NW P fr.tf) (lp P fr.tf (cellSlot P)) (workerFuelW3 fr dc)
      (workerMeaning2 S P fr.onset fr.callOk) := by
  intro n x w
  obtain ⟨Hend, Aend, hstep, hbit⟩ := worker_stepW3 fr dc n x (List.ofFn w) List.length_ofFn
  have hle : fr.cost n + 1 + tailStepsW3 fr dc n x (List.ofFn w) ≤ workerFuelW3 fr dc n :=
    Nat.add_le_add_left (Finset.le_sup (f := fun xw : BitInput n × BitInput (n / 16) =>
      tailStepsW3 fr dc n xw.1 (List.ofFn xw.2)) (Finset.mem_univ (x, w))) _
  obtain ⟨r, hr, hh, ht, _⟩ := hstep.enlarge hle
  refine ⟨r, hr, ?_⟩
  show readTapeBit (r.final.tapes _) (r.final.heads _) = true ↔ _
  rw [hh, ht, hbit]
  exact fr.sem n x (List.ofFn w) List.length_ofFn

/-- **`tr:time` for the worker (C7)**: the front's source work within `Af·(N+1)^a`; its one C1 call within
`callBudget` (`hsel`); every tail (the loop's calls and the decision) within the per-call factor times the schedule's
length, bounded by the count (`hcount`), and absorbed into `q^{callDeg}` by `GateFreeOK` (`habs`). -/
theorem worker_timeW3 (fr : FrontAtW3 P S c1 Af Kf N₀) (dc : DecideAt P Kd) (hKd : ∀ cap, dc.cost cap ≤ Kd * (cap + 1))
    (d : ℕ) (hA : Af + 2 * Kd + 8 ≤ B.A)
    (hcount : ∀ N, N₀ ≤ N → ∀ (z : BitInput N) (g : UnionGuess S z),
      UnionGuards S z g → ∀ tr : List ℕ,
        (g.checkData tr).schedule.length ≤ B.q N ^ d)
    (habs : ∀ N, N₀ ≤ N → Kf * (3 + Kd) * (B.q N + 1) ^ (d + (callDegMargin - 1)) ≤ B.q N ^ E.callDeg)
    (hsel : ∀ N, N₀ ≤ N → c1.budgetAt B (B.q N) ≤ B.callBudget (B.q N)) :
    ∀ N, B.onset ≤ N → workerFuelW3 fr dc N + 2 ≤ B.A * (N + 1) ^ B.a + B.q N ^ E.callDeg * B.callBudget (B.q N) := by
  intro N hN
  have hpow : 1 ≤ (N + 1) ^ B.a := Nat.one_le_pow _ _ (Nat.succ_pos N)
  have h3 : (Af + 2 * Kd + 8) * (N + 1) ^ B.a ≤ B.A * (N + 1) ^ B.a := Nat.mul_le_mul_right _ hA
  have h4 : Af * (N + 1) ^ B.a + (2 * Kd + 8) ≤ (Af + 2 * Kd + 8) * (N + 1) ^ B.a := by
    have : 2 * Kd + 8 ≤ (2 * Kd + 8) * (N + 1) ^ B.a := Nat.le_mul_of_pos_right _ hpow
    nlinarith
  by_cases hon : N < fr.onset
  · -- rejected outright: the empty table, a small bank
    have htail : ∀ xw : BitInput N × BitInput (N / 16), tailStepsW3 fr dc N xw.1 (List.ofFn xw.2) ≤
        2 + 2 * Kd := by
      intro xw
      obtain ⟨hnil, hcap⟩ := fr.rej N xw.1 (List.ofFn xw.2) List.length_ofFn hon
      have h1 := hKd (fr.out N xw.1 (List.ofFn xw.2)).cap
      rw [hcap] at h1
      unfold tailStepsW3 FrontOut.loopSteps
      rw [hnil, hcap]
      simp only [List.length_nil, zero_mul, zero_add]
      omega
    have hsup := Finset.sup_le (fun xw (_ : xw ∈ Finset.univ) => htail xw)
    have hc := fr.costRej N hN hon
    unfold workerFuelW3
    have h5 : B.A * (N + 1) ^ B.a ≤ B.A * (N + 1) ^ B.a + B.q N ^ E.callDeg * B.callBudget (B.q N) :=
      Nat.le_add_right _ _
    omega
  · -- past the onset: the calls
    have hon' : fr.onset ≤ N := Nat.le_of_not_lt hon
    have hN₀ : N₀ ≤ N := le_trans fr.honset hon'
    obtain ⟨q, hq⟩ : ∃ q, B.q N = q := ⟨_, rfl⟩
    have htail : ∀ xw : BitInput N × BitInput (N / 16), tailStepsW3 fr dc N xw.1 (List.ofFn xw.2) ≤
        2 + (q ^ d + Kd) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) := by
      intro xw
      have hd1 := hKd (fr.out N xw.1 (List.ofFn xw.2)).cap
      have hcapA := fr.capAcc N xw.1 (List.ofFn xw.2) List.length_ofFn hon'
      rw [hq] at hcapA
      have hd2 : dc.cost (fr.out N xw.1 (List.ofFn xw.2)).cap ≤
          Kd * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) :=
        le_trans hd1 (Nat.mul_le_mul_left _ hcapA)
      have hloop : (fr.out N xw.1 (List.ofFn xw.2)).loopSteps q ≤
          q ^ d * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) + 1 := by
        unfold FrontOut.loopSteps
        by_cases h0 : (fr.out N xw.1 (List.ofFn xw.2)).table = []
        · rw [h0]; simp
        · obtain ⟨g, hsize, hlen⟩ := fr.len N xw.1 (List.ofFn xw.2) List.length_ofFn hon' h0
          have hc := hcount N hN₀ xw.1 g hsize g.translation
          have hper := fr.perCall N xw.1 (List.ofFn xw.2) List.length_ofFn hon' h0
          rw [hq] at hc hper
          have := Nat.mul_le_mul (hlen.trans hc) hper
          omega
      unfold tailStepsW3
      rw [hq]
      have e : (q ^ d + Kd) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) =
          q ^ d * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) +
            Kd * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) := by ring
      omega
    have hsup := Finset.sup_le (fun xw (_ : xw ∈ Finset.univ) => htail xw)
    have hc := fr.costAcc N hN hon'
    have hs := hsel N hN₀
    have hab := habs N hN₀
    rw [hq] at hc hs hab
    -- the calls' part: `(2 + q^d + Kd)·Kf·X·b ≤ Kf(3+Kd)(q+1)^{d+m-1}·b ≤ q^{callDeg}·b`
    have hqd : q ^ d ≤ (q + 1) ^ d := Nat.pow_le_pow_left (Nat.le_succ q) d
    have hqd1 : 1 ≤ (q + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos q)
    have hcalls : Kf * (q + 1) ^ (callDegMargin - 1) * (B.callBudget q + c1.budgetAt B q) +
        (2 + (q ^ d + Kd) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q)) ≤
          2 + q ^ E.callDeg * B.callBudget q := by
      have e1 : Kf * (q + 1) ^ (callDegMargin - 1) * (B.callBudget q + c1.budgetAt B q) ≤
          2 * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) := by
        have := Nat.mul_le_mul_left (Kf * (q + 1) ^ (callDegMargin - 1)) (Nat.add_le_add_left hs (B.callBudget q))
        calc _ ≤ Kf * (q + 1) ^ (callDegMargin - 1) * (B.callBudget q + B.callBudget q) := this
          _ = 2 * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) := by ring
      have e2 : (2 + (q ^ d + Kd)) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) ≤
          (Kf * (3 + Kd) * (q + 1) ^ (d + (callDegMargin - 1))) * B.callBudget q := by
        rw [pow_add]
        have : 2 + (q ^ d + Kd) ≤ (3 + Kd) * (q + 1) ^ d := by nlinarith
        calc (2 + (q ^ d + Kd)) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q)
            ≤ ((3 + Kd) * (q + 1) ^ d) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) :=
              Nat.mul_le_mul_right _ this
          _ = Kf * (3 + Kd) * ((q + 1) ^ d * (q + 1) ^ (callDegMargin - 1)) * B.callBudget q := by ring
      have e3 := Nat.mul_le_mul_right (B.callBudget q) hab
      have e4 : (2 + (q ^ d + Kd)) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) =
          2 * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) +
            (q ^ d + Kd) * (Kf * (q + 1) ^ (callDegMargin - 1) * B.callBudget q) := by ring
      omega
    unfold workerFuelW3
    rw [hq]
    omega

end Assembly

/-! ## Layer B at the gate -/

section LeafB
variable (l : Literals)

/-- The worker from its stages at one coefficient, source work, primitive and language. -/
noncomputable def workerOfE3 (e : ℕ) (F : GateFree l) (coef A : ℕ) (P : FusedPrimitive (IUE l F e coef A)) (L : Language)
    (hL : InNTIME (fun n => n ^ (kE l e + 2)) L) {d₁ : ℕ} (c1 : C1At d₁) (Af Kf N₀ Kd : ℕ)
    (fr : FrontAtW3 P (SUE l F e coef A L hL) c1 Af Kf N₀) (dc : DecideAt P Kd)
    (hA : Af + 2 * Kd + 8 ≤ A)
    (hcount : ∀ N, N₀ ≤ N → ∀ (z : BitInput N) (g : UnionGuess (SUE l F e coef A L hL) z),
      UnionGuards (SUE l F e coef A L hL) z g →
        ∀ tr : List ℕ, (g.checkData tr).schedule.length ≤
          ((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e)).q N ^ unionCallDeg l)
    (habs : ∀ N, N₀ ≤ N → Kf * (3 + Kd) * (((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e)).q N + 1) ^
      (unionCallDeg l + (callDegMargin - 1)) ≤ ((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e)).q N ^ F.E.callDeg)
    (hsel : ∀ N, N₀ ≤ N → c1.budgetAt ((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e))
      (((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e)).q N) ≤
        ((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e)).callBudget
          (((gate0 l F).budget (kE l e) coef A (aE l e) (haE l e)).q N)) :
    WorkerAt3 (SUE l F e coef A L hL) P where
  t := NW P fr.tf
  s := _
  p := workerMachineW3 fr dc
  ht := two_le_NW P fr.tf
  result := lp P fr.tf (cellSlot P)
  fuel := workerFuelW3 fr dc
  onset := fr.onset
  callOk := fr.callOk
  run := worker_runW3 fr dc
  hok := fr.hok
  time := worker_timeW3 fr dc dc.hcost (unionCallDeg l) hA hcount habs hsel

/-- **Layer B at the gate: workers with the atom test from the stages.** -/
noncomputable def workers_of_stagesE3 (c1 : C1Impl) (dec : DecideF) (e : ℕ)
    (fronts : ∀ F : GateFree l, GateFreeOK l F → FrontsFWE3 e l F) (count : CallCountF l) :
    ∀ F : GateFree l, GateFreeOK l F → WorkersFE3 l e F := fun F hF =>
  ⟨(fronts F hF).1 + 2 * dec.1 + 8, by omega, fun coef hc P L hL =>
    let fd := (fronts F hF).2 coef hc _ P L hL
    let c1d := c1 fd.1
    let fk := fd.2 c1d
    let N₀ := Classical.choose (PlanW2.eventual_timeE l e F hF coef _ hc L hL c1d fk.1 dec.1 count)
    have hN₀ := Classical.choose_spec (PlanW2.eventual_timeE l e F hF coef _ hc L hL c1d fk.1 dec.1 count)
    workerOfE3 l e F coef _ P L hL c1d (fronts F hF).1 fk.1 N₀ dec.1 (fk.2 N₀) (dec.2 P) le_rfl
      (fun N hN => (hN₀ N hN).1) (fun N hN => (hN₀ N hN).2.1) (fun N hN => (hN₀ N hN).2.2)⟩

end LeafB

end NearCubicWires.WireExponent3_5.UnionMachine.PlanW3

end
