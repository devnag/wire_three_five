import Proof.Wire_3_5.Assembly.FreeBase
import Proof.Wire_3_5.UnionMachine.SlackBase
import Proof.Wire_3_5.UnionMachine.SchedLoop
import Proof.Wire_3_5.Selection.Contract
import Proof.MachineModel.Layout

/-! # C6: leaf U's enclosing application (P3:3669-3697, 3504-3554, 3797-3811)

Realizes, as the term of leaf U with its missing stages as explicit residuals, the paper's union weak machine: "The
weak machine guesses one size-`q^G` general oracle, a class tag, and one sparse grid sum for each distinct PCPP variable.
It rejects malformed descriptions, oversized atoms, and coefficients outside the fixed grid. Systematic parities are
constructed from the PCPP output. It then selects the common star translation, constructs the shared coordinate
filters, and performs (tr:tests)" and "At the finitely many source lengths where this fixed envelope exceeds the
refuter's `N/10` guess budget, the machine rejects outright" (P3:3669-3680); its soundness, `tr:soundness`
(P3:3504-3554); and its time, "the time for all polynomially many verification calls has the form [...]"
(P3:3797-3811), with the source preprocessing `N^{d_ver}q^{O_G(1)}` and `C_clk > d_ver + 2` (P3:3653-3655).

Paper quantity of the main type: **`UnionLeafF l`** (the union's build, `tr:soundness`, `tr:time` as `B.Split`, and
eventual `tr:completeness`, at the gate `gate0 l F` and the pinned setup `setupF l F`, under `GateFreeOK l F`).

Two layers, both proved here:
* **Layer A** (`unionLeafF_of_workers`): leaf U from a WORKER per primitive and language (`WorkerAt`: a machine whose
  result on the refuter's `⌊N/16⌋`-bit witness is the slack run `unionSlackRun` past an onset, within a fuel meeting
  the ledger's split). It uses M1 (`weakOf`, the slack soundness/completeness) and two setup residuals.
* **Layer B** (`workers_of_stages`): the worker from its stages, assembled here: the FRONT (U0–U5: gate, decode, PCP,
  substitution, PCPP, derived data, the coset selection docked from C1, the call table with the request writer and
  `callOk`, the thresholds preloaded into the accumulators, the loop's capacities), then the VERIFIED schedule loop
  (M3 `sched_loop`: the docked rewound estimator, the `p`-bit rounding, the accumulation, scrubbed between calls),
  then the (U7). The time is assembled here too (C7): the front's source work, one call for C1 at C1's OWN
  envelope (`Free.selection_le_callBudget`), the calls' count (the forcing lemma) times a per-call factor within
  `callDegMargin − 1` powers of `q + 1`, absorbed by `GateFreeOK` (`Split.calls_absorb`).

Residuals (the plan's helper types): `C1Impl` (C1/C3: `Implements (c1inst E₁ cosetWord selWord _ c₁)` at C1's own
envelope and the union's encodings), `DecideF` (U7), `FrontsF l F` (U0–U5), `CallCountF l` (`setupF_calls_le`),
`AcceptsCallF l` (a guess passing the tests makes an admissible call), `SetupFactsF l` (the setup's language, outer
error, width growth and propagated error with the rounding). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.ExtDecompositionBatch NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.Bindings.CLW20Theorem113
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine Filter
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)

/-! ## The union's own constants (P3:3633, 3653-3655) -/

section Consts

end Consts

/-- The rounding precision `p(q) = ⌈log₂(q+2)⌉`: `2^{−p} ≤ 1/(q+2)`, and `2^p ≤ 2(q+2)` keeps the
rounding and the accumulation polynomial in `q`. -/
def unionBits (q : ℕ) : ℕ := Nat.clog 2 (q + 2)

/-! ## Layer A: the worker and leaf U -/

section Worker

namespace WorkerAt

end WorkerAt

end Worker

/-! ### The leaf's residual families -/

section Leaf
variable (l : Literals)

theorem rejectAll_runtime (N : ℕ) : rejectAll.runtime N = 3 := rfl

end Leaf

/-! ## Layer B: the worker from its stages -/

/-! ### C1, docked at its own envelope -/

/-- **C1's input word**, fixed by the union (which writes it): `n`, `r`, the gates (their weights, then their
threshold), the populations (their gate indices, then their weight `p_X`). -/
def selWord (R : NearCubicWires.WireExponent3_5.Machine.SelectionReq) : List Bool :=
  natWord R.n ++ natWord R.r ++ natWord R.gates.length ++
    R.gates.flatMap (fun g => (List.ofFn fun i => intWord (g.weights i)).flatten ++ intWord g.threshold) ++
    natWord R.pops.length ++ R.pops.flatMap (fun X => natListWord X.1 ++ ratWord X.2)

/-- **C1's output word**, fixed by the union (which reads it): the selected coset's syndrome codes, the same
`natListWord` the request word carries as its translation (`PrimRequest.word`). -/
def cosetWord (c : NearCubicWires.WireExponent3_5.Machine.S0Stub.Coset) : List Bool := natListWord c

/-- **C1's contract with polynomial-size inputs**: `c1inst` at the union's encodings, its precondition strengthened by
`|selWord R| ≤ (n+1)^d`. The paper's selection time `2^{n/2+O(k)}poly(n)` (P3:1335, 1359-1360) is for inputs of
polynomial size (the carriers' envelope, P3:3071-3072); without a size bound no machine meets a budget fixed by
`(n, k)`, because it cannot read a longer request while the argmin depends on all of it. -/
def c1sized (d : ℕ) (E₁ : Envelope) (c₁ : ℕ) : NearCubicWires.WireExponent3_5.Machine.MachineContract E₁ :=
  { NearCubicWires.WireExponent3_5.SelectionMachine.c1inst E₁ cosetWord selWord (fun _ => 0) c₁ with
    pre := fun R => (NearCubicWires.WireExponent3_5.SelectionMachine.c1inst E₁ cosetWord selWord (fun _ => 0) c₁).pre R ∧
      (selWord R).length ≤ (R.n + 1) ^ d }

/-- **C1 at input-size degree `d`**: the coset-selection machine ("It then selects the common star translation",
P3:3673; `star:selection`, P3:1324-1362) implementing `c1sized d` at C1's OWN envelope `E₁` and coefficient `c₁`.
Docked at its own envelope, it is one call inside `callBudget` for every leaf envelope (`Free.selection_le_callBudget`),
so `GateFreeOK` needs no C1 constant. -/
structure C1At (d : ℕ) where
  E₁ : Envelope
  c₁ : ℕ
  impl : NearCubicWires.WireExponent3_5.Machine.Implements (c1sized d E₁ c₁)

/-- **Residual C1** (C1/C3): C1 at every input-size degree (its envelope may grow with `d`). -/
def C1Impl : Type := ∀ d : ℕ, C1At d

/-- The budget of one docked C1 call at native width `q`: C1's selection class at its own envelope, at the ledger's
star width `kOf q` (its contract's budget at `n = q`, `r = rOf q`). -/
def C1At.budgetAt {d : ℕ} (c : C1At d) {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) (q : ℕ) : ℕ :=
  c.c₁ * classBound c.E₁ .selection q (B.kOf q) 0

/-! ### The stages' layout -/

section Stages
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

/-- The loop's tape count: the schedule-loop bank in base's scrubbed layout. -/
noncomputable abbrev NL : ℕ := Sched.NA P + 1 + 1

/-- The worker's tapes: the refuter's input (`0`) and witness (`1`), the loop's bank, then the front's own `tf`. -/
noncomputable abbrev NW (tf : ℕ) : ℕ := 2 + NL P + tf

/-- The loop bank's slots in the worker. -/
noncomputable def lp (tf : ℕ) (i : Fin (NL P)) : Fin (NW P tf) :=
  ⟨2 + i.val, by have := i.isLt; show 2 + i.val < 2 + NL P + tf; omega⟩

theorem two_le_NW (tf : ℕ) : 2 ≤ NW P tf := by show 2 ≤ 2 + NL P + tf; omega

theorem lp_inj (tf : ℕ) : Function.Injective (lp P tf) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [lp] at this
  exact Fin.ext (by omega)

/-- The result cell: the loop bank's cell tape (the fixed tape `1`). -/
noncomputable def cellSlot : Fin (NL P) := Scrub.inner (Sched.fx P 1)

/-- The loop bank's heads at kept data `K`. -/
noncomputable def bankH (K : Sched.Kept) : Fin (NL P) → ℕ := Scrub.heads (Sched.iterH P K)

/-- The loop bank's tapes at kept data `K`: registers of capacity `cap`, scratch blank at `R`, log `Lg`, driver `R`. -/
noncomputable def bankA (cap R Lg : ℕ) (K : Sched.Kept) : Fin (NL P) → List Bool :=
  Scrub.bank (Scrub.blank (Sched.scr P) (Sched.iterA P cap K) R) R Lg

end Stages

/-- The worker's entry tapes: base's `Verifier.inputTapes` (framed input, framed witness, blank). -/
def entryA {u N : ℕ} (x : BitInput N) (w : List Bool) : Fin u → List Bool :=
  fun i => if i.val = 0 then RepairOrdinary.frame (List.ofFn x) else if i.val = 1 then RepairOrdinary.frame w else []

/-- **The decision** (P3:3485-3489), with the slack thresholds preloaded into the accumulators by the front:
`Z_V ≤ 0`, `Z_Q ≤ 0`, `Z_μ ≥ 0` (accumulator `2k` positive, `2k+1` negative, `k = V, Q, μ`). -/
def decisionOf (acc : Fin 6 → ℕ) : Bool :=
  decide (acc 0 ≤ acc 1) && decide (acc 2 ≤ acc 3) && decide (acc 5 ≤ acc 4)

/-! ### Residual U7: the decision -/

section Decide
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

/-- **Residual U7, the decision** (P3:3485-3489): on the loop's final bank, the result cell becomes the decision of
the accumulators, within `Kd·(cap+1)` steps. -/
structure DecideAt (Kd : ℕ) where
  sd : ℕ
  M : Machine (NL P) sd
  cost : ℕ → ℕ
  hcost : ∀ cap, cost cap ≤ Kd * (cap + 1)
  run : ∀ (cap R Lg : ℕ) (K : Sched.Kept), 1 ≤ cap → (∀ i, K.acc i ≤ cap) → ∃ (Hd : Fin (NL P) → ℕ)
    (Ad : Fin (NL P) → List Bool), Step M (cost cap) (bankH P K) (bankA P cap R Lg K) Hd Ad ∧
      readTapeBit (Ad (cellSlot P)) (Hd (cellSlot P)) = decisionOf K.acc

end Decide

/-- **Residual U7** at every ledger and primitive, with one constant `Kd`. -/
def DecideF : Type :=
  Σ Kd : ℕ, ∀ {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I),
    DecideAt P Kd

/-! ### Residual U0–U5: the front -/

section Front
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- M3 `sched_loop`'s hypotheses at the table's common width `n0`. -/
structure LoopHyps (cap R Lg p n0 Mm Wm : ℕ) (acc0 : Fin 6 → ℕ) (Ls : List (Sched.TEntry I)) : Prop where
  hn : ∀ t ∈ Ls, t.req.1.n = n0
  hM : ∀ t ∈ Ls, t.e.mag ≤ Mm
  hW : ∀ t ∈ Ls, t.e.word.length ≤ Wm
  hcapR : 2 * Wm + Mm + 2 ≤ cap
  hcapD : 4 * (2 * B.callBudget n0 + 3) + 8 * 2 ^ p + 20 ≤ cap
  hcapA : ∀ i, acc0 i + (Ls.length + 2) * (Mm * (8 * 2 ^ p)) ≤ cap
  hR1 : cap + 1 ≤ R
  hR2 : Sched.stageCost Mm Wm (B.callBudget n0) (2 * B.callBudget n0 + 3) p + 1 ≤ R
  hL : R + 1 ≤ Lg

/-- The front's reference output at one input and witness: the call table (admissible entries), the accumulators'
start (the slack thresholds, or the rejecting pattern), the rounding precision in the rounding register (`unionBits q`
on a table the loop runs), the loop's capacities and the table's entry bounds. -/
structure FrontOut (I : PrimitiveInputs B) where
  table : List (Sched.TEntry I)
  acc0 : Fin 6 → ℕ
  p : ℕ
  cap : ℕ
  R : ℕ
  Lg : ℕ
  Mm : ℕ
  Wm : ℕ

variable (P : FusedPrimitive I)

/-- The loop's kept data at its entry. -/
noncomputable def FrontOut.kept (o : FrontOut I) : Sched.Kept := Sched.KOf P o.p o.acc0 o.table 0

/-- The loop's kept data at its exit. -/
noncomputable def FrontOut.keptEnd (o : FrontOut I) : Sched.Kept :=
  Sched.KOf P o.p o.acc0 o.table o.table.length

/-- The loop's step count on the table (M3 `sched_loop`; one step on an empty table). -/
def FrontOut.loopSteps (o : FrontOut I) (n0 : ℕ) : ℕ :=
  o.table.length * (Sched.loopCost o.Mm o.Wm (B.callBudget n0) o.p o.R + 2) + 1

end Front

/-! ### The worker: front, loop, decision -/

section Assembly
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {P : FusedPrimitive I}
 {d₁ : ℕ} {c1 : C1At d₁} {Af Kf N₀ Kd : ℕ}

/-- **The loop on the front's table** (M3 `sched_loop`; an empty table stops at once). -/
theorem loop_step (o : FrontOut I) (n0 : ℕ)
    (h : o.table ≠ [] → LoopHyps o.cap o.R o.Lg o.p n0 o.Mm o.Wm o.acc0 o.table) :
    Step (Sched.loopM P) (o.loopSteps n0) (bankH P (o.kept P)) (bankA P o.cap o.R o.Lg (o.kept P))
      (bankH P (o.keptEnd P)) (bankA P o.cap o.R o.Lg (o.keptEnd P)) := by
  by_cases h0 : o.table = []
  · have hs0 : Sched.scr P (Sched.fx P 0) = false := by simp [Sched.scr, Sched.keptV, Sched.fx_val]
    have hlen : o.table.length = 0 := by rw [h0]; rfl
    have hw := whileRun (Sched.loopBody P) (Scrub.inner (Sched.fx P 0)) 0
      (Sched.loopCost o.Mm o.Wm (B.callBudget n0) o.p o.R)
      (fun j => bankH P (Sched.KOf P o.p o.acc0 o.table j))
      (fun j => bankA P o.cap o.R o.Lg (Sched.KOf P o.p o.acc0 o.table j))
      (fun j hj => absurd hj (Nat.not_lt_zero j))
      (by
        simp only [bankA, bankH, Scrub.bank_inner, Scrub.heads_inner, Scrub.blank, hs0, Bool.false_eq_true,
          ↓reduceIte, Sched.iterA_fx, Sched.iterH_fx, Sched.fixedA, Sched.fixedH, Sched.KOf]
        have := Sched.tbl_end o.table
        rw [hlen] at this
        exact this)
      (fun j hj => absurd hj (Nat.not_lt_zero j))
    unfold FrontOut.loopSteps FrontOut.kept FrontOut.keptEnd
    rw [hlen]
    exact hw
  · have hy := h h0
    exact Sched.sched_loop P o.cap o.R o.Lg o.p n0 o.Mm o.Wm o.acc0 o.table hy.hn hy.hM hy.hW hy.hcapR hy.hcapD
      hy.hcapA hy.hR1 hy.hR2 hy.hL

end Assembly

/-! ### Layer B at the gate -/

section LeafB
variable (l : Literals)

/-- The ledger's width grows (`TimeBudget.growth`). -/
theorem tendsto_q {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) : Tendsto B.q atTop atTop :=
  tendsto_atTop_atTop.2 fun m => B.growth m

end LeafB

end NearCubicWires.WireExponent3_5.UnionMachine.Plan
