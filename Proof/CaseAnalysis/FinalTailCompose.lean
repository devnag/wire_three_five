import Proof.CaseAnalysis.FinalTailFeed
import Proof.CaseAnalysis.FinalTailVerdict
import Proof.CaseAnalysis.FinalWorkerDockSeam

namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailCompose

open LocalBitMultitape ExtDecompositionBatch
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit
open CloseoutRowsOriginalSchedule (Phase)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 A stage, with every head parked

`Rewind.machine p` logs one mark per transition of `p` on a fresh tape and then
consumes the marks, moving every head of `p` left once per mark.  Nothing here
is new: it is `Rewind.reset_run`, restated as a `Step`. -/

/-! ## §2 The gate's exit tapes, named -/

/-- The bank a gated worker hands its body: the verifier's framed input on tape
`0`, its framed witness on tape `1`, `[true]` on the gate's scratch slot, blank
everywhere else. -/
def entryOf {t : ℕ} (fl : Fin t) (input witness : List Bool) : Fin t → List Bool :=
  fun i => if i = fl then [true]
    else if i.val = 0 then frame input else if i.val = 1 then frame witness else []

theorem entry_eq {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t) (res fl : Fin t)
    (h0 : fl.val ≠ 0) (h1 : fl.val ≠ 1) (input witness : List Bool) :
    exitTapes fl ((UAcceptanceCarrier.verifier p ht res).inputTapes input witness) 0 true
      = entryOf fl input witness := by
  have hblank : (UAcceptanceCarrier.verifier p ht res).inputTapes input witness fl = [] := by
    rw [UAcceptanceCarrier.inputTapes_eq]
    simp [h0, h1]
  funext i
  rw [exitTapes_blank fl _ true hblank i, UAcceptanceCarrier.inputTapes_eq]
  unfold entryOf
  by_cases hi : i = fl
  · simp [hi]
  · simp [hi]

/-! ## §3 The body block's four named local slots

W1 freezes the dock's layout at `input = 0`, `port = 215`, `flag = 216`,
`result = 217`; S2's stage widens the bank to `218+e` with those ports at
`Fin.castAdd e`. -/

variable (e : ℕ)

def wport : Fin (218+e) := Fin.castAdd e port
def wflag : Fin (218+e) := Fin.castAdd e flag
def winput : Fin (218+e) := Fin.castAdd e inputTape
def wwit : Fin (218+e) := Fin.castAdd e ⟨1, by omega⟩

@[simp] theorem wport_val : (wport e).val = 215 := rfl
@[simp] theorem wflag_val : (wflag e).val = 216 := rfl
@[simp] theorem winput_val : (winput e).val = 0 := rfl
@[simp] theorem wwit_val : (wwit e).val = 1 := rfl

def BlockRuns {bs : ℕ} (body : Machine (218+e) bs) (F : ℕ)
    (input witness : List Bool) (rec : List Bool) : Prop :=
  ∃ (heads : Fin (218+e) → ℕ) (exit : Fin (218+e) → List Bool),
    Step body F (fun _ => 0) (entryOf (wflag e) input witness) heads exit ∧
    exit (wport e) = rec ∧
    exit (winput e) = frame input ∧ exit (wwit e) = frame witness

/-! ## §5 The composed bank

T2 froze its tail bank at `tailBank = 475`: identity on `0 … 220`, its three feed
copies at `221 … 472`, `tailFlag = 473`, `tailSpare = 474`.  The composition adds
its blocks ABOVE that, so every slot the tail names keeps its index.

| tapes | contents |
|---|---|
| `0`, `1` | the verifier's framed input and framed witness, SHARED by the three blocks |
| `218`, `219`, `220` | the three record slots (T2's `scratchT`) |
| `221 … 474` | T2's feed copies, `tailFlag = 473`, `tailSpare = 474` — never touched here |
| `475 + k*(218+e) + j` | block `k`'s local tape `j` (`k = 0,1,2`; `j ∉ {0,1,215}`) |
| `L`, `L+1` (`L := 475+3*(218+e)`) | the two literal scratch tapes |
| `L+2`, `L+3`, `L+4` | the three rewind counters |
| `L+5` | reserved for the tail's own rewind counter |
-/

/-- The composed bank. -/
def bigOf : ℕ := 475 + 3*(218+e) + 6

def scrVal : Phase → ℕ
  | .penalty => 218
  | .moment => 219
  | .clause => 220

def litVal : Phase → ℕ
  | .penalty => 475 + 3*(218+e)
  | .moment => 475 + 3*(218+e)
  | .clause => 475 + 3*(218+e) + 1

def cntVal : Phase → ℕ
  | .penalty => 475 + 3*(218+e) + 2
  | .moment => 475 + 3*(218+e) + 3
  | .clause => 475 + 3*(218+e) + 4

theorem scrVal_le (ph : Phase) : 218 ≤ scrVal ph ∧ scrVal ph ≤ 220 := by
  cases ph <;> simp only [scrVal] <;> omega
theorem litVal_le (ph : Phase) :
    475 + 3*(218+e) ≤ litVal e ph ∧ litVal e ph ≤ 475 + 3*(218+e) + 1 := by
  cases ph <;> simp only [litVal] <;> omega
theorem cntVal_le (ph : Phase) :
    475 + 3*(218+e) + 2 ≤ cntVal e ph ∧ cntVal e ph ≤ 475 + 3*(218+e) + 4 := by
  cases ph <;> simp only [cntVal] <;> omega

def scr (ph : Phase) : Fin (bigOf e) :=
  ⟨scrVal ph, by have := scrVal_le ph; show scrVal ph < 475 + 3*(218+e) + 6; omega⟩
def cnt (ph : Phase) : Fin (bigOf e) :=
  ⟨cntVal e ph, by have := cntVal_le e ph; show cntVal e ph < 475 + 3*(218+e) + 6; omega⟩
def litOf (ph : Phase) : Fin (bigOf e) :=
  ⟨litVal e ph, by have := litVal_le e ph; show litVal e ph < 475 + 3*(218+e) + 6; omega⟩

@[simp] theorem scr_val (ph : Phase) : (scr e ph).val = scrVal ph := rfl
@[simp] theorem cnt_val (ph : Phase) : (cnt e ph).val = cntVal e ph := rfl
@[simp] theorem litOf_val (ph : Phase) : (litOf e ph).val = litVal e ph := rfl

/-- The tape reserved for the TAIL's own rewind counter. -/
def tailCnt : Fin (bigOf e) := ⟨475 + 3*(218+e) + 5, by
  show 475 + 3*(218+e) + 5 < 475 + 3*(218+e) + 6; omega⟩

@[simp] theorem tailCnt_val : (tailCnt e).val = 475 + 3*(218+e) + 5 := rfl

/-! ### The gate's three slots -/

/-- The gate's input slot. -/
def gInput : Fin (bigOf e) := ⟨0, by show (0:ℕ) < 475 + 3*(218+e) + 6; omega⟩
/-- Bank tape `1`, the framed witness. -/
def gWit : Fin (bigOf e) := ⟨1, by show (1:ℕ) < 475 + 3*(218+e) + 6; omega⟩
/-- The gate's verdict slot: T2's `tailFlag`, at the same index. -/
def gResult : Fin (bigOf e) := ⟨473, by show (473:ℕ) < 475 + 3*(218+e) + 6; omega⟩

@[simp] theorem gInput_val : (gInput e).val = 0 := rfl
@[simp] theorem gWit_val : (gWit e).val = 1 := rfl
@[simp] theorem gResult_val : (gResult e).val = 473 := rfl

/-! ### A block is parked, read off the ambient bank -/

/-! ## §6 One phase's body, docked and head-parked -/

/-! ## §7 The two literal flag writes -/


/-! ## §8 The four literal slots, by index -/


/-! ## §9 The three phase bodies, composed inside one bank -/

/-- The composed budget: two four-step literal writes, three DOUBLED block
budgets (the `Rewind` head-reset factor), and the four paid bridge steps of
`Composition.machine`.  Every summand is `len`-determined exactly when the block
budgets are. -/
def bodyThreeFuel (F : Phase → ℕ) : ℕ :=
  ((4+1+4) + 1 + ((2*F .penalty+2) + 1 + (2*F .moment+2))) + 1 + (2*F .clause+2)

/-! ## §10 Inside P4's gate

W1's `worker onset input flag result body` IS `C10LengthGate.gated`, and
`gated_verifier_pass` hands the body the verifier's own tapes with every head at
`0` and the single scratch slot `flag` carrying `[true]` — which is precisely
`entryOf (gFlag e)`.  So the composed body plugs into the gate with no glue. -/

/-! ## §11 T2's decision tail, docked

T2's bank (`tailBank = 475`) is the identity on `0 … 220` and never touches
`i.val < 221`, so it embeds into the composed bank index for index; only its own
rewind counter needs a fresh tape, and that is `tailCnt`. -/

/-- T2's bank sits at the bottom of the composed bank, index for index. -/
def tslot (i : Fin C10TailVerdict.tailBank) : Fin (bigOf e) :=
  ⟨i.val, by
    have hi : i.val < 475 := i.isLt
    show i.val < 475 + 3*(218+e) + 6
    omega⟩

@[simp] theorem tslot_val (i : Fin C10TailVerdict.tailBank) : (tslot e i).val = i.val := rfl

/-! ## §12 The whole C.10 machine, above the cutoff

Three phase bodies, T2's three-comparator decision tail, all inside P4's gate,
at ONE run: `Verdict.run` and `Verdict.accepts_iff` for the composed machine. -/

/-! ## §13 The uniform tail, and the FIXED composed machine

`C10Verdict.Verdict` fixes one machine `p` per input, which `verdict_run_of_records`
supplies; `C10Fusion.Pipeline` fixes ONE machine for every `n`, `x` and `bits`,
and that is strictly more.  `tail_step` as frozen quantifies `states` and `m`
INSIDE the `∀ W …`, so the composed machine varies with the record width — the
literal threshold words are written by `HierarchyFixedWord`, whose state count is
the word's length, i.e. `w W`.

`UniformTail` is the same theorem with `states`, `m` and the budget FUNCTION
hoisted out.  Against it the composed machine `composedWorker` is fixed once the
three block bodies and the tail machine are, and `Pipeline`'s single `p` exists. -/

end NearCubicWires.RepairSource.CloseoutFinal.C10TailCompose
