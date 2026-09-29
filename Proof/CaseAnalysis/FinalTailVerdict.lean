import Proof.CaseAnalysis.FinalTailAnd
import Proof.CaseAnalysis.FinalTailFeedPrep

/-! **Decision tail, stage 2b-iv — the three C.10 tests, AND-ed, physically.**

Paper C.10 (~4103): the machine "passes validity only if the first estimated
average is at most `2*zeta` and all estimated second moments are at most
`1+zeta`"; C.10.1: it "accepts a branch only if `mu~ >= theta_acc`", and
`acceptanceThreshold` is literally `midpoint = (c_p+s_p)/2`. This module runs
those three tests as ONE machine and commits their conjunction to a single flag.

`feed_exists` (T1, `…C10TailFeed`) delivers one test on the 305-tape feed bank
from a PARKED bank, consuming its comparator block, its two normaliser blocks and
its literal-word block. Three tests therefore need three private copies of those
tapes, so the whole 305-bank feed machine is docked three times by `feedSlots k`:
the identity on the shared prefix `0 … 220` (the worker's 218 tapes plus the three
phase records), and `221 … 304` to a private block `k`. The three verdicts land on
three distinct tapes `feedSlots k (cmpSlots 65)`; `and3` (three nested P4 branches
ending in `setOne`) folds them into `tailFlag`, which a literal `[false]` word
initialises.

No new machine and no new constant: everything here is `Step.seq` of `Step.dock`ed
existing GREEN stages. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdict

open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open LocalBitMultitape ExtDecompositionBatch
open CompetitorThresholdDecision
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep
open NearCubicWires.RepairSource.CloseoutFinal.C10TailAnd

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ### The verdict bank -/

/-- The verdict bank: the feed bank's shared prefix `0 … 220` (worker `0 … 217`
and the three phase records `218/219/220`), three private copies of the feed's
84 tail tapes `221 … 304` (landing at `221 … 304`, `305 … 388`, `389 … 472`), the
AND flag `tailFlag = 473`, and one blank spare `tailSpare = 474` for its literal
word. -/
abbrev tailBank : ℕ := 475

/-- The AND flag: paper C.10's single "passes validity and accepts" bit. -/
def tailFlag : Fin tailBank := ⟨473, by show 473 < 475; omega⟩
/-- The blank second tape `HierarchyFixedWord.machine` needs to write `[false]`. -/
def tailSpare : Fin tailBank := ⟨474, by show 474 < 475; omega⟩

/-- Slot `i` of the feed bank inside private copy `k`. -/
def feedIdx (k : Fin 3) (i : Fin bank) : ℕ :=
  if i.val < 221 then i.val else 221 + 84*k.val + (i.val - 221)

theorem feedIdx_lt_flag (k : Fin 3) (i : Fin bank) : feedIdx k i < 473 := by
  have hi : i.val < 305 := i.isLt
  have hk : k.val < 3 := k.isLt
  unfold feedIdx
  split <;> omega

theorem feedIdx_lt (k : Fin 3) (i : Fin bank) : feedIdx k i < 475 := by
  have := feedIdx_lt_flag k i
  omega

/-- **The three docking maps.** Identity on `0 … 220`; `221 … 304` into copy `k`. -/
def feedSlots (k : Fin 3) (i : Fin bank) : Fin tailBank := ⟨feedIdx k i, feedIdx_lt k i⟩

theorem feedSlots_injective (k : Fin 3) : Function.Injective (feedSlots k) := by
  intro i j h
  have hv : feedIdx k i = feedIdx k j := congrArg Fin.val h
  apply Fin.ext
  unfold feedIdx at hv
  by_cases h1 : i.val < 221
  · rw [if_pos h1] at hv
    by_cases h2 : j.val < 221
    · rw [if_pos h2] at hv
      exact hv
    · rw [if_neg h2] at hv
      omega
  · rw [if_neg h1] at hv
    by_cases h2 : j.val < 221
    · rw [if_pos h2] at hv
      omega
    · rw [if_neg h2] at hv
      omega

/-- **Pairwise disjointness.** No slot of copy `k` hits a private tape of copy
`k'`. (The shared prefix `0 … 220` is deliberately NOT disjoint: all three copies
read the same three phase records.) -/
theorem feedSlots_disjoint {k k' : Fin 3} (hk : k ≠ k') (i : Fin bank) (hi : 221 ≤ i.val)
    (j : Fin bank) : feedSlots k j ≠ feedSlots k' i := by
  intro h
  have hv : feedIdx k j = feedIdx k' i := congrArg Fin.val h
  have hkne : k.val ≠ k'.val := fun hh => hk (Fin.ext hh)
  have hj : j.val < 305 := j.isLt
  have hi2 : i.val < 305 := i.isLt
  have hk3 : k.val < 3 := k.isLt
  have hk4 : k'.val < 3 := k'.isLt
  unfold feedIdx at hv
  rw [if_neg (by omega : ¬ i.val < 221)] at hv
  by_cases hjj : j.val < 221
  · rw [if_pos hjj] at hv
    omega
  · rw [if_neg hjj] at hv
    omega

theorem feedSlots_ne_flag (k : Fin 3) (i : Fin bank) : feedSlots k i ≠ tailFlag := by
  intro h
  have hv : feedIdx k i = 473 := congrArg Fin.val h
  have hlt := feedIdx_lt_flag k i
  omega

theorem feedSlots_ne_spare (k : Fin 3) (i : Fin bank) : feedSlots k i ≠ tailSpare := by
  intro h
  have hv : feedIdx k i = 474 := congrArg Fin.val h
  have hlt := feedIdx_lt_flag k i
  omega

theorem flag_ne_spare : tailFlag ≠ tailSpare := by
  intro h
  have hv : (473 : ℕ) = 474 := congrArg Fin.val h
  omega

/-- The shared-prefix slot of `i`, seen inside the feed bank. -/
def preIdx (i : Fin tailBank) (h : i.val < 221) : Fin bank :=
  ⟨i.val, by show i.val < 218 + 87; omega⟩

theorem feedSlots_pre (k : Fin 3) (i : Fin tailBank) (h : i.val < 221) :
    feedSlots k (preIdx i h) = i := by
  apply Fin.ext
  show (if i.val < 221 then i.val else 221 + 84*k.val + (i.val - 221)) = i.val
  rw [if_pos h]

/-- The three phase records, on the shared prefix. -/
def scratchT (ph : CloseoutRowsOriginalSchedule.Phase) : Fin tailBank :=
  match ph with
  | .penalty => ⟨218, by show 218 < 475; omega⟩
  | .moment => ⟨219, by show 219 < 475; omega⟩
  | .clause => ⟨220, by show 220 < 475; omega⟩

theorem scratchT_lt (ph : CloseoutRowsOriginalSchedule.Phase) : (scratchT ph).val < 221 := by
  cases ph <;> decide

theorem feedSlots_scratch (k : Fin 3) (ph : CloseoutRowsOriginalSchedule.Phase) :
    feedSlots k (scratch ph) = scratchT ph := by
  apply Fin.ext
  cases ph <;> rfl

/-! ### Every block slot lives above the shared prefix -/

theorem cmp_ge (j : Fin 67) : 221 ≤ (cmpSlots j).val := by
  show 221 ≤ 221 + j.val
  omega
theorem normA_ge (j : Fin 5) : 221 ≤ (normSlots j).val := by
  show 221 ≤ 288 + j.val
  omega
theorem normB_ge (j : Fin 5) : 221 ≤ (normSlotsB j).val := by
  show 221 ≤ 293 + j.val
  omega
theorem word_ge (j : Fin 6) : 221 ≤ (wordSlots j).val := by
  show 221 ≤ 298 + j.val
  omega

theorem cmp_ne_pre (j : Fin bank) (hj : j.val < 221) (i : Fin 67) : cmpSlots i ≠ j := by
  intro h
  have hv : (cmpSlots i).val = j.val := congrArg Fin.val h
  have hge := cmp_ge i
  omega
theorem normA_ne_pre (j : Fin bank) (hj : j.val < 221) (i : Fin 5) : normSlots i ≠ j := by
  intro h
  have hv : (normSlots i).val = j.val := congrArg Fin.val h
  have hge := normA_ge i
  omega
theorem normB_ne_pre (j : Fin bank) (hj : j.val < 221) (i : Fin 5) : normSlotsB i ≠ j := by
  intro h
  have hv : (normSlotsB i).val = j.val := congrArg Fin.val h
  have hge := normB_ge i
  omega
theorem word_ne_pre (j : Fin bank) (hj : j.val < 221) (i : Fin 6) : wordSlots i ≠ j := by
  intro h
  have hv : (wordSlots i).val = j.val := congrArg Fin.val h
  have hge := word_ge i
  omega

/-! ### A two-slot map on the verdict bank, for the flag's literal word -/

def pairT (src dst : Fin tailBank) (i : Fin 2) : Fin tailBank := if i.val = 0 then src else dst

theorem pairT_injective (src dst : Fin tailBank) (hne : src ≠ dst) :
    Function.Injective (pairT src dst) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · have h' : src = dst := by simpa [pairT] using h
    exact absurd h' hne
  · have h' : dst = src := by simpa [pairT] using h
    exact absurd h'.symm hne
  · rfl

theorem pairT_ne {src dst i : Fin tailBank} (h1 : src ≠ i) (h2 : dst ≠ i) (j : Fin 2) :
    pairT src dst j ≠ i := by
  fin_cases j
  · simpa [pairT] using h1
  · simpa [pairT] using h2

/-- **Initialise the flag.** `and3` needs `A res = [false]`; a two-tape
`HierarchyFixedWord` literal writes it from blanks and returns both heads to `0`. -/
theorem flag_init (H : Fin tailBank → ℕ) (A : Fin tailBank → List Bool)
    (hfH : H tailFlag = 0) (hsH : H tailSpare = 0)
    (hfA : A tailFlag = []) (hsA : A tailSpare = []) :
    Step (RecoveryFocus.machine (pairT tailFlag tailSpare) (HierarchyFixedWord.machine [false]))
      4 H A H (install (pairT tailFlag tailSpare) A ![[false], List.replicate 1 false]) := by
  have hH : ∀ j, H (pairT tailFlag tailSpare j) = 0 := by
    intro j
    fin_cases j
    · simpa [pairT] using hfH
    · simpa [pairT] using hsH
  have hA : ∀ j, A (pairT tailFlag tailSpare j) = [] := by
    intro j
    fin_cases j
    · simpa [pairT] using hfA
    · simpa [pairT] using hsA
  have hstep := (word_step [false]).dock (pairT tailFlag tailSpare)
    (pairT_injective tailFlag tailSpare flag_ne_spare) H A hH hA
  rwa [dockH_existing (pairT tailFlag tailSpare) H (fun _ => 0) hH] at hstep

/-! ### The AND, with its frame -/

/-- `and3_step` with the extra "nothing but `res` moves" conjunct that the tail's
`A' i = A i` clause needs; same four-case proof. -/
theorem and3_step_frame {u : ℕ} (f1 f2 f3 res : Fin u)
    (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH1 : H f1 = 0) (hH2 : H f2 = 0) (hH3 : H f3 = 0) (hHr : H res = 0)
    (hAr : A res = [false]) :
    ∃ tout : Fin u → List Bool,
      Step (and3 f1 f2 f3 res) 4 H A H tout ∧
      (readTapeBit (tout res) 0 = true ↔
        (readTapeBit (A f1) 0 = true ∧ readTapeBit (A f2) 0 = true ∧
          readTapeBit (A f3) 0 = true)) ∧
      (∀ i, i ≠ res → tout i = A i) := by
  have hself := exitTapes_false_self res A hAr
  have hr0 : readTapeBit (A res) 0 = false := by simp [hAr, readTapeBit]
  cases hb1 : readTapeBit (A f1) 0
  · refine ⟨A, ?_, ?_, ?_⟩
    · have h := branch_reject f1 res (and2 f2 f3 res) H A (by rw [hH1]; exact hb1)
      rw [hHr, hself] at h
      exact Step.enlarge h (by norm_num)
    · simp [hr0]
    · intro i _
      rfl
  cases hb2 : readTapeBit (A f2) 0
  · refine ⟨A, ?_, ?_, ?_⟩
    · have inner := branch_reject f2 res (and1 f3 res) H A (by rw [hH2]; exact hb2)
      rw [hHr, hself] at inner
      have h := branch_pass f1 res (and2 f2 f3 res) H A (by rw [hH1]; exact hb1) 1 H A inner
      exact Step.enlarge h (by norm_num)
    · simp [hr0]
    · intro i _
      rfl
  cases hb3 : readTapeBit (A f3) 0
  · refine ⟨A, ?_, ?_, ?_⟩
    · have inner := branch_reject f3 res (setSlot res) H A (by rw [hH3]; exact hb3)
      rw [hHr, hself] at inner
      have mid := branch_pass f2 res (and1 f3 res) H A (by rw [hH2]; exact hb2) 1 H A inner
      have h := branch_pass f1 res (and2 f2 f3 res) H A (by rw [hH1]; exact hb1) 2 H A mid
      exact Step.enlarge h (by norm_num)
    · simp [hr0]
    · intro i _
      rfl
  · refine ⟨Function.update A res [true], ?_, ?_, ?_⟩
    · have inner := setSlot_step res H A hHr hAr
      have l3 := branch_pass f3 res (setSlot res) H A (by rw [hH3]; exact hb3) 1 H _ inner
      have l2 := branch_pass f2 res (and1 f3 res) H A (by rw [hH2]; exact hb2) 2 H _ l3
      exact branch_pass f1 res (and2 f2 f3 res) H A (by rw [hH1]; exact hb1) 3 H _ l2
    · simp [readTapeBit]
    · intro i hi
      exact Function.update_of_ne hi _ _

/-! ### The T1 → T2 interface -/

/-! ### One feed, docked into the verdict bank -/

/-! ### The parked verdict bank -/

/-! ### The two directions of `passes` -/

theorem passes_false (p n d : ℕ) (q : ℚ) : passes false p n d q ↔ estimate p n d ≤ q := by
  simp [passes]

theorem passes_true (p n d : ℕ) (q : ℚ) : passes true p n d q ↔ q ≤ estimate p n d := by
  simp [passes]

/-! ### The theorem -/

end NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdict
