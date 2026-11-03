import Proof.Wire_3_5.Filters.GF2Primitive
import Proof.Wire_3_5.MachineModel.BlockBranch
import Proof.Wire_3_5.MachineModel.BlockCopy

/-! # Block v3 (S5): the join count of two sorted streams

Paper: P3:1339-1356 and 1734-1738. The selection joins count the pairs `(z_L, z_R)` with `a(z_L) + b(z_R) = 0`
by sorting and merging. The kernel reference is `JoinElimination.joinByCounts`, i.e. `Σ_v #left(v) · #right(v)`.
The machine takes the sorter's output format: `sortBlock_out` gives `stream sorted`, which is
`(sorted.map word).flatMap frame ++ [false]` because `recordBits r = frame (word r)`. That is two streams of
framed words of one width, sorted by `RadixSemantics.value`.

The paper quantity of the main theorem is `joinCount A B = Σ_{b ∈ B} #A(b)`. The machine runs two merge passes,
each with a cursor over each stream and one register per cursor:
* pass `≤` accumulates `Σ_b #{a ≤ b}`;
* pass `<` accumulates `Σ_b #{a < b}`;
* their difference is `Σ_b #{a = b}`.
Each merge step compares the two registers (a fold into a cell), then either counts the `a` and loads the next
`a`, or adds the count to the accumulator and loads the next `b`. Its cost is linear in the streams.

Part 1 holds the small machines and the branch lemmas. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## Step-level branches over `branchM` -/

theorem branch_true {t s₁ s₂ n : ℕ} (i : Fin t) {p : Machine t s₁} (q : Machine t s₂) {H H' : Fin t → ℕ}
    {A A' : Fin t → List Bool} (h : Step p n H A H' A') (hb : readTapeBit (A i) (H i) = true) :
    Step (branchM i p q) (n + 2) H A H' A' := by
  obtain ⟨r, hr, hh, ht, _⟩ := h
  obtain ⟨m, hm, htimed⟩ := branchM_timed i p q 1 (Or.inl rfl) H A (by simp [entryBit, hb]) n r hr
  obtain ⟨actual, ha, haf, _⟩ := htimed.run (by simp [branchM, RecoveryCalls.machine, RecoveryCalls.stopped])
  have more := runFrom_moreFuel (branchM i p q) m (n + 2 - m) _ actual ha
  rw [Nat.add_sub_of_le (by omega)] at more
  refine ⟨actual, more, ?_, ?_, by omega⟩
  · rw [haf, ← hh]; rfl
  · rw [haf, ← ht]; rfl

theorem branch_false {t s₁ s₂ n : ℕ} (i : Fin t) (p : Machine t s₁) {q : Machine t s₂} {H H' : Fin t → ℕ}
    {A A' : Fin t → List Bool} (h : Step q n H A H' A') (hb : readTapeBit (A i) (H i) = false) :
    Step (branchM i p q) (n + 2) H A H' A' := by
  obtain ⟨r, hr, hh, ht, _⟩ := h
  obtain ⟨m, hm, htimed⟩ := branchM_timed i p q 2 (Or.inr rfl) H A (by simp [entryBit, hb]) n r hr
  obtain ⟨actual, ha, haf, _⟩ := htimed.run (by simp [branchM, RecoveryCalls.machine, RecoveryCalls.stopped])
  have more := runFrom_moreFuel (branchM i p q) m (n + 2 - m) _ actual ha
  rw [Nat.add_sub_of_le (by omega)] at more
  refine ⟨actual, more, ?_, ?_, by omega⟩
  · rw [haf, ← hh]; rfl
  · rw [haf, ← ht]; rfl

/-! ## A docked stage that keeps the other heads where they are -/

theorem dockKeep {k s n u : ℕ} {M : Machine k s} {tin tout : Fin k → List Bool}
    (h : Step M n (fun _ => 0) tin (fun _ => 0) tout) (slots : Fin k → Fin u) (hi : Function.Injective slots)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (slots j) = 0) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots M) n H A H (RecoveryRootRound.install slots A tout) := by
  have hd := dockRun h slots hi H A hH hA
  have e : dockH slots H (fun _ => 0) = H := by
    funext i
    cases hp : RecoveryFocus.pick slots i with
    | none => simp [dockH, hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots hp
      simp only [dockH, hp]
      rw [← he, hH j]
  rwa [e] at hd

/-! ## The comparison fold into a cell -/

/-- One bit of the comparison, low bit first: a differing bit decides (the later bit is more significant). -/
def cmpStep (a b s : Bool) : Bool := if a == b then s else b

def foldBits (f : Bool → Bool → Bool → Bool) : Bool → List Bool → List Bool → Bool
  | s, a :: u, b :: v => foldBits f (f a b s) u v
  | s, _, _ => s

theorem foldCmp_value (u v : List Bool) (h : u.length = v.length) (s : Bool) :
    foldBits cmpStep s u v = if value u = value v then s else decide (value u < value v) := by
  induction u generalizing v s with
  | nil =>
    cases v with
    | nil => simp [foldBits, value]
    | cons b v => simp at h
  | cons a u ih =>
    cases v with
    | nil => simp at h
    | cons b v =>
      rw [foldBits, ih v (by simpa using h)]
      have hvu : value (a :: u) = a.toNat + 2 * value u := rfl
      have hvv : value (b :: v) = b.toNat + 2 * value v := rfl
      by_cases huv : value u = value v
      · rw [if_pos huv]
        by_cases hab : a = b
        · subst hab
          have he : value (a :: u) = value (a :: v) := by rw [hvu, hvv, huv]
          rw [if_pos he]
          simp [cmpStep]
        · have hne : value (a :: u) ≠ value (b :: v) := by
            rw [hvu, hvv, huv]; cases a <;> cases b <;> simp_all [Bool.toNat]
          rw [if_neg hne]
          have hlt : (value (a :: u) < value (b :: v)) ↔ b = true := by
            rw [hvu, hvv, huv]; cases a <;> cases b <;> simp_all [Bool.toNat]
          have hc : cmpStep a b s = b := by unfold cmpStep; cases a <;> cases b <;> simp_all
          rw [hc]
          apply Bool.eq_iff_iff.mpr
          rw [decide_eq_true_iff]
          exact hlt.symm
      · rw [if_neg huv]
        have hne : value (a :: u) ≠ value (b :: v) := by
          rw [hvu, hvv]; cases a <;> cases b <;> simp [Bool.toNat] <;> omega
        rw [if_neg hne]
        apply decide_eq_decide.mpr
        rw [hvu, hvv]
        cases a <;> cases b <;> simp [Bool.toNat] <;> omega

namespace FoldCell
open Three (act cfg)

/-- A fold of two framed words, the final state written into a cell. States `0`/`1` read a marker with state
`false`/`true`, `2`/`3` read a bit, `4` halts. -/
def machine (f : Bool → Bool → Bool → Bool) (init : Bool) : Machine 3 5 where
  descriptionBits := 0
  start := if init then 1 else 0
  halted := fun q => q.val == 4
  rule := fun q sc =>
    if q.val = 0 then
      some (if sc 0 then act 2 none none none .right .right .stay else act 4 none none (some false) .stay .stay .stay)
    else if q.val = 1 then
      some (if sc 0 then act 3 none none none .right .right .stay else act 4 none none (some true) .stay .stay .stay)
    else if q.val = 2 then
      some (if f (sc 0) (sc 1) false then act 1 none none none .right .right .stay
        else act 0 none none none .right .right .stay)
    else if q.val = 3 then
      some (if f (sc 0) (sc 1) true then act 1 none none none .right .right .stay
        else act 0 none none none .right .right .stay)
    else none

variable (f : Bool → Bool → Bool → Bool) (init : Bool)

def mark (s : Bool) : Fin 5 := if s then 1 else 0
def bitS (s : Bool) : Fin 5 := if s then 3 else 2

theorem mark_step (s : Bool) (X Y F : List Bool) (hx hy : ℕ) (hr : readTapeBit X hx = true) :
    step (machine f init) (cfg (mark s) X Y F hx hy 0) = some (cfg (bitS s) X Y F (hx + 1) (hy + 1) 0) := by
  cases s
  · exact Three.step_cfg (machine f init) 0 2 X Y F hx hy 0 none none none .right .right .stay (by simp [machine, hr])
  · exact Three.step_cfg (machine f init) 1 3 X Y F hx hy 0 none none none .right .right .stay (by simp [machine, hr])

theorem end_step (s c : Bool) (X Y : List Bool) (hx hy : ℕ) (hr : readTapeBit X hx = false) :
    step (machine f init) (cfg (mark s) X Y [c] hx hy 0) = some (cfg 4 X Y [s] hx hy 0) := by
  cases s
  · show step (machine f init) (cfg 0 X Y [c] hx hy 0) = some (cfg 4 X Y [false] hx hy 0)
    rw [Three.step_cfg (machine f init) 0 4 X Y [c] hx hy 0 none none (some false) .stay .stay .stay
      (by simp [machine, hr])]
    simp [Two.wr, HeadMove.apply, writeTapeBit]
  · show step (machine f init) (cfg 1 X Y [c] hx hy 0) = some (cfg 4 X Y [true] hx hy 0)
    rw [Three.step_cfg (machine f init) 1 4 X Y [c] hx hy 0 none none (some true) .stay .stay .stay
      (by simp [machine, hr])]
    simp [Two.wr, HeadMove.apply, writeTapeBit]

theorem bit_step (s a b : Bool) (X Y F : List Bool) (hx hy : ℕ) (ha : readTapeBit X hx = a) (hb : readTapeBit Y hy = b) :
    step (machine f init) (cfg (bitS s) X Y F hx hy 0) = some (cfg (mark (f a b s)) X Y F (hx + 1) (hy + 1) 0) := by
  cases s <;> cases h : f a b _
  · show step (machine f init) (cfg 2 X Y F hx hy 0) = some (cfg 0 X Y F (hx + 1) (hy + 1) 0)
    exact Three.step_cfg (machine f init) 2 0 X Y F hx hy 0 none none none .right .right .stay
      (by simp [machine, ha, hb, h])
  · show step (machine f init) (cfg 2 X Y F hx hy 0) = some (cfg 1 X Y F (hx + 1) (hy + 1) 0)
    exact Three.step_cfg (machine f init) 2 1 X Y F hx hy 0 none none none .right .right .stay
      (by simp [machine, ha, hb, h])
  · show step (machine f init) (cfg 3 X Y F hx hy 0) = some (cfg 0 X Y F (hx + 1) (hy + 1) 0)
    exact Three.step_cfg (machine f init) 3 0 X Y F hx hy 0 none none none .right .right .stay
      (by simp [machine, ha, hb, h])
  · show step (machine f init) (cfg 3 X Y F hx hy 0) = some (cfg 1 X Y F (hx + 1) (hy + 1) 0)
    exact Three.step_cfg (machine f init) 3 1 X Y F hx hy 0 none none none .right .right .stay
      (by simp [machine, ha, hb, h])

theorem timed (c : Bool) (u : List Bool) : ∀ (v : List Bool) (s : Bool), u.length = v.length →
    RecoveryExecution.Timed (machine f init) (2 * u.length + 1)
      (cfg (mark s) (frame u) (frame v) [c] 0 0 0)
      (cfg 4 (frame u) (frame v) [foldBits f s u v] (2 * u.length) (2 * u.length) 0) := by
  suffices key : ∀ (v preX preY : List Bool) (s : Bool), u.length = v.length →
      RecoveryExecution.Timed (machine f init) (2 * u.length + 1)
        (cfg (mark s) (preX ++ frame u) (preY ++ frame v) [c] preX.length preY.length 0)
        (cfg 4 (preX ++ frame u) (preY ++ frame v) [foldBits f s u v] (preX.length + 2 * u.length)
          (preY.length + 2 * u.length) 0) by
    intro v s hl
    simpa using key v [] [] s hl
  induction u with
  | nil =>
    intro v preX preY s _
    have hs := end_step f init s c (preX ++ frame []) (preY ++ frame v) preX.length preY.length
      (by simpa [frame] using Streaming.read_append preX [] false)
    simpa [frame, foldBits] using RecoveryExecution.Timed.single (p := machine f init) (by cases s <;> rfl) hs
  | cons a u ih =>
    intro v preX preY s hl
    obtain ⟨b, v, rfl⟩ : ∃ b v', v = b :: v' := by
      cases v with
      | nil => simp at hl
      | cons b v => exact ⟨b, v, rfl⟩
    have hl' : u.length = v.length := by simpa using hl
    have hr1 : readTapeBit (preX ++ frame (a :: u)) preX.length = true := by
      simpa [frame] using Streaming.read_append preX (a :: frame u) true
    have hra : readTapeBit (preX ++ frame (a :: u)) (preX.length + 1) = a := by
      simpa [frame] using Streaming.read_append (preX ++ [true]) (frame u) a
    have hrb : readTapeBit (preY ++ frame (b :: v)) (preY.length + 1) = b := by
      simpa [frame] using Streaming.read_append (preY ++ [true]) (frame v) b
    have hs1 := mark_step f init s (preX ++ frame (a :: u)) (preY ++ frame (b :: v)) [c] preX.length preY.length hr1
    have hs2 := bit_step f init s a b (preX ++ frame (a :: u)) (preY ++ frame (b :: v)) [c] (preX.length + 1)
      (preY.length + 1) hra hrb
    have t1 := RecoveryExecution.Timed.single (p := machine f init) (by cases s <;> rfl) hs1
    have t2 := RecoveryExecution.Timed.single (p := machine f init) (by cases s <;> rfl) hs2
    have tail := ih v (preX ++ [true, a]) (preY ++ [true, b]) (f a b s) hl'
    have eX : preX ++ [true, a] ++ frame u = preX ++ frame (a :: u) := by simp [frame]
    have eY : preY ++ [true, b] ++ frame v = preY ++ frame (b :: v) := by simp [frame]
    have e3 : (preX ++ [true, a]).length = preX.length + 1 + 1 := by simp
    have e4 : (preY ++ [true, b]).length = preY.length + 1 + 1 := by simp
    have e5 : foldBits f (f a b s) u v = foldBits f s (a :: u) (b :: v) := rfl
    have e7 : preX.length + 1 + 1 + 2 * u.length = preX.length + 2 * (a :: u).length := by simp; omega
    have e8 : preY.length + 1 + 1 + 2 * u.length = preY.length + 2 * (a :: u).length := by simp; omega
    rw [eX, eY, e3, e4, e5, e7, e8] at tail
    have := (t1.trans t2).trans tail
    rwa [show 1 + 1 + (2 * u.length + 1) = 2 * (a :: u).length + 1 by simp; omega] at this

theorem run (u v : List Bool) (c : Bool) (hl : u.length = v.length) :
    Step (machine f init) (2 * u.length + 1) ![0, 0, 0] ![frame u, frame v, [c]]
      ![2 * u.length, 2 * u.length, 0] ![frame u, frame v, [foldBits f init u v]] := by
  obtain ⟨r, hr, hf, hs⟩ := (timed f init c u v init hl).run rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  exacts [r, by cases init <;> exact hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega]

end FoldCell

/-! ## In-place ripple arithmetic `S := ripple g h c₀ S C` (addition, subtraction) -/

/-- A ripple over two words, low bit first: output bit `g a b c`, next carry `h a b c`. -/
def ripple (g h : Bool → Bool → Bool → Bool) : Bool → List Bool → List Bool → List Bool
  | c, a :: u, b :: v => g a b c :: ripple g h (h a b c) u v
  | _, _, _ => []

def sum3 (a b c : Bool) : Bool := xor (xor a b) c
def carry3 (a b c : Bool) : Bool := (a && b) || (c && xor a b)

theorem ripple_add (d x y : ℕ) (c : Bool) :
    ripple sum3 carry3 c (binary d x) (binary d y) = binary d (x + y + c.toNat) := by
  induction d generalizing x y c with
  | zero => rfl
  | succ d ih =>
    have e1 : binary (d + 1) x = (x % 2 == 1) :: binary d (x / 2) := rfl
    have e2 : binary (d + 1) y = (y % 2 == 1) :: binary d (y / 2) := rfl
    have e3 : binary (d + 1) (x + y + c.toNat) =
        ((x + y + c.toNat) % 2 == 1) :: binary d ((x + y + c.toNat) / 2) := rfl
    rw [e1, e2, e3]
    simp only [ripple]
    rw [ih]
    congr 1
    · rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;> rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
        cases c <;> simp [sum3, hx, hy, Nat.add_mod]
    · congr 1
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;> rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
        cases c <;> simp [carry3, hx, hy] <;> omega

namespace RippleIn
open Two (act cfg wr)

/-- Tape 0 the word (in place), tape 1 the operand. States `0`/`1` read a marker with carry `false`/`true`,
`2`/`3` rewrite a bit, `4` halts. -/
def machine (g h : Bool → Bool → Bool → Bool) (c₀ : Bool) : Machine 2 5 where
  descriptionBits := 0
  start := if c₀ then 1 else 0
  halted := fun q => q.val == 4
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then act 2 none none .right .right else act 4 none none .stay .stay)
    else if q.val = 1 then some (if sc 0 then act 3 none none .right .right else act 4 none none .stay .stay)
    else if q.val = 2 then
      some (if h (sc 0) (sc 1) false then act 1 (some (g (sc 0) (sc 1) false)) none .right .right
        else act 0 (some (g (sc 0) (sc 1) false)) none .right .right)
    else if q.val = 3 then
      some (if h (sc 0) (sc 1) true then act 1 (some (g (sc 0) (sc 1) true)) none .right .right
        else act 0 (some (g (sc 0) (sc 1) true)) none .right .right)
    else none

variable (g h : Bool → Bool → Bool → Bool) (c₀ : Bool)

def mark (c : Bool) : Fin 5 := if c then 1 else 0
def bitS (c : Bool) : Fin 5 := if c then 3 else 2

theorem mark_step (c : Bool) (S C : List Bool) (hs hc : ℕ) (hr : readTapeBit S hs = true) :
    step (machine g h c₀) (cfg (mark c) S C hs hc) = some (cfg (bitS c) S C (hs + 1) (hc + 1)) := by
  cases c
  · exact Two.step_cfg (machine g h c₀) 0 2 S C hs hc none none .right .right (by simp [machine, hr])
  · exact Two.step_cfg (machine g h c₀) 1 3 S C hs hc none none .right .right (by simp [machine, hr])

theorem end_step (c : Bool) (S C : List Bool) (hs hc : ℕ) (hr : readTapeBit S hs = false) :
    step (machine g h c₀) (cfg (mark c) S C hs hc) = some (cfg 4 S C hs hc) := by
  cases c
  · exact Two.step_cfg (machine g h c₀) 0 4 S C hs hc none none .stay .stay (by simp [machine, hr])
  · exact Two.step_cfg (machine g h c₀) 1 4 S C hs hc none none .stay .stay (by simp [machine, hr])

theorem bit_step (c a b : Bool) (S C : List Bool) (hs hc : ℕ) (ha : readTapeBit S hs = a) (hb : readTapeBit C hc = b) :
    step (machine g h c₀) (cfg (bitS c) S C hs hc) =
      some (cfg (mark (h a b c)) (writeTapeBit S hs (g a b c)) C (hs + 1) (hc + 1)) := by
  cases c <;> cases hh : h a b _
  · show step (machine g h c₀) (cfg 2 S C hs hc) = some (cfg 0 (writeTapeBit S hs (g a b false)) C (hs + 1) (hc + 1))
    exact Two.step_cfg (machine g h c₀) 2 0 S C hs hc (some (g a b false)) none .right .right
      (by simp [machine, ha, hb, hh])
  · show step (machine g h c₀) (cfg 2 S C hs hc) = some (cfg 1 (writeTapeBit S hs (g a b false)) C (hs + 1) (hc + 1))
    exact Two.step_cfg (machine g h c₀) 2 1 S C hs hc (some (g a b false)) none .right .right
      (by simp [machine, ha, hb, hh])
  · show step (machine g h c₀) (cfg 3 S C hs hc) = some (cfg 0 (writeTapeBit S hs (g a b true)) C (hs + 1) (hc + 1))
    exact Two.step_cfg (machine g h c₀) 3 0 S C hs hc (some (g a b true)) none .right .right
      (by simp [machine, ha, hb, hh])
  · show step (machine g h c₀) (cfg 3 S C hs hc) = some (cfg 1 (writeTapeBit S hs (g a b true)) C (hs + 1) (hc + 1))
    exact Two.step_cfg (machine g h c₀) 3 1 S C hs hc (some (g a b true)) none .right .right
      (by simp [machine, ha, hb, hh])

theorem timed (u : List Bool) : ∀ (v preS preC : List Bool) (c : Bool), u.length = v.length →
    RecoveryExecution.Timed (machine g h c₀) (2 * u.length + 1)
      (cfg (mark c) (preS ++ frame u) (preC ++ frame v) preS.length preC.length)
      (cfg 4 (preS ++ frame (ripple g h c u v)) (preC ++ frame v) (preS.length + 2 * u.length)
        (preC.length + 2 * u.length)) := by
  induction u with
  | nil =>
    intro v preS preC c _
    have hs := end_step g h c₀ c (preS ++ frame []) (preC ++ frame v) preS.length preC.length
      (by simpa [frame] using Streaming.read_append preS [] false)
    simpa [frame, ripple] using RecoveryExecution.Timed.single (p := machine g h c₀) (by cases c <;> rfl) hs
  | cons a u ih =>
    intro v preS preC c hl
    obtain ⟨b, v, rfl⟩ : ∃ b v', v = b :: v' := by
      cases v with
      | nil => simp at hl
      | cons b v => exact ⟨b, v, rfl⟩
    have hl' : u.length = v.length := by simpa using hl
    have hr1 : readTapeBit (preS ++ frame (a :: u)) preS.length = true := by
      simpa [frame] using Streaming.read_append preS (a :: frame u) true
    have hra : readTapeBit (preS ++ frame (a :: u)) (preS.length + 1) = a := by
      simpa [frame] using Streaming.read_append (preS ++ [true]) (frame u) a
    have hrb : readTapeBit (preC ++ frame (b :: v)) (preC.length + 1) = b := by
      simpa [frame] using Streaming.read_append (preC ++ [true]) (frame v) b
    have hs1 := mark_step g h c₀ c (preS ++ frame (a :: u)) (preC ++ frame (b :: v)) preS.length preC.length hr1
    have hs2 := bit_step g h c₀ c a b (preS ++ frame (a :: u)) (preC ++ frame (b :: v)) (preS.length + 1)
      (preC.length + 1) hra hrb
    have hw : writeTapeBit (preS ++ frame (a :: u)) (preS.length + 1) (g a b c) = preS ++ [true, g a b c] ++ frame u := by
      simpa [frame] using write_mid (preS ++ [true]) (frame u) a (g a b c)
    rw [hw] at hs2
    have t1 := RecoveryExecution.Timed.single (p := machine g h c₀) (by cases c <;> rfl) hs1
    have t2 := RecoveryExecution.Timed.single (p := machine g h c₀) (by cases c <;> rfl) hs2
    have tail := ih v (preS ++ [true, g a b c]) (preC ++ [true, b]) (h a b c) hl'
    have eC : preC ++ [true, b] ++ frame v = preC ++ frame (b :: v) := by simp [frame]
    have e3 : (preS ++ [true, g a b c]).length = preS.length + 1 + 1 := by simp
    have e4 : (preC ++ [true, b]).length = preC.length + 1 + 1 := by simp
    have e5 : preS ++ [true, g a b c] ++ frame (ripple g h (h a b c) u v) = preS ++ frame (ripple g h c (a :: u) (b :: v)) := by
      simp [frame, ripple]
    have e7 : preS.length + 1 + 1 + 2 * u.length = preS.length + 2 * (a :: u).length := by simp; omega
    have e8 : preC.length + 1 + 1 + 2 * u.length = preC.length + 2 * (a :: u).length := by simp; omega
    rw [eC, e3, e4, e5, e7, e8] at tail
    have := (t1.trans t2).trans tail
    rwa [show 1 + 1 + (2 * u.length + 1) = 2 * (a :: u).length + 1 by simp; omega] at this

theorem run (u v : List Bool) (hl : u.length = v.length) :
    Step (machine g h c₀) (2 * u.length + 1) ![0, 0] ![frame u, frame v]
      ![2 * u.length, 2 * u.length] ![frame (ripple g h c₀ u v), frame v] := by
  obtain ⟨r, hr, hf, hs⟩ := (timed g h c₀ u v [] [] c₀ hl).run rfl
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hr hf
  refine ⟨r, by cases c₀ <;> exact hr, ?_, ?_, by omega⟩
  · rw [hf]; rfl
  · rw [hf]; rfl

end RippleIn


/-! ## The merge, as pure semantics -/

/-- The register after loading up to record `k` of `L`: the current record, the last one once `L` is exhausted, or
the stale word `r0` if `L` is empty. -/
def reg (L : List (List Bool)) (k : ℕ) (r0 : List Bool) : List Bool := ((L.take (k + 1)).getLast?).getD r0

/-- The stream head after loading up to record `k`. -/
def pos (L : List (List Bool)) (k : ℕ) : ℕ := ((L.take (k + 1)).flatMap frame).length

/-- The merge state: records of `A` counted, records of `B` processed, the accumulated sum, the last test. -/
structure MS where
  i : ℕ
  j : ℕ
  s : ℕ
  t : Bool

/-- One merge step, exactly as the machine takes it. -/
def mstep (A B : List (List Bool)) (init : Bool) (ra0 rb0 : List Bool) (m : MS) : MS :=
  if (foldBits cmpStep init (reg A m.i ra0) (reg B m.j rb0) && decide (m.i < A.length)) then
    ⟨m.i + 1, m.j, m.s, true⟩
  else ⟨m.i, m.j + 1, m.s + m.i, false⟩

theorem reg_lt (L : List (List Bool)) (k : ℕ) (r0 : List Bool) (hk : k < L.length) : reg L k r0 = L[k] := by
  unfold reg
  rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left (by omega)]
  rw [List.getElem?_take, if_pos (by omega), show k + 1 - 1 = k by omega, List.getElem?_eq_getElem hk]
  rfl

/-- The relation the pass counts: `≤` (init `true`) or `<` (init `false`) on values. -/
def rel (init : Bool) (a b : List Bool) : Prop := value a < value b ∨ (init = true ∧ value a = value b)

instance (init : Bool) (a b : List Bool) : Decidable (rel init a b) := by unfold rel; infer_instance

theorem foldCmp_rel (init : Bool) (a b : List Bool) (h : a.length = b.length) :
    foldBits cmpStep init a b = decide (rel init a b) := by
  rw [foldCmp_value a b h]
  unfold rel
  by_cases he : value a = value b
  · rw [if_pos he]; cases init <;> simp [he]
  · rw [if_neg he]; apply decide_eq_decide.mpr; simp [he]

/-- The merge invariant along the path. -/
def Inv (A B : List (List Bool)) (init : Bool) (m : MS) : Prop :=
  m.i ≤ A.length ∧ m.j ≤ B.length ∧
    (∀ i' (hi' : i' < A.length), i' < m.i → ∀ j' (hj' : j' < B.length), m.j ≤ j' → rel init A[i'] B[j']) ∧
    m.s = ((B.take m.j).map (fun b => A.countP (fun a => decide (rel init a b)))).sum

theorem rel_mono_right (init : Bool) (a b b' : List Bool) (hbb : value b ≤ value b') (h : rel init a b) :
    rel init a b' := by
  unfold rel at *
  rcases h with h | ⟨hi, h⟩
  · exact Or.inl (by omega)
  · rcases Nat.lt_or_ge (value a) (value b') with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨hi, by omega⟩

theorem not_rel_mono_left (init : Bool) (a a' b : List Bool) (haa : value a ≤ value a') (h : ¬ rel init a b) :
    ¬ rel init a' b := by
  unfold rel at *
  intro h'
  apply h
  rcases h' with h' | ⟨hi, h'⟩
  · exact Or.inl (by omega)
  · rcases Nat.lt_or_ge (value a) (value b) with h'' | h''
    · exact Or.inl h''
    · exact Or.inr ⟨hi, by omega⟩

/-- When the `i` counted records of `A` are exactly those related to `b`, the count is `i`. -/
theorem countP_prefix (A : List (List Bool)) (p : List Bool → Bool) (i : ℕ) (hi : i ≤ A.length)
    (hyes : ∀ i' (h : i' < i), p (A[i']'(by omega)) = true) (hno : ∀ i' (h : i' < A.length), i ≤ i' → p A[i'] = false) :
    A.countP p = i := by
  have hsplit : A = A.take i ++ A.drop i := (List.take_append_drop i A).symm
  rw [hsplit, List.countP_append]
  have h1 : (A.take i).countP p = i := by
    rw [List.countP_eq_length.mpr]
    · simp; omega
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_take]
      exact hyes k (by simp at hk; omega)
  have h2 : (A.drop i).countP p = 0 := by
    rw [List.countP_eq_zero]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_drop]
    have := hno (i + k) (by simp at hk; omega) (by omega)
    simp [this]
  omega

theorem mstep_inv (A B : List (List Bool)) (init : Bool) (ra0 rb0 : List Bool) (W : ℕ)
    (hA : ∀ a ∈ A, a.length = W) (hB : ∀ b ∈ B, b.length = W)
    (sA : A.Pairwise (fun a b => value a ≤ value b)) (sB : B.Pairwise (fun a b => value a ≤ value b))
    (m : MS) (hm : Inv A B init m) (hj : m.j < B.length) : Inv A B init (mstep A B init ra0 rb0 m) := by
  obtain ⟨hi, hjle, hall, hs⟩ := hm
  have hregB : reg B m.j rb0 = B[m.j] := reg_lt B m.j rb0 hj
  unfold mstep
  by_cases hc : (foldBits cmpStep init (reg A m.i ra0) (reg B m.j rb0) && decide (m.i < A.length)) = true
  · rw [if_pos hc]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hcmp, hiA⟩ := hc
    have hregA : reg A m.i ra0 = A[m.i] := reg_lt A m.i ra0 hiA
    rw [hregA, hregB, foldCmp_rel init _ _ (by rw [hA _ (List.getElem_mem _), hB _ (List.getElem_mem _)])] at hcmp
    simp only [decide_eq_true_eq] at hcmp
    refine ⟨by simp; omega, hjle, fun i' hi' hi'' j' hj' hjj => ?_, hs⟩
    rcases Nat.lt_or_ge i' m.i with h | h
    · exact hall i' hi' h j' hj' hjj
    · have : i' = m.i := by simp at hi''; omega
      subst this
      rcases Nat.eq_or_lt_of_le hjj with h' | h'
      · subst h'; exact hcmp
      · exact rel_mono_right init _ _ _ ((List.pairwise_iff_getElem.mp sB) m.j j' hj hj' h') hcmp
  · rw [if_neg hc]
    refine ⟨hi, by simp; omega, fun i' hi' hi'' j' hj' hjj => hall i' hi' hi'' j' hj' (by simp at hjj; omega), ?_⟩
    rw [hs, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    congr 1
    symm
    apply countP_prefix A _ m.i hi
    · intro i' h
      simp only [decide_eq_true_eq]
      exact hall i' (by omega) h m.j hj le_rfl
    · intro i' h hge
      simp only [decide_eq_false_iff_not]
      have hnot : ¬ rel init A[m.i] B[m.j] ∨ ¬ m.i < A.length := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and_or] at hc
        rcases hc with hc | hc
        · left
          by_cases hiA : m.i < A.length
          · rw [reg_lt A m.i ra0 hiA, hregB, foldCmp_rel init _ _ (by rw [hA _ (List.getElem_mem _),
              hB _ (List.getElem_mem _)])] at hc
            simpa using hc
          · exact absurd (by omega : m.i < A.length) hiA
        · right; exact hc
      rcases hnot with hn | hn
      · rcases Nat.eq_or_lt_of_le hge with h' | h'
        · subst h'; exact hn
        · exact not_rel_mono_left init _ _ _ ((List.pairwise_iff_getElem.mp sA) m.i i' (by omega) h h') hn
      · exact absurd (by omega : m.i < A.length) hn
















/-! ## The merge pass machine (12 tapes)

Tapes: 0 `A` and 1 `B` (the streams); 2 `RA` and 3 `RB` (the registers); 4 `CA` (the count); 5 the pass's sum;
6 the other pass's sum (untouched); 7 `T`, 8 `AV`, 9 `BV` (cells); 10 a spare cell; 11 the rewind log. -/

def andOp : Bool → Bool → Bool → Bool := fun t a _ => t && a


section PassStages

end PassStages


/-! ### Loading the next record -/

/-- A stream: the framed words, then the terminator. -/
def streamOf (L : List (List Bool)) : List Bool := L.flatMap frame ++ [false]

/-- The start of record `k` on the stream. -/
def pre (L : List (List Bool)) (k : ℕ) : ℕ := ((L.take k).flatMap frame).length

theorem streamOf_split (L : List (List Bool)) (k : ℕ) (hk : k < L.length) :
    streamOf L = (L.take k).flatMap frame ++ frame L[k] ++ ((L.drop (k + 1)).flatMap frame ++ [false]) := by
  have e : L = L.take k ++ L[k] :: L.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  calc streamOf L = streamOf (L.take k ++ L[k] :: L.drop (k + 1)) := congrArg streamOf e
    _ = _ := by simp only [streamOf, List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem pre_succ (L : List (List Bool)) (k : ℕ) (hk : k < L.length) :
    pre L (k + 1) = pre L k + (2 * L[k].length + 1) := by
  unfold pre
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append, List.length_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, frame_length]

theorem read_pre (L : List (List Bool)) (k : ℕ) (hne : ∀ w ∈ L, w ≠ []) :
    readTapeBit (streamOf L) (pre L k) = decide (k < L.length) := by
  by_cases hk : k < L.length
  · rw [streamOf_split L k hk, decide_eq_true hk]
    obtain ⟨b, w, hw⟩ : ∃ b w, L[k] = b :: w := by
      cases h : L[k] with
      | nil => exact absurd h (hne _ (List.getElem_mem hk))
      | cons b w => exact ⟨b, w, rfl⟩
    rw [hw]
    simpa [frame, pre, List.append_assoc] using Streaming.read_append ((L.take k).flatMap frame)
      (b :: frame w ++ ((L.drop (k + 1)).flatMap frame ++ [false])) true
  · rw [decide_eq_false hk]
    unfold pre streamOf
    rw [List.take_of_length_le (by omega)]
    simpa using Streaming.read_append (L.flatMap frame) [] false

def loadCost (W : ℕ) : ℕ := 2 * (2 * W + 1) + 2 + 1 + 1 + 1 + 1 + 2

section Loads

end Loads


/-! ### One merge pass as one `Step` -/










/-! ## The join count: pass `≤`, rewind the streams, pass `<` (sums swapped), subtract -/


/-! ## Cost in a class, the bridge to the kernel reference, twins -/




end NearCubicWires.WireExponent3_5.Block
