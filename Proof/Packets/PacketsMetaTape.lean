import Proof.MachineModel.Runs
import Proof.Amplification.RecoveryCallController
import Proof.Amplification.RecoveryCursorCalls

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsMeta
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound

/-! ## Tape helpers -/

theorem read_write (l : List Bool) (p j : ℕ) (b : Bool) :
    readTapeBit (writeTapeBit l p b) j = if j = p then b else readTapeBit l j := by
  induction l generalizing p j with
  | nil =>
    induction p generalizing j with
    | zero => cases j <;> simp [writeTapeBit, readTapeBit]
    | succ p ih =>
      cases j with
      | zero => simp [writeTapeBit, readTapeBit]
      | succ j =>
        have h := ih j
        simp only [writeTapeBit, readTapeBit, List.getD_cons_succ] at h ⊢
        rw [h]
        simp
  | cons x l ih =>
    cases p with
    | zero => cases j <;> simp [writeTapeBit, readTapeBit]
    | succ p =>
      cases j with
      | zero => simp [writeTapeBit, readTapeBit]
      | succ j =>
        have h := ih p j
        simp only [writeTapeBit, readTapeBit, List.getD_cons_succ] at h ⊢
        rw [h]
        simp

/-- Successive writes from position `p`. -/
def writes (l : List Bool) (p : ℕ) : List Bool → List Bool
  | [] => l
  | v :: vs => writes (writeTapeBit l p v) (p + 1) vs

theorem read_writes (vs : List Bool) (l : List Bool) (p j : ℕ) :
    readTapeBit (writes l p vs) j =
      if p ≤ j ∧ j < p + vs.length then vs.getD (j - p) false else readTapeBit l j := by
  induction vs generalizing l p with
  | nil => simp [writes]; omega
  | cons v vs ih =>
    simp only [writes, ih, read_write, List.length_cons]
    by_cases h1 : j = p
    · subst h1; simp
    · by_cases h2 : p + 1 ≤ j ∧ j < p + 1 + vs.length
      · have h3 : p ≤ j ∧ j < p + (vs.length + 1) := by omega
        rw [if_pos h2, if_pos h3]
        have e : j - p = (j - (p + 1)) + 1 := by omega
        rw [e]; simp
      · have h3 : ¬ (p ≤ j ∧ j < p + (vs.length + 1)) := by omega
        rw [if_neg h2, if_neg h3, if_neg h1]

/-! ## Tape semantics -/

/-- The semantic role of one tape. -/
inductive TS where
  /-- A width-`W` register holding `x` in cells `1..W` (LSB at cell 1), head at 0. -/
  | reg (x : ℕ)
  /-- The ruler: cell 0 blank, cells `1..W` marked, cell `W+1` blank; head at 0. -/
  | ruler
  /-- A flag bit at cell 0, head at 0. -/
  | flag (b : Bool)
  /-- Arbitrary cell contents `f` with head at `h`. -/
  | cells (f : ℕ → Bool) (h : ℕ)
  /-- The unary output: exactly `replicate n true`, head at `n`. -/
  | out (n : ℕ)
  /-- Unconstrained. -/
  | any

def TR (W : ℕ) : TS → ℕ → List Bool → Prop
  | .reg x, h, l => h = 0 ∧ ∀ j, 1 ≤ j → j ≤ W → readTapeBit l j = x.testBit (j - 1)
  | .ruler, h, l => h = 0 ∧ readTapeBit l 0 = false ∧ (∀ j, 1 ≤ j → j ≤ W → readTapeBit l j = true) ∧
      readTapeBit l (W + 1) = false
  | .flag b, h, l => h = 0 ∧ readTapeBit l 0 = b
  | .cells f h0, h, l => h = h0 ∧ ∀ j, readTapeBit l j = f j
  | .out n, h, l => h = n ∧ l = List.replicate n true
  | .any, _, _ => True

/-- The machine realizes the semantic transition `σ ⟶ σ'` within `n` steps. -/
def LRuns {t s : ℕ} (W : ℕ) (P : Machine t s) (n : ℕ) (σ σ' : Fin t → TS) : Prop :=
  ∀ (H : Fin t → ℕ) (A : Fin t → List Bool), (∀ i, TR W (σ i) (H i) (A i)) →
    ∃ (H' : Fin t → ℕ) (A' : Fin t → List Bool), Step P n H A H' A' ∧ ∀ i, TR W (σ' i) (H' i) (A' i)

theorem LRuns.enlarge {t s W : ℕ} {P : Machine t s} {n m : ℕ} {σ σ' : Fin t → TS}
    (h : LRuns W P n σ σ') (hnm : n ≤ m) : LRuns W P m σ σ' := by
  intro H A hA
  obtain ⟨H', A', hs, h'⟩ := h H A hA
  exact ⟨H', A', hs.enlarge hnm, h'⟩

theorem LRuns.weaken {t s W : ℕ} {P : Machine t s} {n : ℕ} {σ σ' σ'' : Fin t → TS}
    (h : LRuns W P n σ σ') (hw : ∀ i H A, TR W (σ' i) H A → TR W (σ'' i) H A) : LRuns W P n σ σ'' := by
  intro H A hA
  obtain ⟨H', A', hs, h'⟩ := h H A hA
  exact ⟨H', A', hs, fun i => hw i _ _ (h' i)⟩

theorem LRuns.seq {t sp sq W : ℕ} {P : Machine t sp} {Q : Machine t sq} {n m : ℕ}
    {σ σ' σ'' : Fin t → TS} (hp : LRuns W P n σ σ') (hq : LRuns W Q m σ' σ'') :
    LRuns W (Composition.machine P Q) (n + 1 + m) σ σ'' := by
  intro H A hA
  obtain ⟨H1, A1, s1, h1⟩ := hp H A hA
  obtain ⟨H2, A2, s2, h2⟩ := hq H1 A1 h1
  exact ⟨H2, A2, s1.seq s2, h2⟩

/-! ## Docking -/

theorem dockH_self {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) (H : Fin u → ℕ) :
    dockH slots H (fun j => H (slots j)) = H := by
  funext i
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    exact dockH_slot slots hi H _ j
  · exact dockH_other slots H _ i (fun j hj => h ⟨j, hj⟩)

theorem install_self {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (A : Fin u → List Bool) : install slots A (fun j => A (slots j)) = A := by
  funext i
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    exact install_slot slots hi A _ j
  · exact install_other slots A _ i (fun j hj => h ⟨j, hj⟩)

/-- **Docking.** A local run on the slot tapes is a run of the focused machine; tapes outside the slots
keep their roles. -/
theorem LRuns.focus {m N s W : ℕ} {P : Machine m s} {n : ℕ} {τ τ' : Fin m → TS}
    (h : LRuns W P n τ τ') (slots : Fin m → Fin N) (hi : Function.Injective slots)
    (σ σ' : Fin N → TS) (hin : ∀ j, σ (slots j) = τ j) (hout : ∀ j, σ' (slots j) = τ' j)
    (hrest : ∀ i, (∀ j, slots j ≠ i) → σ' i = σ i) :
    LRuns W (RecoveryFocus.machine slots P) n σ σ' := by
  intro H A hA
  obtain ⟨H', A', hs, h'⟩ := h (fun j => H (slots j)) (fun j => A (slots j))
    (fun j => by rw [← hin j]; exact hA (slots j))
  have hf := hs.focus slots hi H A
  rw [dockH_self slots hi H, install_self slots hi A] at hf
  refine ⟨_, _, hf, fun i => ?_⟩
  by_cases hx : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := hx
    rw [dockH_slot slots hi, install_slot slots hi, hout j]
    exact h' j
  · have hn : ∀ j, slots j ≠ i := fun j hj => hx ⟨j, hj⟩
    rw [dockH_other slots H H' i hn, install_other slots A A' i hn, hrest i hn]
    exact hA i

/-- Docking with the ambient role map updated at the slots only. -/
noncomputable def dockS {m N : ℕ} (slots : Fin m → Fin N) (σ : Fin N → TS) (τ' : Fin m → TS) : Fin N → TS :=
  fun i => match RecoveryFocus.pick slots i with | some j => τ' j | none => σ i

theorem dockS_slot {m N : ℕ} (slots : Fin m → Fin N) (hi : Function.Injective slots) (σ : Fin N → TS)
    (τ' : Fin m → TS) (j : Fin m) : dockS slots σ τ' (slots j) = τ' j := by
  simp [dockS, RecoveryFocus.pick_slot slots hi]

theorem dockS_other {m N : ℕ} (slots : Fin m → Fin N) (σ : Fin N → TS) (τ' : Fin m → TS) (i : Fin N)
    (hn : ∀ j, slots j ≠ i) : dockS slots σ τ' i = σ i := by
  classical
  have he : ¬∃ j, slots j = i := by rintro ⟨j, hj⟩; exact hn j hj
  simp [dockS, RecoveryFocus.pick, he]

theorem LRuns.dock {m N s W : ℕ} {P : Machine m s} {n : ℕ} {τ τ' : Fin m → TS}
    (h : LRuns W P n τ τ') (slots : Fin m → Fin N) (hi : Function.Injective slots)
    (σ : Fin N → TS) (hin : ∀ j, σ (slots j) = τ j) :
    LRuns W (RecoveryFocus.machine slots P) n σ (dockS slots σ τ') :=
  h.focus slots hi σ _ hin (dockS_slot slots hi σ τ') (dockS_other slots σ τ')

section Control
variable {t : ℕ}

/-- The step of a timed run to a `Step`. -/
theorem step_of_timed {s : ℕ} {P : Machine t s} {n m : ℕ} {H H' : Fin t → ℕ} {A A' : Fin t → List Bool}
    {q : Fin s} {c : Configuration t s} (h : Timed P n c ⟨q, H', A'⟩) (hc : c = ⟨P.start, H, A⟩)
    (hq : P.halted q = true) (hnm : n ≤ m) :
    Step P m H A H' A' := by
  subst hc
  obtain ⟨r, hr, hf, _⟩ := h.run hq
  have hs : Step P n H A H' A' := Step.of_run hr (by rw [hf]) (by rw [hf])
  exact hs.enlarge hnm

theorem scanned_flag {W : ℕ} {b : Bool} {H : ℕ} {l : List Bool} (h : TR W (.flag b) H l) :
    readTapeBit l H = b := by
  obtain ⟨h0, h1⟩ := h
  rw [h0]; exact h1

/-! ### Branch -/

def iteSizes (a b c : ℕ) : Fin 3 → ℕ := ![a, b, c]

def itePrograms {a b c : ℕ} (C : Machine t a) (P : Machine t b) (Q : Machine t c) :
    (j : Fin 3) → Machine t (iteSizes a b c j)
  | ⟨0, _⟩ => C
  | ⟨1, _⟩ => P
  | ⟨2, _⟩ => Q
  | ⟨n + 3, h⟩ => False.elim (by omega)

def iteNext {a b c : ℕ} (flag : Fin t) (j : Fin 3) (_ : Fin (iteSizes a b c j)) (bits : Fin t → Bool) :
    Option (Fin 3) :=
  if j.val = 0 then (if bits flag then some 1 else some 2) else none

theorem iteNext_true {a b c : ℕ} (flag : Fin t) (q : Fin (iteSizes a b c 0)) (bits : Fin t → Bool)
    (h : bits flag = true) : iteNext flag 0 q bits = some 1 := by simp [iteNext, h]
theorem iteNext_false {a b c : ℕ} (flag : Fin t) (q : Fin (iteSizes a b c 0)) (bits : Fin t → Bool)
    (h : bits flag = false) : iteNext flag 0 q bits = some 2 := by simp [iteNext, h]
theorem iteNext_one {a b c : ℕ} (flag : Fin t) (q : Fin (iteSizes a b c 1)) (bits : Fin t → Bool) :
    iteNext flag 1 q bits = none := rfl
theorem iteNext_two {a b c : ℕ} (flag : Fin t) (q : Fin (iteSizes a b c 2)) (bits : Fin t → Bool) :
    iteNext flag 2 q bits = none := rfl

/-- Run `C`, then `P` if the flag tape reads `true`, else `Q`. -/
noncomputable def Ite {a b c : ℕ} (C : Machine t a) (P : Machine t b) (Q : Machine t c) (flag : Fin t) :=
  RecoveryCalls.machine (iteSizes a b c) (itePrograms C P Q) 0 (iteNext flag)

theorem Ite.runs {a b c W : ℕ} (C : Machine t a) (P : Machine t b) (Q : Machine t c) (flag : Fin t)
    {nc np nq : ℕ} {σ τ ρ : Fin t → TS} (bit : Bool)
    (hc : LRuns W C nc σ τ) (hf : τ flag = .flag bit)
    (hp : bit = true → LRuns W P np τ ρ) (hq : bit = false → LRuns W Q nq τ ρ) :
    LRuns W (Ite C P Q flag) (nc + np + nq + 2) σ ρ := by
  intro H A hA
  obtain ⟨H1, A1, ⟨r1, hr1, hh1, ht1, hs1⟩, h1⟩ := hc H A hA
  have hscan : r1.final.scanned flag = bit := by
    have := h1 flag
    rw [hf] at this
    unfold Configuration.scanned
    rw [hh1, ht1]
    exact scanned_flag this
  cases bit with
  | true =>
    obtain ⟨H2, A2, ⟨r2, hr2, hh2, ht2, hs2⟩, h2⟩ := hp rfl H1 A1 h1
    obtain ⟨n1, hn1, t1⟩ := call_receipt (iteSizes a b c) (itePrograms C P Q) 0 (iteNext flag) 0 1 nc _ r1 hr1
      (iteNext_true flag _ _ hscan)
    have hr2' : runFrom (itePrograms C P Q 1) np
        (RecoveryCalls.restarted (itePrograms C P Q 1) r1.final.heads r1.final.tapes) = some r2 := by
      rw [hh1, ht1]; exact hr2
    obtain ⟨n2, hn2, t2⟩ := stop_receipt (iteSizes a b c) (itePrograms C P Q) 0 (iteNext flag) 1 np _ r2 hr2'
      (iteNext_one flag _ _)
    have tt := t1.trans t2
    refine ⟨H2, A2, ?_, h2⟩
    have e : RecoveryCalls.stopped (iteSizes a b c) r2.final.heads r2.final.tapes =
        ⟨RecoveryCalls.controlCode (iteSizes a b c) none, H2, A2⟩ := by
      rw [hh2, ht2]; rfl
    rw [e] at tt
    exact step_of_timed tt rfl (by simp [Ite, RecoveryCalls.machine]) (by omega)
  | false =>
    obtain ⟨H2, A2, ⟨r2, hr2, hh2, ht2, hs2⟩, h2⟩ := hq rfl H1 A1 h1
    obtain ⟨n1, hn1, t1⟩ := call_receipt (iteSizes a b c) (itePrograms C P Q) 0 (iteNext flag) 0 2 nc _ r1 hr1
      (iteNext_false flag _ _ hscan)
    have hr2' : runFrom (itePrograms C P Q 2) nq
        (RecoveryCalls.restarted (itePrograms C P Q 2) r1.final.heads r1.final.tapes) = some r2 := by
      rw [hh1, ht1]; exact hr2
    obtain ⟨n2, hn2, t2⟩ := stop_receipt (iteSizes a b c) (itePrograms C P Q) 0 (iteNext flag) 2 nq _ r2 hr2'
      (iteNext_two flag _ _)
    have tt := t1.trans t2
    refine ⟨H2, A2, ?_, h2⟩
    have e : RecoveryCalls.stopped (iteSizes a b c) r2.final.heads r2.final.tapes =
        ⟨RecoveryCalls.controlCode (iteSizes a b c) none, H2, A2⟩ := by
      rw [hh2, ht2]; rfl
    rw [e] at tt
    exact step_of_timed tt rfl (by simp [Ite, RecoveryCalls.machine]) (by omega)

/-! ### Loop -/

def loopSizes (a b : ℕ) : Fin 2 → ℕ := ![a, b]

def loopPrograms {a b : ℕ} (C : Machine t a) (B : Machine t b) : (j : Fin 2) → Machine t (loopSizes a b j)
  | ⟨0, _⟩ => C
  | ⟨1, _⟩ => B
  | ⟨n + 2, h⟩ => False.elim (by omega)

def loopNext {a b : ℕ} (flag : Fin t) (j : Fin 2) (_ : Fin (loopSizes a b j)) (bits : Fin t → Bool) :
    Option (Fin 2) :=
  if j.val = 0 then (if bits flag then some 1 else none) else some 0

theorem loopNext_true {a b : ℕ} (flag : Fin t) (q : Fin (loopSizes a b 0)) (bits : Fin t → Bool)
    (h : bits flag = true) : loopNext flag 0 q bits = some 1 := by simp [loopNext, h]
theorem loopNext_false {a b : ℕ} (flag : Fin t) (q : Fin (loopSizes a b 0)) (bits : Fin t → Bool)
    (h : bits flag = false) : loopNext flag 0 q bits = none := by simp [loopNext, h]
theorem loopNext_one {a b : ℕ} (flag : Fin t) (q : Fin (loopSizes a b 1)) (bits : Fin t → Bool) :
    loopNext flag 1 q bits = some 0 := rfl

/-- `while (C; flag) do B`: run the test `C`; if the flag reads `true`, run `B` and repeat. -/
noncomputable def Loop {a b : ℕ} (C : Machine t a) (B : Machine t b) (flag : Fin t) :=
  RecoveryCalls.machine (loopSizes a b) (loopPrograms C B) 0 (loopNext flag)

theorem Loop.timed {a b W : ℕ} (C : Machine t a) (B : Machine t b) (flag : Fin t) {nc nb : ℕ}
    (σ τ : ℕ → Fin t → TS) (n : ℕ)
    (hc : ∀ i, i ≤ n → LRuns W C nc (σ i) (τ i)) (hf : ∀ i, i ≤ n → τ i flag = .flag (decide (i < n)))
    (hb : ∀ i, i < n → LRuns W B nb (τ i) (σ (i + 1))) :
    ∀ m i, i + m = n → ∀ (H : Fin t → ℕ) (A : Fin t → List Bool), (∀ x, TR W (σ i x) (H x) (A x)) →
      ∃ k H' A', k ≤ (m + 1) * (nc + nb + 2) ∧
        Timed (Loop C B flag) k
          (controlConfig (RecoveryCalls.code (loopSizes a b) 0) (RecoveryCalls.restarted C H A))
          ⟨RecoveryCalls.controlCode (loopSizes a b) none, H', A'⟩ ∧ ∀ x, TR W (τ n x) (H' x) (A' x) := by
  intro m
  induction m with
  | zero =>
    intro i hi H A hA
    have hin : i = n := by omega
    subst hin
    obtain ⟨H1, A1, ⟨r1, hr1, hh1, ht1, hs1⟩, h1⟩ := hc i (le_refl _) H A hA
    have hscan : r1.final.scanned flag = false := by
      have := h1 flag
      rw [hf i (le_refl _)] at this
      unfold Configuration.scanned
      rw [hh1, ht1]
      simpa using scanned_flag this
    obtain ⟨n1, hn1, t1⟩ := stop_receipt (loopSizes a b) (loopPrograms C B) 0 (loopNext flag) 0 nc _ r1 hr1
      (loopNext_false flag _ _ hscan)
    refine ⟨n1, H1, A1, by omega, ?_, h1⟩
    have e : RecoveryCalls.stopped (loopSizes a b) r1.final.heads r1.final.tapes =
        ⟨RecoveryCalls.controlCode (loopSizes a b) none, H1, A1⟩ := by
      rw [hh1, ht1]; rfl
    rw [e] at t1
    exact t1
  | succ m ih =>
    intro i hi H A hA
    have hin : i < n := by omega
    obtain ⟨H1, A1, ⟨r1, hr1, hh1, ht1, hs1⟩, h1⟩ := hc i (by omega) H A hA
    have hscan : r1.final.scanned flag = true := by
      have := h1 flag
      rw [hf i (by omega)] at this
      unfold Configuration.scanned
      rw [hh1, ht1]
      simpa [hin] using scanned_flag this
    obtain ⟨n1, hn1, t1⟩ := call_receipt (loopSizes a b) (loopPrograms C B) 0 (loopNext flag) 0 1 nc _ r1 hr1
      (loopNext_true flag _ _ hscan)
    obtain ⟨H2, A2, ⟨r2, hr2, hh2, ht2, hs2⟩, h2⟩ := hb i hin H1 A1 h1
    have hr2' : runFrom (loopPrograms C B 1) nb
        (RecoveryCalls.restarted (loopPrograms C B 1) r1.final.heads r1.final.tapes) = some r2 := by
      rw [hh1, ht1]; exact hr2
    obtain ⟨n2, hn2, t2⟩ := call_receipt (loopSizes a b) (loopPrograms C B) 0 (loopNext flag) 1 0 nb _ r2 hr2'
      (loopNext_one flag _ _)
    obtain ⟨k, H', A', hk, t3, h3⟩ := ih (i + 1) (by omega) H2 A2 h2
    have e : RecoveryCalls.restarted (loopPrograms C B 0) r2.final.heads r2.final.tapes =
        RecoveryCalls.restarted C H2 A2 := by
      rw [hh2, ht2]; rfl
    rw [e] at t2
    refine ⟨n1 + n2 + k, H', A', ?_, (t1.trans t2).trans t3, h3⟩
    have : (m + 1 + 1) * (nc + nb + 2) = (m + 1) * (nc + nb + 2) + (nc + nb + 2) := by ring
    omega

theorem Loop.runs {a b W : ℕ} (C : Machine t a) (B : Machine t b) (flag : Fin t) {nc nb : ℕ}
    (σ τ : ℕ → Fin t → TS) (n : ℕ)
    (hc : ∀ i, i ≤ n → LRuns W C nc (σ i) (τ i)) (hf : ∀ i, i ≤ n → τ i flag = .flag (decide (i < n)))
    (hb : ∀ i, i < n → LRuns W B nb (τ i) (σ (i + 1))) :
    LRuns W (Loop C B flag) ((n + 1) * (nc + nb + 2)) (σ 0) (τ n) := by
  intro H A hA
  obtain ⟨k, H', A', hk, tt, h'⟩ := Loop.timed C B flag σ τ n hc hf hb n 0 (by omega) H A hA
  exact ⟨H', A', step_of_timed tt rfl (by simp [Loop, RecoveryCalls.machine]) hk, h'⟩

end Control

end NearCubicWires.PacketsMeta

