import Proof.Packets.PacketsMetaRegs

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsMeta
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
noncomputable section

/-! ## Stream contents -/

/-- The content of a stream tape holding `w` at cells `1..|w|`. -/
def sf (w : List Bool) : ℕ → Bool := fun j => readTapeBit (false :: w) j

/-- The blank content. -/
def blank : ℕ → Bool := fun _ => false

theorem sf_succ (w : List Bool) (j : ℕ) : sf w (j + 1) = w.getD j false := by
  simp [sf, readTapeBit]

theorem sf_marks_true (n j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ n) : sf (List.replicate n true) j = true := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [sf_succ, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_replicate]

/-! ## One fixed action -/

/-- One action chosen from the scanned bits, then halt. -/
def oneStep (t : ℕ) (act : (Fin t → Bool) → (Fin t → Option Bool) × (Fin t → HeadMove)) : Machine t 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q b => if q.val = 0 then some ⟨1, (act b).1, (act b).2⟩ else none

/-- The tapes after one action. -/
def acted {t : ℕ} (w : Fin t → Option Bool) (H : Fin t → ℕ) (A : Fin t → List Bool) : Fin t → List Bool :=
  fun i => match w i with
    | none => A i
    | some b => writeTapeBit (A i) (H i) b

theorem oneStep_run (t : ℕ) (act : (Fin t → Bool) → (Fin t → Option Bool) × (Fin t → HeadMove))
    (H : Fin t → ℕ) (A : Fin t → List Bool) :
    Step (oneStep t act) 1 H A
      (fun i => ((act (fun j => readTapeBit (A j) (H j))).2 i).apply (H i))
      (acted (act (fun j => readTapeBit (A j) (H j))).1 H A) := by
  have hs : LocalBitMultitape.step (oneStep t act) ⟨0, H, A⟩ =
      some ⟨1, fun i => ((act (fun j => readTapeBit (A j) (H j))).2 i).apply (H i),
        acted (act (fun j => readTapeBit (A j) (H j))).1 H A⟩ := by
    simp only [LocalBitMultitape.step, oneStep]
    rfl
  obtain ⟨r, hr, hf, _⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (by rw [hf]) (by rw [hf])

/-! ## Move while a tape reads `true` -/

/-- Move every head by `mv` while tape `k` reads `true`; halt at the first `false`. -/
def whileM (t : ℕ) (k : Fin t) (mv : Fin t → HeadMove) : Machine t 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q b => if q.val = 0 then
      (if b k then some ⟨0, fun _ => none, mv⟩ else some ⟨1, fun _ => none, fun _ => .stay⟩)
    else none

/-- The heads after `j` moves. -/
def iterH {t : ℕ} (mv : Fin t → HeadMove) (j : ℕ) (H : Fin t → ℕ) : Fin t → ℕ :=
  fun i => (fun h => (mv i).apply h)^[j] (H i)

theorem iterH_succ {t : ℕ} (mv : Fin t → HeadMove) (j : ℕ) (H : Fin t → ℕ) :
    iterH mv (j + 1) H = iterH mv j (fun i => (mv i).apply (H i)) := by
  funext i; simp only [iterH, Function.iterate_succ_apply]

theorem whileM_timed (t : ℕ) (k : Fin t) (mv : Fin t → HeadMove) (A : Fin t → List Bool) :
    ∀ (m : ℕ) (H : Fin t → ℕ), (∀ j, j < m → readTapeBit (A k) (iterH mv j H k) = true) →
      readTapeBit (A k) (iterH mv m H k) = false →
      Timed (whileM t k mv) (m + 1) ⟨0, H, A⟩ ⟨1, iterH mv m H, A⟩ := by
  intro m
  induction m with
  | zero =>
    intro H _ hf
    refine Timed.single (by rfl) ?_
    have hf' : readTapeBit (A k) (H k) = false := hf
    simp only [LocalBitMultitape.step, whileM, Configuration.scanned, hf']
    simp only [Fin.isValue, ↓reduceIte, Bool.false_eq_true, Option.map_some]
    refine congrArg some ?_
    apply configuration_ext
    · rfl
    · funext i; rfl
    · rfl
  | succ m ih =>
    intro H ht hf
    have h0 : readTapeBit (A k) (H k) = true := ht 0 (by omega)
    have hs : LocalBitMultitape.step (whileM t k mv) ⟨0, H, A⟩ =
        some ⟨0, fun i => (mv i).apply (H i), A⟩ := by
      simp only [LocalBitMultitape.step, whileM, Configuration.scanned, h0]
      simp only [Fin.isValue, ↓reduceIte, Option.map_some]
      refine congrArg some ?_
      apply configuration_ext
      · rfl
      · rfl
      · rfl
    have h2 := ih (fun i => (mv i).apply (H i))
      (fun j hj => by rw [← iterH_succ]; exact ht (j + 1) (by omega))
      (by rw [← iterH_succ]; exact hf)
    rw [← iterH_succ] at h2
    have h := (Timed.single (by rfl) hs).trans h2
    rwa [show 1 + (m + 1) = m + 1 + 1 by omega] at h

theorem whileM_run (t : ℕ) (k : Fin t) (mv : Fin t → HeadMove) (A : Fin t → List Bool) (m : ℕ)
    (H : Fin t → ℕ) (ht : ∀ j, j < m → readTapeBit (A k) (iterH mv j H k) = true)
    (hf : readTapeBit (A k) (iterH mv m H k) = false) :
    Step (whileM t k mv) (m + 1) H A (iterH mv m H) A := by
  obtain ⟨r, hr, hfin, _⟩ := (whileM_timed t k mv A m H ht hf).run (by rfl)
  exact Step.of_run hr (by rw [hfin]) (by rw [hfin])

theorem iter_left (j h : ℕ) : (fun h => HeadMove.left.apply h)^[j] h = h - j := by
  induction j generalizing h with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, ih]; simp [HeadMove.apply]; omega

/-! ## Rewind a stream -/

/-- Tapes: 0 marks, 1 stream. One step left, then left while the marks read `true`, then one step
right: both heads end at cursor `1`. -/
def rewind : Machine 2 (2 + (2 + 2)) :=
  Composition.machine (oneStep 2 (fun _ => (fun _ => none, fun _ => .left)))
    (Composition.machine (whileM 2 0 (fun _ => .left)) (oneStep 2 (fun _ => (fun _ => none, fun _ => .right))))

theorem rewind_lruns (W n p : ℕ) (f : ℕ → Bool) (hp1 : 1 ≤ p) (hp : p ≤ n + 1) :
    LRuns W rewind (p + 4) ![.cells (sf (List.replicate n true)) p, .cells f p]
      ![.cells (sf (List.replicate n true)) 1, .cells f 1] := by
  intro H A hA
  have h0 : H 0 = p ∧ ∀ j, readTapeBit (A 0) j = sf (List.replicate n true) j := hA 0
  have h1 : H 1 = p ∧ ∀ j, readTapeBit (A 1) j = f j := hA 1
  have eH : H = fun _ => p := by funext i; fin_cases i; exact h0.1; exact h1.1
  have s1 : Step (oneStep 2 (fun _ => (fun _ => none, fun _ => .left))) 1 H A (fun _ => p - 1) A :=
    (oneStep_run 2 (fun _ => (fun _ => none, fun _ => .left)) H A).congr
      (by funext i; rw [eH]; rfl) (by funext i; rfl)
  have s2 := whileM_run 2 0 (fun _ => .left) A (p - 1) (fun _ => p - 1)
    (by
      intro j hj
      simp only [iterH, iter_left]
      rw [h0.2]
      exact sf_marks_true n _ (by omega) (by omega))
    (by
      simp only [iterH, iter_left]
      rw [h0.2, show p - 1 - (p - 1) = 0 by omega]
      rfl)
  have eH2 : iterH (fun _ : Fin 2 => HeadMove.left) (p - 1) (fun _ => p - 1) = fun _ => 0 := by
    funext i
    change (fun h => HeadMove.left.apply h)^[p - 1] (p - 1) = 0
    rw [iter_left]; omega
  rw [eH2] at s2
  have s3 : Step (oneStep 2 (fun _ => (fun _ => none, fun _ => .right))) 1 (fun _ => 0) A (fun _ => 1) A :=
    (oneStep_run 2 (fun _ => (fun _ => none, fun _ => .right)) (fun _ => 0) A).congr
      (by funext i; rfl) (by funext i; rfl)
  have hall := s1.seq (s2.seq s3)
  refine ⟨_, _, hall.enlarge (by omega), ?_⟩
  intro i
  fin_cases i
  · exact ⟨rfl, h0.2⟩
  · exact ⟨rfl, h1.2⟩

/-! ## One-step instructions -/

/-- `flag := stream bit; advance` (tapes 0 marks, 1 stream, 2 flag). -/
def readBit : Machine 3 2 :=
  oneStep 3 (fun b => (![none, none, some (b 1)], ![.right, .right, .stay]))

theorem readBit_lruns (W p : ℕ) (f g : ℕ → Bool) (c : Bool) :
    LRuns W readBit 1 ![.cells g p, .cells f p, .flag c] ![.cells g (p + 1), .cells f (p + 1), .flag (f p)] := by
  intro H A hA
  have h0 : H 0 = p ∧ ∀ j, readTapeBit (A 0) j = g j := hA 0
  have h1 : H 1 = p ∧ ∀ j, readTapeBit (A 1) j = f j := hA 1
  have h2 : H 2 = 0 ∧ readTapeBit (A 2) 0 = c := hA 2
  refine ⟨_, _, oneStep_run 3 _ H A, ?_⟩
  intro i
  fin_cases i
  · exact ⟨by simp [HeadMove.apply, h0.1], h0.2⟩
  · exact ⟨by simp [HeadMove.apply, h1.1], h1.2⟩
  · refine ⟨by simp [HeadMove.apply, h2.1], ?_⟩
    simp only [acted]
    simp [h2.1, h1.1, read_write, h1.2]

/-- `flag := stream bit` without moving (tapes 0 stream, 1 flag). -/
def peek : Machine 2 2 :=
  oneStep 2 (fun b => (![none, some (b 0)], fun _ => .stay))

theorem peek_lruns (W p : ℕ) (f : ℕ → Bool) (c : Bool) :
    LRuns W peek 1 ![.cells f p, .flag c] ![.cells f p, .flag (f p)] := by
  intro H A hA
  have h0 : H 0 = p ∧ ∀ j, readTapeBit (A 0) j = f j := hA 0
  have h1 : H 1 = 0 ∧ readTapeBit (A 1) 0 = c := hA 1
  refine ⟨_, _, oneStep_run 2 _ H A, ?_⟩
  intro i
  fin_cases i
  · exact ⟨by simp [HeadMove.apply, h0.1], h0.2⟩
  · refine ⟨by simp [HeadMove.apply, h1.1], ?_⟩
    simp only [acted]
    simp [h1.1, h0.1, read_write, h0.2]

/-- Append one `true` to the unary output (tape 0). -/
def append : Machine 1 2 :=
  oneStep 1 (fun _ => (fun _ => some true, fun _ => .right))

theorem append_lruns (W n : ℕ) : LRuns W append 1 ![.out n] ![.out (n + 1)] := by
  intro H A hA
  have h0 : H 0 = n ∧ A 0 = List.replicate n true := hA 0
  refine ⟨_, _, oneStep_run 1 _ H A, ?_⟩
  intro i
  fin_cases i
  refine ⟨by simp [HeadMove.apply, h0.1], ?_⟩
  simp only [acted]
  simp [h0.1, h0.2, write_end_replicate, List.replicate_succ']

/-- Move one tape right. -/
def moveR : Machine 1 2 :=
  oneStep 1 (fun _ => (fun _ => none, fun _ => .right))

theorem moveR_lruns (W h : ℕ) (f : ℕ → Bool) : LRuns W moveR 1 ![.cells f h] ![.cells f (h + 1)] := by
  intro H A hA
  have h0 : H 0 = h ∧ ∀ j, readTapeBit (A 0) j = f j := hA 0
  refine ⟨_, _, oneStep_run 1 _ H A, ?_⟩
  intro i
  fin_cases i
  exact ⟨by simp [HeadMove.apply, h0.1], h0.2⟩

end
end NearCubicWires.PacketsMeta

