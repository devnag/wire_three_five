import Proof.Packets.PacketsMetaReadNat

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

/-! ## The frame encoding -/

theorem frame_getD_even (w : List Bool) : ∀ k, (RepairOrdinary.frame w).getD (2 * k) false = decide (k < w.length) := by
  induction w with
  | nil => intro k; cases k <;> simp [RepairOrdinary.frame]
  | cons b w ih =>
    intro k
    cases k with
    | zero => simp [RepairOrdinary.frame]
    | succ k =>
      rw [show 2 * (k + 1) = (2 * k) + 1 + 1 by omega]
      simp only [RepairOrdinary.frame, List.getD_cons_succ]
      rw [ih k]
      simp

theorem frame_getD_odd (w : List Bool) : ∀ k, k < w.length →
    (RepairOrdinary.frame w).getD (2 * k + 1) false = w.getD k false := by
  induction w with
  | nil => intro k hk; simp at hk
  | cons b w ih =>
    intro k hk
    cases k with
    | zero => simp [RepairOrdinary.frame]
    | succ k =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by omega]
      simp only [RepairOrdinary.frame, List.getD_cons_succ]
      exact ih k (by simp at hk; omega)

/-! ## Stream contents, explicitly -/

theorem sf_eq (w : List Bool) (j : ℕ) : sf w j = if 1 ≤ j ∧ j ≤ w.length then w.getD (j - 1) false else false := by
  rcases j with _ | j
  · rfl
  · rw [sf_succ]
    split_ifs with h
    · rfl
    · exact List.getD_eq_default w false (by omega)

theorem sf_rep (n j : ℕ) : sf (List.replicate n true) j = decide (1 ≤ j ∧ j ≤ n) := by
  rw [sf_eq]
  simp only [List.length_replicate]
  split_ifs with h
  · rw [List.getD_eq_getElem (List.replicate n true) false (by simp; omega), List.getElem_replicate]
    simp [h]
  · exact (decide_eq_false h).symm

theorem dec_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q :=
  decide_eq_decide.mpr h

theorem sf_take (w : List Bool) (k j : ℕ) : sf (w.take k) j = if j ≤ k then sf w j else false := by
  rw [sf_eq, sf_eq]
  simp only [List.length_take]
  by_cases h1 : 1 ≤ j ∧ j ≤ min k w.length
  · rw [if_pos h1, if_pos (by omega), if_pos (by omega)]
    rw [List.getD_eq_getElem (w.take k) false (by simp; omega), List.getElem_take,
      List.getD_eq_getElem w false (by omega)]
  · rw [if_neg h1]
    split_ifs with h2 h3 <;> first | rfl | (exfalso; omega)

/-! ## Unframe -/

namespace Unframe

/-- Tapes: 0 source, 1 stream, 2 marks. -/
def copy : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q b =>
    if q.val = 0 then some ⟨1, fun _ => none, ![.stay, .right, .right]⟩
    else if q.val = 1 then
      (if b 0 then some ⟨2, fun _ => none, ![.right, .stay, .stay]⟩
       else some ⟨3, fun _ => none, ![.right, .stay, .stay]⟩)
    else if q.val = 2 then some ⟨1, ![none, some (b 0), some true], ![.right, .right, .right]⟩
    else none

def cfg (q : Fin 4) (hx hs : ℕ) (X S M : List Bool) : Configuration 3 4 := ⟨q, ![hx, hs, hs], ![X, S, M]⟩

theorem s0 (X S M : List Bool) (hx : ℕ) : step copy (cfg 0 hx 0 X S M) = some (cfg 1 hx 1 X S M) := by
  simp [step, copy, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s1t (X S M : List Bool) (hx hs : ℕ) (h : readTapeBit X hx = true) :
    step copy (cfg 1 hx hs X S M) = some (cfg 2 (hx + 1) hs X S M) := by
  simp [step, copy, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s1f (X S M : List Bool) (hx hs : ℕ) (h : readTapeBit X hx = false) :
    step copy (cfg 1 hx hs X S M) = some (cfg 3 (hx + 1) hs X S M) := by
  simp [step, copy, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s2 (X S M : List Bool) (hx hs : ℕ) :
    step copy (cfg 2 hx hs X S M) =
      some (cfg 1 (hx + 1) (hs + 1) X (writeTapeBit S hs (readTapeBit X hx)) (writeTapeBit M hs true)) := by
  simp [step, copy, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem loop (X : List Bool) (h : ℕ) (w : List Bool)
    (hX : ∀ i, i < (RepairOrdinary.frame w).length → readTapeBit X (h + i) = (RepairOrdinary.frame w).getD i false)
    (S M : List Bool) (hS : ∀ j, readTapeBit S j = false) (hM : ∀ j, readTapeBit M j = false) :
    ∀ k, k ≤ w.length → ∃ S' M', (∀ j, readTapeBit S' j = sf (w.take k) j) ∧
      (∀ j, readTapeBit M' j = sf (List.replicate k true) j) ∧
      Timed copy (2 * k) (cfg 1 h 1 X S M) (cfg 1 (h + 2 * k) (1 + k) X S' M') := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨S, M, fun j => ?_, fun j => ?_, Timed.refl _ _⟩
    · rw [hS]; cases j <;> simp [sf, readTapeBit]
    · rw [hM]; cases j <;> simp [sf, readTapeBit]
  | succ k ih =>
    intro hk
    obtain ⟨S', M', hS', hM', t⟩ := ih (by omega)
    have hlen := RepairOrdinary.frame_length w
    have hm : readTapeBit X (h + 2 * k) = true := by
      rw [hX (2 * k) (by omega), frame_getD_even]; simp; omega
    have hb : readTapeBit X (h + 2 * k + 1) = w.getD k false := by
      rw [show h + 2 * k + 1 = h + (2 * k + 1) by omega, hX (2 * k + 1) (by omega), frame_getD_odd w k (by omega)]
    refine ⟨writeTapeBit S' (1 + k) (readTapeBit X (h + 2 * k + 1)), writeTapeBit M' (1 + k) true,
      fun j => ?_, fun j => ?_, ?_⟩
    · rw [read_write, hb, hS', sf_take, sf_take]
      split_ifs with hj h1 h2 h3 <;> first | rfl | (exfalso; omega) | skip
      · rw [sf_eq, if_pos (by omega)]; congr 1; omega
    · rw [read_write, hM', sf_rep, sf_rep]
      split_ifs with hj
      · exact (decide_eq_true (by omega)).symm
      · exact dec_congr (by omega)
    · have a1 := Timed.single (by rfl) (s1t X S' M' (h + 2 * k) (1 + k) hm)
      have a2 := Timed.single (by rfl) (s2 X S' M' (h + 2 * k + 1) (1 + k))
      have tt := (t.trans a1).trans a2
      rwa [show h + 2 * k + 1 + 1 = h + 2 * (k + 1) by omega, show 1 + k + 1 = 1 + (k + 1) by omega,
        show 2 * k + 1 + 1 = 2 * (k + 1) by omega] at tt

theorem copy_run (X : List Bool) (h : ℕ) (w : List Bool)
    (hX : ∀ i, i < (RepairOrdinary.frame w).length → readTapeBit X (h + i) = (RepairOrdinary.frame w).getD i false)
    (S M : List Bool) (hS : ∀ j, readTapeBit S j = false) (hM : ∀ j, readTapeBit M j = false) :
    ∃ S' M', (∀ j, readTapeBit S' j = sf w j) ∧ (∀ j, readTapeBit M' j = sf (List.replicate w.length true) j) ∧
      Step copy (2 * w.length + 3) ![h, 0, 0] ![X, S, M] ![h + 2 * w.length + 1, 1 + w.length, 1 + w.length]
        ![X, S', M'] := by
  obtain ⟨S', M', hS', hM', t⟩ := loop X h w hX S M hS hM w.length le_rfl
  rw [List.take_length] at hS'
  have hlen := RepairOrdinary.frame_length w
  have hend : readTapeBit X (h + 2 * w.length) = false := by
    rw [hX (2 * w.length) (by omega), frame_getD_even]; simp
  have a0 := Timed.single (by rfl) (s0 X S M h)
  have a1 := Timed.single (by rfl) (s1f X S' M' (h + 2 * w.length) (1 + w.length) hend)
  have tt := (a0.trans t).trans a1
  obtain ⟨r, hr, hf, _⟩ := tt.run (by rfl)
  refine ⟨S', M', hS', hM', ?_⟩
  have hs := Step.of_run (hin := ![h, 0, 0]) (tin := ![X, S, M])
    (hout := ![h + 2 * w.length + 1, 1 + w.length, 1 + w.length]) (tout := ![X, S', M']) hr
    (by rw [hf]; rfl) (by rw [hf]; rfl)
  exact hs.enlarge (by omega)

/-- Copy, then rewind the new stream to cursor `1`. -/
def machine := Composition.machine copy (RecoveryFocus.machine ![2, 1] rewind)

theorem lruns (W h : ℕ) (w : List Bool) (fx : ℕ → Bool)
    (hX : ∀ i, i < (RepairOrdinary.frame w).length → fx (h + i) = (RepairOrdinary.frame w).getD i false) :
    LRuns W machine (5 * w.length + 10) ![.cells fx h, .cells blank 0, .cells blank 0]
      ![.cells fx (h + (RepairOrdinary.frame w).length), .cells (sf w) 1,
        .cells (sf (List.replicate w.length true)) 1] := by
  have hlen := RepairOrdinary.frame_length w
  have hc : LRuns W copy (2 * w.length + 3) ![.cells fx h, .cells blank 0, .cells blank 0]
      ![.cells fx (h + (RepairOrdinary.frame w).length), .cells (sf w) (1 + w.length),
        .cells (sf (List.replicate w.length true)) (1 + w.length)] := by
    intro H A hA
    have h0 : H 0 = h ∧ ∀ j, readTapeBit (A 0) j = fx j := hA 0
    have h1 : H 1 = 0 ∧ ∀ j, readTapeBit (A 1) j = blank j := hA 1
    have h2 : H 2 = 0 ∧ ∀ j, readTapeBit (A 2) j = blank j := hA 2
    obtain ⟨S', M', hS', hM', hs⟩ := copy_run (A 0) h w (fun i hi => by rw [h0.2, hX i hi]) (A 1) (A 2)
      h1.2 h2.2
    have eH : (![h, 0, 0] : Fin 3 → ℕ) = H := by
      funext i; fin_cases i
      · exact h0.1.symm
      · exact h1.1.symm
      · exact h2.1.symm
    have eA : (![A 0, A 1, A 2] : Fin 3 → List Bool) = A := by funext i; fin_cases i <;> rfl
    refine ⟨_, _, hs.congr_in eH eA, ?_⟩
    intro i
    fin_cases i
    · exact ⟨by simp [hlen]; omega, h0.2⟩
    · exact ⟨rfl, hS'⟩
    · exact ⟨rfl, hM'⟩
  have hr := (rewind_lruns W w.length (1 + w.length) (sf w) (by omega) (by omega)).dockK ![2, 1]
    (by decide) ![.cells fx (h + (RepairOrdinary.frame w).length), .cells (sf w) (1 + w.length),
        .cells (sf (List.replicate w.length true)) (1 + w.length)]
    (by intro j; fin_cases j <;> rfl) [0, 1] (by intro j hj; fin_cases j <;> simp at hj)
  have e : ([0, 1] : List (Fin 2)).foldr (fun k ρ => Function.update ρ ((![2, 1] : Fin 2 → Fin 3) k)
      ((![.cells (sf (List.replicate w.length true)) 1, .cells (sf w) 1] : Fin 2 → TS) k))
      (![.cells fx (h + (RepairOrdinary.frame w).length), .cells (sf w) (1 + w.length),
        .cells (sf (List.replicate w.length true)) (1 + w.length)] : Fin 3 → TS) =
      ![.cells fx (h + (RepairOrdinary.frame w).length), .cells (sf w) 1,
        .cells (sf (List.replicate w.length true)) 1] := by
    funext i; fin_cases i <;> rfl
  rw [e] at hr
  exact (hc.seq hr).enlarge (by omega)

end Unframe

/-! ## The ruler -/

namespace Ruler

/-- Tapes: 0 marks, 1 stream, 2 ruler. States `0` test, `1..k` write (the last also advances the
stream), `k+1` halt. -/
def build (k : ℕ) : Machine 3 (k + 2) where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == k + 1
  rule := fun q b =>
    if q.val = 0 then
      (if b 0 then some ⟨⟨1, by omega⟩, fun _ => none, fun _ => .stay⟩
       else some ⟨⟨k + 1, by omega⟩, fun _ => none, fun _ => .stay⟩)
    else if h : q.val < k then some ⟨⟨q.val + 1, by omega⟩, ![none, none, some true], ![.stay, .stay, .right]⟩
    else if q.val = k then some ⟨⟨0, by omega⟩, ![none, none, some true], ![.right, .right, .right]⟩
    else none

def cfg (k : ℕ) (q : Fin (k + 2)) (hm hr : ℕ) (M S R : List Bool) : Configuration 3 (k + 2) :=
  ⟨q, ![hm, hm, hr], ![M, S, R]⟩

theorem chain (k : ℕ) (hk : 1 ≤ k) (M S : List Bool) (hm : ℕ) :
    ∀ d i (R : List Bool) (hr : ℕ) (hi : 1 ≤ i) (hid : i + d = k),
      ∃ R', (∀ j, readTapeBit R' j = if hr ≤ j ∧ j ≤ hr + d then true else readTapeBit R j) ∧
        Timed (build k) (d + 1) (cfg k ⟨i, by omega⟩ hm hr M S R) (cfg k 0 (hm + 1) (hr + d + 1) M S R') := by
  intro d
  induction d with
  | zero =>
    intro i R hr hi hid
    refine ⟨writeTapeBit R hr true, fun j => ?_, ?_⟩
    · rw [read_write]; split_ifs <;> first | rfl | (exfalso; omega)
    · have hik : k = i := by omega
      subst hik
      refine Timed.single (by simp [build, cfg]; try omega) ?_
      simp [step, build, cfg, Configuration.scanned, show k ≠ 0 by omega]
      apply configuration_ext
      · rfl
      · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
      · funext j; fin_cases j <;> simp [applyAction]
  | succ d ih =>
    intro i R hr hi hid
    obtain ⟨R', hR', t⟩ := ih (i + 1) (writeTapeBit R hr true) (hr + 1) (by omega) (by omega)
    refine ⟨R', fun j => ?_, ?_⟩
    · rw [hR', read_write]; split_ifs <;> first | rfl | (exfalso; omega)
    · have hs : step (build k) (cfg k ⟨i, by omega⟩ hm hr M S R) =
          some (cfg k ⟨i + 1, by omega⟩ hm (hr + 1) M S (writeTapeBit R hr true)) := by
        have hlt : i < k := by omega
        simp [step, build, cfg, Configuration.scanned, hlt, show i ≠ 0 by omega]
        apply configuration_ext
        · rfl
        · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
        · funext j; fin_cases j <;> simp [applyAction]
      have tt := (Timed.single (by simp [build, cfg]; try omega) hs).trans t
      rwa [show hr + 1 + d + 1 = hr + (d + 1) + 1 by omega, show 1 + (d + 1) = d + 1 + 1 by omega] at tt

/-- The contents of a ruler under construction: cells `1..P-1` set. -/
def rb (P : ℕ) : ℕ → Bool := fun j => decide (1 ≤ j ∧ j < P)

theorem build_loop (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (M S : List Bool)
    (hM : ∀ j, readTapeBit M j = sf (List.replicate n true) j) :
    ∀ c, c ≤ n → ∀ (P : ℕ) (R : List Bool), 1 ≤ P → (∀ j, readTapeBit R j = rb P j) →
      ∃ R', (∀ j, readTapeBit R' j = rb (P + k * c) j) ∧
        Timed (build k) ((k + 1) * c) (cfg k 0 (n + 1 - c) P M S R) (cfg k 0 (n + 1) (P + k * c) M S R') := by
  intro c
  induction c with
  | zero => intro _ P R _ hR; exact ⟨R, by simpa using hR, by simpa using Timed.refl _ _⟩
  | succ c ih =>
    intro hc P R hP hR
    have hpos : n + 1 - (c + 1) = n - c := by omega
    have hmk : readTapeBit M (n - c) = true := by
      rw [hM, sf_rep]; simp; omega
    have a1 : Timed (build k) 1 (cfg k 0 (n - c) P M S R) (cfg k ⟨1, by omega⟩ (n - c) P M S R) := by
      refine Timed.single (by simp [build, cfg]) ?_
      simp [step, build, cfg, Configuration.scanned, hmk]
      apply configuration_ext
      · rfl
      · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
      · funext j; fin_cases j <;> simp [applyAction]
    obtain ⟨R1, hR1, t1⟩ := chain k hk M S (n - c) (k - 1) 1 R P le_rfl (by omega)
    rw [show n - c + 1 = n + 1 - c by omega, show P + (k - 1) + 1 = P + k by omega] at t1
    obtain ⟨R2, hR2, t2⟩ := ih (by omega) (P + k) R1 (by omega) (fun j => by
      rw [hR1, hR]; unfold rb
      split_ifs with h
      · exact (decide_eq_true (by omega)).symm
      · exact dec_congr (by omega))
    refine ⟨R2, fun j => by rw [hR2, show P + k + k * c = P + k * (c + 1) by ring], ?_⟩
    have tt := (a1.trans t1).trans t2
    rw [hpos]
    rwa [show 1 + (k - 1 + 1) + (k + 1) * c = (k + 1) * (c + 1) by
        rw [show k - 1 + 1 = k by omega]; ring,
      show P + k + k * c = P + k * (c + 1) by ring] at tt

theorem build_run (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (M S R : List Bool)
    (hM : ∀ j, readTapeBit M j = sf (List.replicate n true) j) (P : ℕ) (hP : 1 ≤ P)
    (hR : ∀ j, readTapeBit R j = rb P j) :
    ∃ R', (∀ j, readTapeBit R' j = rb (P + k * n) j) ∧
      Step (build k) ((k + 1) * n + 1) ![1, 1, P] ![M, S, R] ![n + 1, n + 1, P + k * n] ![M, S, R'] := by
  obtain ⟨R', hR', t⟩ := build_loop k hk n M S hM n le_rfl P R hP hR
  rw [show n + 1 - n = 1 by omega] at t
  have hend : readTapeBit M (n + 1) = false := by rw [hM, sf_rep]; simp
  have a : Timed (build k) 1 (cfg k 0 (n + 1) (P + k * n) M S R')
      (cfg k ⟨k + 1, by omega⟩ (n + 1) (P + k * n) M S R') := by
    refine Timed.single (by simp [build, cfg]) ?_
    simp [step, build, cfg, Configuration.scanned, hend]
    apply configuration_ext
    · rfl
    · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
    · funext j; fin_cases j <;> simp [applyAction]
  obtain ⟨r, hr, hf, _⟩ := (t.trans a).run (by simp [build, cfg])
  exact ⟨R', hR', Step.of_run (hin := ![1, 1, P]) (tin := ![M, S, R]) hr (by rw [hf]; rfl) (by rw [hf]; rfl)⟩

/-- Build, then rewind the stream (tapes 0 marks, 1 stream, 2 ruler). -/
def append (k : ℕ) := Composition.machine (build k) (RecoveryFocus.machine ![0, 1] rewind)

theorem append_lruns (W k : ℕ) (hk : 1 ≤ k) (n P : ℕ) (hP : 1 ≤ P) (f : ℕ → Bool) :
    LRuns W (append k) ((k + 1) * n + n + 7)
      ![.cells (sf (List.replicate n true)) 1, .cells f 1, .cells (rb P) P]
      ![.cells (sf (List.replicate n true)) 1, .cells f 1, .cells (rb (P + k * n)) (P + k * n)] := by
  have hb : LRuns W (build k) ((k + 1) * n + 1)
      ![.cells (sf (List.replicate n true)) 1, .cells f 1, .cells (rb P) P]
      ![.cells (sf (List.replicate n true)) (n + 1), .cells f (n + 1), .cells (rb (P + k * n)) (P + k * n)] := by
    intro H A hA
    have h0 : H 0 = 1 ∧ ∀ j, readTapeBit (A 0) j = sf (List.replicate n true) j := hA 0
    have h1 : H 1 = 1 ∧ ∀ j, readTapeBit (A 1) j = f j := hA 1
    have h2 : H 2 = P ∧ ∀ j, readTapeBit (A 2) j = rb P j := hA 2
    obtain ⟨R', hR', hs⟩ := build_run k hk n (A 0) (A 1) (A 2) h0.2 P hP h2.2
    have eH : (![1, 1, P] : Fin 3 → ℕ) = H := by
      funext i; fin_cases i
      · exact h0.1.symm
      · exact h1.1.symm
      · exact h2.1.symm
    have eA : (![A 0, A 1, A 2] : Fin 3 → List Bool) = A := by funext i; fin_cases i <;> rfl
    refine ⟨_, _, hs.congr_in eH eA, ?_⟩
    intro i
    fin_cases i
    · exact ⟨rfl, h0.2⟩
    · exact ⟨rfl, h1.2⟩
    · exact ⟨rfl, hR'⟩
  have hr := (rewind_lruns W n (n + 1) f (by omega) le_rfl).dockK ![0, 1] (by decide)
    ![.cells (sf (List.replicate n true)) (n + 1), .cells f (n + 1), .cells (rb (P + k * n)) (P + k * n)]
    (by intro j; fin_cases j <;> rfl) [0, 1] (by intro j hj; fin_cases j <;> simp at hj)
  have e : ([0, 1] : List (Fin 2)).foldr (fun j ρ => Function.update ρ ((![0, 1] : Fin 2 → Fin 3) j)
      ((![.cells (sf (List.replicate n true)) 1, .cells f 1] : Fin 2 → TS) j))
      (![.cells (sf (List.replicate n true)) (n + 1), .cells f (n + 1), .cells (rb (P + k * n)) (P + k * n)] :
        Fin 3 → TS) =
      ![.cells (sf (List.replicate n true)) 1, .cells f 1, .cells (rb (P + k * n)) (P + k * n)] := by
    funext i; fin_cases i <;> rfl
  rw [e] at hr
  exact (hb.seq hr).enlarge (by omega)

/-- Rewind the finished ruler: one step left, then left while set. -/
def finish :=
  Composition.machine (oneStep 1 (fun _ => (fun _ => none, fun _ => .left))) (whileM 1 0 (fun _ => .left))

theorem finish_lruns (W : ℕ) : LRuns W finish (W + 3) ![.cells (rb (W + 1)) (W + 1)] ![.ruler] := by
  intro H A hA
  have h0 : H 0 = W + 1 ∧ ∀ j, readTapeBit (A 0) j = rb (W + 1) j := hA 0
  have s1 : Step (oneStep 1 (fun _ => (fun _ => none, fun _ => .left))) 1 H A (fun _ => W) A :=
    (oneStep_run 1 (fun _ => (fun _ => none, fun _ => .left)) H A).congr
      (by funext i; fin_cases i; simp [HeadMove.apply, h0.1]) (by funext i; rfl)
  have s2 := whileM_run 1 0 (fun _ => .left) A W (fun _ => W)
    (by
      intro j hj
      change readTapeBit (A 0) ((fun h => HeadMove.left.apply h)^[j] W) = true
      rw [iter_left, h0.2]; unfold rb; simp; omega)
    (by
      change readTapeBit (A 0) ((fun h => HeadMove.left.apply h)^[W] W) = false
      rw [iter_left, h0.2]; unfold rb; simp)
  have eH : iterH (fun _ : Fin 1 => HeadMove.left) W (fun _ => W) = fun _ => 0 := by
    funext i
    change (fun h => HeadMove.left.apply h)^[W] W = 0
    rw [iter_left]; omega
  rw [eH] at s2
  refine ⟨_, _, (s1.seq s2).enlarge (by omega), ?_⟩
  intro i
  fin_cases i
  change TR W .ruler 0 (A 0)
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [h0.2]; unfold rb; simp
  · intro j hj1 hjW; rw [h0.2]; unfold rb; simp; omega
  · rw [h0.2]; unfold rb; simp

end Ruler

/-! ## A fixed word as a fresh stream -/

theorem sf_out (w : List Bool) (j : ℕ) (h : w.length + 1 ≤ j) : sf w j = false := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [sf_succ, List.getD_eq_default _ _ (by omega)]

namespace Word

/-- Tapes: 0 stream, 1 marks. State `0` steps right; state `i+1` (`i < |u|`) writes `u[i]`; `|u|+1` halts. -/
def write (u : List Bool) : Machine 2 (u.length + 2) where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == u.length + 1
  rule := fun q _ =>
    if q.val = 0 then some ⟨⟨1, by omega⟩, fun _ => none, fun _ => .right⟩
    else if h : q.val ≤ u.length then
      some ⟨⟨q.val + 1, by omega⟩, ![some (u.getD (q.val - 1) false), some true], fun _ => .right⟩
    else none

def cfg (u : List Bool) (q : Fin (u.length + 2)) (h : ℕ) (S M : List Bool) : Configuration 2 (u.length + 2) :=
  ⟨q, fun _ => h, ![S, M]⟩

theorem chain (u : List Bool) : ∀ d i (S M : List Bool) (hid : i + d = u.length)
    (hS : ∀ j, i + 1 ≤ j → readTapeBit S j = false) (hM : ∀ j, i + 1 ≤ j → readTapeBit M j = false),
    ∃ S' M', (∀ j, readTapeBit S' j = if i + 1 ≤ j then sf u j else readTapeBit S j) ∧
      (∀ j, readTapeBit M' j = if i + 1 ≤ j then sf (List.replicate u.length true) j else readTapeBit M j) ∧
      Timed (write u) d (cfg u ⟨i + 1, by omega⟩ (i + 1) S M) (cfg u ⟨u.length + 1, by omega⟩ (u.length + 1) S' M') := by
  intro d
  induction d with
  | zero =>
    intro i S M hid hS hM
    have hi : i = u.length := by omega
    subst hi
    refine ⟨S, M, fun j => ?_, fun j => ?_, Timed.refl _ _⟩
    · split_ifs with h
      · rw [hS j h, sf_out u j h]
      · rfl
    · split_ifs with h
      · rw [hM j h, sf_out _ j (by simp; omega)]
      · rfl
  | succ d ih =>
    intro i S M hid hS hM
    have hs : step (write u) (cfg u ⟨i + 1, by omega⟩ (i + 1) S M) =
        some (cfg u ⟨i + 2, by omega⟩ (i + 2) (writeTapeBit S (i + 1) (u.getD i false))
          (writeTapeBit M (i + 1) true)) := by
      have hle : i + 1 ≤ u.length := by omega
      simp [step, write, cfg, Configuration.scanned, hle]
      apply configuration_ext
      · rfl
      · funext j; simp [applyAction, HeadMove.apply]
      · funext j; fin_cases j <;> simp [applyAction]
    obtain ⟨S', M', hS', hM', t⟩ := ih (i + 1) (writeTapeBit S (i + 1) (u.getD i false))
      (writeTapeBit M (i + 1) true) (by omega)
      (fun j hj => by rw [read_write, if_neg (by omega)]; exact hS j (by omega))
      (fun j hj => by rw [read_write, if_neg (by omega)]; exact hM j (by omega))
    refine ⟨S', M', fun j => ?_, fun j => ?_, ?_⟩
    · rw [hS']
      split_ifs with h1 h2
      · rfl
      · exfalso; omega
      · rw [read_write, if_pos (by omega), show j = i + 1 by omega, sf_succ]
      · rw [read_write, if_neg (by omega)]
    · rw [hM']
      split_ifs with h1 h2
      · rfl
      · exfalso; omega
      · rw [read_write, if_pos (by omega), show j = i + 1 by omega]
        exact (sf_marks_true u.length (i + 1) (by omega) (by omega)).symm
      · rw [read_write, if_neg (by omega)]
    · have tt := (Timed.single (by simp [write, cfg]; omega) hs).trans t
      rwa [show 1 + d = d + 1 by omega] at tt

theorem write_run (u : List Bool) (S M : List Bool) (hS : ∀ j, readTapeBit S j = false)
    (hM : ∀ j, readTapeBit M j = false) :
    ∃ S' M', (∀ j, readTapeBit S' j = sf u j) ∧ (∀ j, readTapeBit M' j = sf (List.replicate u.length true) j) ∧
      Step (write u) (u.length + 1) (fun _ => 0) ![S, M] (fun _ => u.length + 1) ![S', M'] := by
  have a0 : Timed (write u) 1 (cfg u 0 0 S M) (cfg u ⟨0 + 1, by omega⟩ (0 + 1) S M) := by
    refine Timed.single (by simp [write, cfg]) ?_
    simp [step, write, cfg, Configuration.scanned]
    apply configuration_ext
    · rfl
    · funext j; simp [applyAction, HeadMove.apply]
    · funext j; fin_cases j <;> simp [applyAction]
  obtain ⟨S', M', hS', hM', t⟩ := chain u u.length 0 S M (by omega) (fun j _ => hS j) (fun j _ => hM j)
  refine ⟨S', M', fun j => ?_, fun j => ?_, ?_⟩
  · rw [hS']; split_ifs with h
    · rfl
    · rw [hS, show j = 0 by omega]; rfl
  · rw [hM']; split_ifs with h
    · rfl
    · rw [hM, show j = 0 by omega]; rfl
  · obtain ⟨r, hr, hf, _⟩ := (a0.trans t).run (by simp [write, cfg])
    exact (Step.of_run (hin := fun _ => 0) (tin := ![S, M]) hr (by rw [hf]; rfl) (by rw [hf]; rfl)).enlarge
      (by omega)

/-- Write `u`, then rewind (tapes 0 stream, 1 marks). -/
def machine (u : List Bool) := Composition.machine (write u) (RecoveryFocus.machine ![1, 0] rewind)

theorem lruns (W : ℕ) (u : List Bool) :
    LRuns W (machine u) (2 * u.length + 7) ![.cells blank 0, .cells blank 0]
      ![.cells (sf u) 1, .cells (sf (List.replicate u.length true)) 1] := by
  have hw : LRuns W (write u) (u.length + 1) ![.cells blank 0, .cells blank 0]
      ![.cells (sf u) (u.length + 1), .cells (sf (List.replicate u.length true)) (u.length + 1)] := by
    intro H A hA
    have h0 : H 0 = 0 ∧ ∀ j, readTapeBit (A 0) j = blank j := hA 0
    have h1 : H 1 = 0 ∧ ∀ j, readTapeBit (A 1) j = blank j := hA 1
    obtain ⟨S', M', hS', hM', hs⟩ := write_run u (A 0) (A 1) h0.2 h1.2
    have eH : (fun _ => 0 : Fin 2 → ℕ) = H := by
      funext i; fin_cases i
      · exact h0.1.symm
      · exact h1.1.symm
    have eA : (![A 0, A 1] : Fin 2 → List Bool) = A := by funext i; fin_cases i <;> rfl
    refine ⟨_, _, hs.congr_in eH eA, ?_⟩
    intro i
    fin_cases i
    · exact ⟨rfl, hS'⟩
    · exact ⟨rfl, hM'⟩
  have hr := (rewind_lruns W u.length (u.length + 1) (sf u) (by omega) le_rfl).dockK ![1, 0] (by decide)
    ![.cells (sf u) (u.length + 1), .cells (sf (List.replicate u.length true)) (u.length + 1)]
    (by intro j; fin_cases j <;> rfl) [0, 1] (by intro j hj; fin_cases j <;> simp at hj)
  have e : ([0, 1] : List (Fin 2)).foldr (fun j ρ => Function.update ρ ((![1, 0] : Fin 2 → Fin 2) j)
      ((![.cells (sf (List.replicate u.length true)) 1, .cells (sf u) 1] : Fin 2 → TS) j))
      (![.cells (sf u) (u.length + 1), .cells (sf (List.replicate u.length true)) (u.length + 1)] : Fin 2 → TS) =
      ![.cells (sf u) 1, .cells (sf (List.replicate u.length true)) 1] := by
    funext i; fin_cases i <;> rfl
  rw [e] at hr
  exact (hw.seq hr).enlarge (by omega)

end Word

end
end NearCubicWires.PacketsMeta

