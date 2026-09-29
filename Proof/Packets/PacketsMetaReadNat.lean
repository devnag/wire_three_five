import Proof.Packets.PacketsMetaStream
import Proof.Foundations.RepresentationSourceContracts

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
open NearCubicWires.RepairRepresentation
noncomputable section

namespace ReadNat

def machine : Machine 5 6 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 5
  rule := fun q b =>
    if q.val = 0 then some ⟨1, fun _ => none, ![.right, .stay, .stay, .right, .right]⟩
    else if q.val = 1 then
      (if b 1 then some ⟨1, ![none, none, none, some true, none], ![.stay, .right, .right, .right, .stay]⟩
       else some ⟨2, fun _ => none, ![.stay, .right, .right, .left, .stay]⟩)
    else if q.val = 2 then
      (if b 3 then some ⟨2, ![none, none, none, some false, some (b 1)], ![.right, .right, .right, .left, .right]⟩
       else some ⟨3, fun _ => none, fun _ => .stay⟩)
    else if q.val = 3 then
      (if b 0 then some ⟨3, ![none, none, none, none, some false], ![.right, .stay, .stay, .stay, .right]⟩
       else some ⟨4, fun _ => none, ![.left, .stay, .stay, .stay, .left]⟩)
    else if q.val = 4 then
      (if b 0 then some ⟨4, fun _ => none, ![.left, .stay, .stay, .stay, .left]⟩
       else some ⟨5, fun _ => none, fun _ => .stay⟩)
    else none

/-- Ruler and register heads together (`hr`), stream and marks together (`hs`), counter `hu`. -/
def cfg (q : Fin 6) (hr hs hu : ℕ) (Rl S M U R : List Bool) : Configuration 5 6 :=
  ⟨q, ![hr, hs, hs, hu, hr], ![Rl, S, M, U, R]⟩

theorem s0 (Rl S M U R : List Bool) (p : ℕ) :
    step machine (cfg 0 0 p 0 Rl S M U R) = some (cfg 1 1 p 1 Rl S M U R) := by
  simp [step, machine, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s1t (Rl S M U R : List Bool) (hr hs hu : ℕ) (h : readTapeBit S hs = true) :
    step machine (cfg 1 hr hs hu Rl S M U R) = some (cfg 1 hr (hs + 1) (hu + 1) Rl S M (writeTapeBit U hu true) R) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s1f (Rl S M U R : List Bool) (hr hs hu : ℕ) (h : readTapeBit S hs = false) :
    step machine (cfg 1 hr hs hu Rl S M U R) = some (cfg 2 hr (hs + 1) (hu - 1) Rl S M U R) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s2t (Rl S M U R : List Bool) (hr hs hu : ℕ) (h : readTapeBit U hu = true) :
    step machine (cfg 2 hr hs hu Rl S M U R) =
      some (cfg 2 (hr + 1) (hs + 1) (hu - 1) Rl S M (writeTapeBit U hu false)
        (writeTapeBit R hr (readTapeBit S hs))) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s2f (Rl S M U R : List Bool) (hr hs hu : ℕ) (h : readTapeBit U hu = false) :
    step machine (cfg 2 hr hs hu Rl S M U R) = some (cfg 3 hr hs hu Rl S M U R) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s3t (Rl S M U R : List Bool) (hr hs hu : ℕ) (h : readTapeBit Rl hr = true) :
    step machine (cfg 3 hr hs hu Rl S M U R) = some (cfg 3 (hr + 1) hs hu Rl S M U (writeTapeBit R hr false)) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s3f (Rl S M U R : List Bool) (hr hs hu : ℕ) (h : readTapeBit Rl hr = false) :
    step machine (cfg 3 hr hs hu Rl S M U R) = some (cfg 4 (hr - 1) hs hu Rl S M U R) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s4t (Rl S M U R : List Bool) (hr hs hu : ℕ) (h : readTapeBit Rl hr = true) :
    step machine (cfg 4 hr hs hu Rl S M U R) = some (cfg 4 (hr - 1) hs hu Rl S M U R) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s4f (Rl S M U R : List Bool) (hr hs hu : ℕ) (h : readTapeBit Rl hr = false) :
    step machine (cfg 4 hr hs hu Rl S M U R) = some (cfg 5 hr hs hu Rl S M U R) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem nh1 : machine.halted 1 = false := rfl
theorem nh2 : machine.halted 2 = false := rfl
theorem nh3 : machine.halted 3 = false := rfl
theorem nh4 : machine.halted 4 = false := rfl

/-- Phase 1: the leading ones are counted onto the unary tape. -/
theorem phase1 (Rl S M U R : List Bool) (p ℓ : ℕ) (hS : ∀ i, i < ℓ → readTapeBit S (p + i) = true)
    (hU : ∀ j, readTapeBit U j = false) :
    ∀ k, k ≤ ℓ → ∃ U', (∀ j, readTapeBit U' j = decide (1 ≤ j ∧ j ≤ k)) ∧
      Timed machine k (cfg 1 1 p 1 Rl S M U R) (cfg 1 1 (p + k) (1 + k) Rl S M U' R) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨U, fun j => by rw [hU]; simp; omega, ?_⟩
    exact Timed.refl _ _
  | succ k ih =>
    intro hk
    obtain ⟨U', hU', t⟩ := ih (by omega)
    refine ⟨writeTapeBit U' (1 + k) true, fun j => ?_, ?_⟩
    · rw [read_write]
      split_ifs with h
      · simp; omega
      · rw [hU']; simp only [decide_eq_decide]; omega
    · have s := Timed.single nh1 (s1t Rl S M U' R 1 (p + k) (1 + k) (hS k (by omega)))
      have tt := t.trans s
      rwa [show p + k + 1 = p + (k + 1) by omega, show 1 + k + 1 = 1 + (k + 1) by omega] at tt

/-- Phase 2: the bits are copied into the register while the counter is erased. -/
theorem phase2 (Rl S M R : List Bool) (p ℓ : ℕ) (x : ℕ)
    (hB : ∀ i, i < ℓ → readTapeBit S (p + ℓ + 1 + i) = x.testBit i) (U : List Bool)
    (hU : ∀ j, readTapeBit U j = decide (1 ≤ j ∧ j ≤ ℓ)) :
    ∀ k, k ≤ ℓ → ∃ U' R', (∀ j, readTapeBit U' j = decide (1 ≤ j ∧ j ≤ ℓ - k)) ∧
      (∀ j, readTapeBit R' j = if 1 ≤ j ∧ j ≤ k then x.testBit (j - 1) else readTapeBit R j) ∧
      Timed machine k (cfg 2 1 (p + ℓ + 1) ℓ Rl S M U R) (cfg 2 (1 + k) (p + ℓ + 1 + k) (ℓ - k) Rl S M U' R') := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨U, R, fun j => by rw [hU, Nat.sub_zero], fun j => by rw [if_neg (by omega)], ?_⟩
    exact Timed.refl _ _
  | succ k ih =>
    intro hk
    obtain ⟨U', R', hU', hR', t⟩ := ih (by omega)
    have hu : readTapeBit U' (ℓ - k) = true := by rw [hU']; simp; omega
    refine ⟨writeTapeBit U' (ℓ - k) false, writeTapeBit R' (1 + k) (readTapeBit S (p + ℓ + 1 + k)),
      fun j => ?_, fun j => ?_, ?_⟩
    · rw [read_write]
      split_ifs with h
      · simp; omega
      · rw [hU']; simp only [decide_eq_decide]; omega
    · rw [read_write]
      split_ifs with h h'
      · rw [hB k (by omega)]; congr 1; omega
      · exfalso; omega
      · rw [hR', if_pos (by omega)]
      · rw [hR']; rw [if_neg (by omega)]
    · have s := Timed.single nh2 (s2t Rl S M U' R' (1 + k) (p + ℓ + 1 + k) (ℓ - k) hu)
      have tt := t.trans s
      rwa [show 1 + k + 1 = 1 + (k + 1) by omega, show p + ℓ + 1 + k + 1 = p + ℓ + 1 + (k + 1) by omega,
        show ℓ - k - 1 = ℓ - (k + 1) by omega] at tt

/-- Phase 3: the register cells above the number are cleared up to the ruler's end. -/
theorem phase3 (Rl S M U : List Bool) (hs hu ℓ W : ℕ)
    (hRl : ∀ j, 1 ≤ j → j ≤ W → readTapeBit Rl j = true) (R : List Bool) :
    ∀ k, ℓ + k ≤ W → ∃ R', (∀ j, readTapeBit R' j = if ℓ + 1 ≤ j ∧ j ≤ ℓ + k then false else readTapeBit R j) ∧
      Timed machine k (cfg 3 (1 + ℓ) hs hu Rl S M U R) (cfg 3 (1 + ℓ + k) hs hu Rl S M U R') := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨R, fun j => by rw [if_neg (by omega)], Timed.refl _ _⟩
  | succ k ih =>
    intro hk
    obtain ⟨R', hR', t⟩ := ih (by omega)
    refine ⟨writeTapeBit R' (1 + ℓ + k) false, fun j => ?_, ?_⟩
    · rw [read_write]
      split_ifs with h h'
      · rfl
      · exfalso; omega
      · rw [hR', if_pos (by omega)]
      · rw [hR', if_neg (by omega)]
    · have s := Timed.single nh3 (s3t Rl S M U R' (1 + ℓ + k) hs hu (hRl _ (by omega) (by omega)))
      have tt := t.trans s
      rwa [show 1 + ℓ + k + 1 = 1 + ℓ + (k + 1) by omega] at tt

/-- Phase 4: the ruler and register heads return to `0`. -/
theorem phase4 (Rl S M U R : List Bool) (hs hu W : ℕ) (hRl : ∀ j, 1 ≤ j → j ≤ W → readTapeBit Rl j = true) :
    ∀ k, k ≤ W → Timed machine k (cfg 4 W hs hu Rl S M U R) (cfg 4 (W - k) hs hu Rl S M U R) := by
  intro k
  induction k with
  | zero => intro _; exact Timed.refl _ _
  | succ k ih =>
    intro hk
    have s := Timed.single nh4 (s4t Rl S M U R (W - k) hs hu (hRl _ (by omega) (by omega)))
    have tt := (ih (by omega)).trans s
    rwa [show W - k - 1 = W - (k + 1) by omega] at tt

/-- **The run.** -/
theorem run (Rl S M U R : List Bool) (p ℓ x W : ℕ) (hℓ : ℓ ≤ W) (hx : x < 2 ^ ℓ)
    (hR0 : readTapeBit Rl 0 = false) (hRl : ∀ j, 1 ≤ j → j ≤ W → readTapeBit Rl j = true)
    (hRW : readTapeBit Rl (W + 1) = false)
    (hS1 : ∀ i, i < ℓ → readTapeBit S (p + i) = true) (hS2 : readTapeBit S (p + ℓ) = false)
    (hS3 : ∀ i, i < ℓ → readTapeBit S (p + ℓ + 1 + i) = x.testBit i) (hU : ∀ j, readTapeBit U j = false) :
    ∃ U' R', (∀ j, readTapeBit U' j = false) ∧ (∀ j, 1 ≤ j → j ≤ W → readTapeBit R' j = x.testBit (j - 1)) ∧
      Step machine (2 * W + ℓ + 5) ![0, p, p, 0, 0] ![Rl, S, M, U, R]
        ![0, p + 2 * ℓ + 1, p + 2 * ℓ + 1, 0, 0] ![Rl, S, M, U', R'] := by
  obtain ⟨U1, hU1, t1⟩ := phase1 Rl S M U R p ℓ hS1 hU ℓ le_rfl
  obtain ⟨U2, R2, hU2, hR2, t2⟩ := phase2 Rl S M R p ℓ x hS3 U1 hU1 ℓ le_rfl
  obtain ⟨R3, hR3, t3⟩ := phase3 Rl S M U2 (p + ℓ + 1 + ℓ) (ℓ - ℓ) ℓ W hRl R2 (W - ℓ) (by omega)
  have t4 := phase4 Rl S M U2 R3 (p + ℓ + 1 + ℓ) (ℓ - ℓ) W hRl W le_rfl
  have a0 := Timed.single (by rfl) (s0 Rl S M U R p)
  have a1 := Timed.single nh1 (s1f Rl S M U1 R 1 (p + ℓ) (1 + ℓ) hS2)
  rw [show 1 + ℓ - 1 = ℓ by omega, show p + ℓ + 1 = p + ℓ + 1 by rfl] at a1
  have hu0 : readTapeBit U2 (ℓ - ℓ) = false := by rw [hU2]; simp
  have a2 := Timed.single nh2 (s2f Rl S M U2 R2 (1 + ℓ) (p + ℓ + 1 + ℓ) (ℓ - ℓ) hu0)
  have a3 := Timed.single nh3 (s3f Rl S M U2 R3 (1 + ℓ + (W - ℓ)) (p + ℓ + 1 + ℓ) (ℓ - ℓ)
    (by rw [show 1 + ℓ + (W - ℓ) = W + 1 by omega]; exact hRW))
  rw [show 1 + ℓ + (W - ℓ) - 1 = W by omega] at a3
  have a4 := Timed.single nh4 (s4f Rl S M U2 R3 (W - W) (p + ℓ + 1 + ℓ) (ℓ - ℓ)
    (by rw [Nat.sub_self]; exact hR0))
  have tt := (((((((a0.trans t1).trans a1).trans t2).trans a2).trans t3).trans a3).trans t4).trans a4
  obtain ⟨r, hr, hf, _⟩ := tt.run (by rfl)
  refine ⟨U2, R3, fun j => by rw [hU2]; simp; omega, fun j hj1 hjW => ?_, ?_⟩
  · rw [hR3]
    split_ifs with h
    · have : ℓ ≤ j - 1 := by omega
      exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) this))).symm
    · rw [hR2, if_pos (by omega)]
  · have hs := Step.of_run (hin := ![0, p, p, 0, 0]) (tin := ![Rl, S, M, U, R])
      (hout := ![0, p + 2 * ℓ + 1, p + 2 * ℓ + 1, 0, 0]) (tout := ![Rl, S, M, U2, R3]) hr
      (by rw [hf]; simp only [cfg, Nat.sub_self]; funext j; fin_cases j <;> simp <;> omega)
      (by rw [hf]; rfl)
    exact hs.enlarge (by omega)

/-! ## The word `natWord x` and the role-level run -/

theorem natWord_length (x : ℕ) : (natWord x).length = 2 * natBitLength x + 1 := by
  simp [natWord, NearCubicWires.WilliamsPublishedForm.framedNatBits,
    NearCubicWires.WilliamsPublishedForm.fixedWidthNatBits]
  omega

theorem natWord_getD (x i : ℕ) :
    (natWord x).getD i false = if i < natBitLength x then true else if i = natBitLength x then false
      else x.testBit (i - natBitLength x - 1) := by
  unfold natWord NearCubicWires.WilliamsPublishedForm.framedNatBits
    NearCubicWires.WilliamsPublishedForm.fixedWidthNatBits
  set ℓ := natBitLength x
  rw [List.getD_eq_getElem?_getD]
  by_cases h1 : i < ℓ
  · rw [if_pos h1, List.getElem?_append_left (by simpa using h1)]
    simp [h1]
  · rw [if_neg h1, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate]
    by_cases h2 : i = ℓ
    · subst h2; simp
    · rw [if_neg h2]
      obtain ⟨k, hk⟩ : ∃ k, i - ℓ = k + 1 := ⟨i - ℓ - 1, by omega⟩
      rw [hk, List.getElem?_cons_succ]
      by_cases h3 : k < ℓ
      · rw [List.getElem?_ofFn]
        simp [h3]
        try (congr 1; omega)
      · rw [List.getElem?_eq_none (by simp; omega)]
        simp only [Option.getD_none]
        symm
        apply Nat.testBit_lt_two_pow
        have hx : x < 2 ^ ℓ := Nat.lt_pow_succ_log_self (by norm_num) x
        exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem lt_natBitLength (x : ℕ) : x < 2 ^ natBitLength x := Nat.lt_pow_succ_log_self (by norm_num) x

/-- **ReadNat on roles.** The stream (tape 1, with its marks on tape 2) reads `natWord x` from its
cursor `p`; the register (tape 4) ends holding `x`, the cursor moves past the word. -/
theorem lruns (W p x y : ℕ) (f g : ℕ → Bool) (hW : natBitLength x ≤ W)
    (hS : ∀ i, i < (natWord x).length → f (p + i) = (natWord x).getD i false) :
    LRuns W machine (3 * W + 5) ![.ruler, .cells f p, .cells g p, .cells blank 0, .reg y]
      ![.ruler, .cells f (p + (natWord x).length), .cells g (p + (natWord x).length), .cells blank 0,
        .reg x] := by
  intro H A hA
  have h0 : H 0 = 0 ∧ readTapeBit (A 0) 0 = false ∧ (∀ j, 1 ≤ j → j ≤ W → readTapeBit (A 0) j = true) ∧
      readTapeBit (A 0) (W + 1) = false := hA 0
  have h1 : H 1 = p ∧ ∀ j, readTapeBit (A 1) j = f j := hA 1
  have h2 : H 2 = p ∧ ∀ j, readTapeBit (A 2) j = g j := hA 2
  have h3 : H 3 = 0 ∧ ∀ j, readTapeBit (A 3) j = blank j := hA 3
  have h4 : H 4 = 0 := (hA 4).1
  set ℓ := natBitLength x with hℓ
  have hlen := natWord_length x
  obtain ⟨U', R', hU', hR', hs⟩ := run (A 0) (A 1) (A 2) (A 3) (A 4) p ℓ x W hW (lt_natBitLength x)
    h0.2.1 h0.2.2.1 h0.2.2.2
    (fun i hi => by rw [h1.2, hS i (by omega), natWord_getD, if_pos hi])
    (by rw [h1.2, hS ℓ (by omega), natWord_getD, if_neg (by omega), if_pos rfl])
    (fun i hi => by
      rw [h1.2, show p + ℓ + 1 + i = p + (ℓ + 1 + i) by omega, hS (ℓ + 1 + i) (by omega), natWord_getD,
        if_neg (by omega), if_neg (by omega)]
      congr 1; omega)
    (fun j => h3.2 j)
  have eH : (![0, p, p, 0, 0] : Fin 5 → ℕ) = H := by
    funext i; fin_cases i
    · exact h0.1.symm
    · exact h1.1.symm
    · exact h2.1.symm
    · exact h3.1.symm
    · exact h4.symm
  have eA : (![A 0, A 1, A 2, A 3, A 4] : Fin 5 → List Bool) = A := by funext i; fin_cases i <;> rfl
  refine ⟨_, _, (hs.congr_in eH eA).enlarge (by omega), ?_⟩
  intro i
  fin_cases i
  · exact ⟨rfl, h0.2⟩
  · exact ⟨by simp [hlen]; omega, h1.2⟩
  · exact ⟨by simp [hlen]; omega, h2.2⟩
  · exact ⟨rfl, hU'⟩
  · exact ⟨rfl, hR'⟩

/-- ReadNat docked at five ambient slots (ruler, stream, marks, unary counter, register). -/
def at5 {N : ℕ} (rl s m u r : Fin N) := RecoveryFocus.machine ![rl, s, m, u, r] machine

theorem at_run {N W : ℕ} (σ : Fin N → TS) (rl s m u r : Fin N) (hi : Function.Injective ![rl, s, m, u, r])
    (p x y : ℕ) (f g : ℕ → Bool) (hW : natBitLength x ≤ W)
    (hS : ∀ i, i < (natWord x).length → f (p + i) = (natWord x).getD i false)
    (hrl : σ rl = .ruler) (hs : σ s = .cells f p) (hm : σ m = .cells g p) (hu : σ u = .cells blank 0)
    (hr : σ r = .reg y) :
    LRuns W (at5 rl s m u r) (3 * W + 5) σ
      (Function.update (Function.update (Function.update σ s (.cells f (p + (natWord x).length)))
        m (.cells g (p + (natWord x).length))) r (.reg x)) := by
  have h := (lruns W p x y f g hW hS).dockK ![rl, s, m, u, r] hi σ
    (by intro j; fin_cases j
        · exact hrl
        · exact hs
        · exact hm
        · exact hu
        · exact hr) [4, 2, 1]
    (by intro j hj; fin_cases j
        · rfl
        · simp at hj
        · simp at hj
        · rfl
        · simp at hj)
  exact h

end ReadNat

end
end NearCubicWires.PacketsMeta

