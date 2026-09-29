import Proof.Packets.PacketsMetaTape

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

/-! ## The pure sweep -/

/-- Process `m` cells of the two bit streams `a`, `b` with carry `c`: the output bits and final carry. -/
def sw (f : Bool → Bool → Bool → Bool × Bool) : Bool → (ℕ → Bool) → (ℕ → Bool) → ℕ → List Bool × Bool
  | c, _, _, 0 => ([], c)
  | c, a, b, m + 1 =>
    ((f (a 0) (b 0) c).1 :: (sw f (f (a 0) (b 0) c).2 (fun k => a (k + 1)) (fun k => b (k + 1)) m).1,
      (sw f (f (a 0) (b 0) c).2 (fun k => a (k + 1)) (fun k => b (k + 1)) m).2)

theorem sw_length (f : Bool → Bool → Bool → Bool × Bool) (c : Bool) (a b : ℕ → Bool) (m : ℕ) :
    (sw f c a b m).1.length = m := by
  induction m generalizing c a b with
  | zero => rfl
  | succ m ih => simp [sw, ih]

theorem sw_congr (f : Bool → Bool → Bool → Bool × Bool) (c : Bool) (m : ℕ) :
    ∀ (a b a' b' : ℕ → Bool), (∀ k, k < m → a k = a' k) → (∀ k, k < m → b k = b' k) →
      sw f c a b m = sw f c a' b' m := by
  induction m generalizing c with
  | zero => intros; rfl
  | succ m ih =>
    intro a b a' b' ha hb
    simp only [sw]
    rw [ha 0 (by omega), hb 0 (by omega),
      ih _ (fun k => a (k + 1)) (fun k => b (k + 1)) (fun k => a' (k + 1)) (fun k => b' (k + 1))
        (fun k hk => ha (k + 1) (by omega)) (fun k hk => hb (k + 1) (by omega))]

/-- LSB-first value of a bit list. -/
def lval : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * lval bs

/-- LSB-first value of the first `m` bits of a stream. -/
def fv (a : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 => (a 0).toNat + 2 * fv (fun k => a (k + 1)) m

theorem lval_lt (l : List Bool) : lval l < 2 ^ l.length := by
  induction l with
  | nil => simp [lval]
  | cons b l ih =>
    simp only [lval, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem lval_testBit (l : List Bool) (k : ℕ) : (lval l).testBit k = l.getD k false := by
  induction l generalizing k with
  | nil => simp [lval]
  | cons b l ih =>
    cases k with
    | zero =>
      simp only [lval, List.getD_cons_zero]
      cases b <;> simp [Nat.testBit_zero]
    | succ k =>
      simp only [lval, List.getD_cons_succ]
      rw [← ih k]
      have e : (b.toNat + 2 * lval l) / 2 = lval l := by cases b <;> simp <;> omega
      rw [Nat.testBit_succ, e]

theorem fv_testBit (x : ℕ) (m : ℕ) : fv (fun k => x.testBit k) m = x % 2 ^ m := by
  induction m generalizing x with
  | zero => simp [fv, Nat.mod_one]
  | succ m ih =>
    simp only [fv]
    have h1 : (fun k => x.testBit (k + 1)) = (fun k => (x / 2).testBit k) := by
      funext k; rw [Nat.testBit_succ]
    rw [h1, ih (x / 2), Nat.testBit_zero, pow_succ]
    have h2 : x % (2 ^ m * 2) = x % 2 + 2 * (x / 2 % 2 ^ m) := by
      rw [Nat.mul_comm, Nat.mod_mul]
    rw [h2]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

/-! ### The five bit functions and their value laws -/

def addF (a b c : Bool) : Bool × Bool := (xor (xor a b) c, (a && b) || (a && c) || (b && c))
def subF (a b c : Bool) : Bool × Bool := (xor (xor a b) c, (!a && b) || (!a && c) || (b && c))
def copyF (_ b c : Bool) : Bool × Bool := (b, c)
def zeroF (_ _ c : Bool) : Bool × Bool := (false, c)
def shlF (a _ c : Bool) : Bool × Bool := (c, a)

theorem sw_add (c : Bool) (a b : ℕ → Bool) (m : ℕ) :
    lval (sw addF c a b m).1 + 2 ^ m * (sw addF c a b m).2.toNat = fv a m + fv b m + c.toNat := by
  induction m generalizing c a b with
  | zero => simp [sw, lval, fv]
  | succ m ih =>
    simp only [sw, lval, fv, pow_succ]
    have h := ih (addF (a 0) (b 0) c).2 (fun k => a (k + 1)) (fun k => b (k + 1))
    generalize (sw addF (addF (a 0) (b 0) c).2 (fun k => a (k + 1)) (fun k => b (k + 1)) m) = r at h ⊢
    have hb : ((addF (a 0) (b 0) c).1).toNat + 2 * ((addF (a 0) (b 0) c).2).toNat =
        (a 0).toNat + (b 0).toNat + c.toNat := by
      cases a 0 <;> cases b 0 <;> cases c <;> rfl
    nlinarith

theorem sw_sub (c : Bool) (a b : ℕ → Bool) (m : ℕ) :
    fv a m + 2 ^ m * (sw subF c a b m).2.toNat = lval (sw subF c a b m).1 + fv b m + c.toNat := by
  induction m generalizing c a b with
  | zero => simp [sw, lval, fv]
  | succ m ih =>
    simp only [sw, lval, fv, pow_succ]
    have h := ih (subF (a 0) (b 0) c).2 (fun k => a (k + 1)) (fun k => b (k + 1))
    generalize (sw subF (subF (a 0) (b 0) c).2 (fun k => a (k + 1)) (fun k => b (k + 1)) m) = r at h ⊢
    have hb : (a 0).toNat + 2 * ((subF (a 0) (b 0) c).2).toNat =
        ((subF (a 0) (b 0) c).1).toNat + (b 0).toNat + c.toNat := by
      cases a 0 <;> cases b 0 <;> cases c <;> rfl
    nlinarith

theorem sw_copy (c : Bool) (a b : ℕ → Bool) (m : ℕ) :
    lval (sw copyF c a b m).1 = fv b m ∧ (sw copyF c a b m).2 = c := by
  induction m generalizing c a b with
  | zero => simp [sw, lval, fv]
  | succ m ih =>
    simp only [sw, lval, fv, copyF]
    obtain ⟨h1, h2⟩ := ih c (fun k => a (k + 1)) (fun k => b (k + 1))
    exact ⟨by rw [h1], h2⟩

theorem sw_zero (c : Bool) (a b : ℕ → Bool) (m : ℕ) :
    lval (sw zeroF c a b m).1 = 0 ∧ (sw zeroF c a b m).2 = c := by
  induction m generalizing c a b with
  | zero => simp [sw, lval]
  | succ m ih =>
    simp only [sw, lval, zeroF]
    obtain ⟨h1, h2⟩ := ih c (fun k => a (k + 1)) (fun k => b (k + 1))
    exact ⟨by rw [h1]; rfl, h2⟩

theorem sw_shl (c : Bool) (a b : ℕ → Bool) (m : ℕ) :
    lval (sw shlF c a b m).1 + 2 ^ m * (sw shlF c a b m).2.toNat = 2 * fv a m + c.toNat := by
  induction m generalizing c a b with
  | zero => simp [sw, lval, fv]
  | succ m ih =>
    simp only [sw, lval, fv, pow_succ, shlF]
    have h := ih (a 0) (fun k => a (k + 1)) (fun k => b (k + 1))
    generalize (sw shlF (a 0) (fun k => a (k + 1)) (fun k => b (k + 1)) m) = r at h ⊢
    nlinarith [h]

/-! ## The sweep machine -/

namespace Sweep

def cq (c : Bool) : Fin 6 := if c then 2 else 1
def rq (c : Bool) : Fin 6 := if c then 4 else 3

/-- Tapes: 0 ruler, 1 `x`, 2 `y`, 3 flag. States: 0 start, `cq c` processing with carry `c`,
`rq c` rewinding with carry `c`, 5 halt. -/
def machine (f : Bool → Bool → Bool → Bool × Bool) (c0 wr : Bool) : Machine 4 6 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 5
  rule := fun q b =>
    if q.val = 0 then some ⟨cq c0, fun _ => none, ![.right, .right, .right, .stay]⟩
    else if q.val = 1 ∨ q.val = 2 then
      (if b 0 then some ⟨cq (f (b 1) (b 2) (decide (q.val = 2))).2,
          ![none, if wr then some (f (b 1) (b 2) (decide (q.val = 2))).1 else none, none, none],
          ![.right, .right, .right, .stay]⟩
      else some ⟨rq (decide (q.val = 2)), fun _ => none, ![.left, .left, .left, .stay]⟩)
    else if q.val = 3 ∨ q.val = 4 then
      (if b 0 then some ⟨q, fun _ => none, ![.left, .left, .left, .stay]⟩
      else some ⟨5, ![none, none, none, some (decide (q.val = 4))], fun _ => .stay⟩)
    else none

def cfg (q : Fin 6) (hr hx hy : ℕ) (R X Y F : List Bool) : Configuration 4 6 :=
  ⟨q, ![hr, hx, hy, 0], ![R, X, Y, F]⟩

theorem cq_val (c : Bool) : decide ((cq c).val = 2) = c := by cases c <;> rfl
theorem rq_val (c : Bool) : decide ((rq c).val = 4) = c := by cases c <;> rfl

theorem start_step (f : Bool → Bool → Bool → Bool × Bool) (c0 wr : Bool) (px py : ℕ) (R X Y F : List Bool) :
    step (machine f c0 wr) (cfg 0 0 px py R X Y F) = some (cfg (cq c0) 1 (px + 1) (py + 1) R X Y F) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp only [Fin.isValue, Fin.val_zero, ↓reduceIte, Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem proc_step (f : Bool → Bool → Bool → Bool × Bool) (c0 wr c : Bool) (i hx hy : ℕ) (R X Y F : List Bool)
    (hR : readTapeBit R i = true) :
    step (machine f c0 wr) (cfg (cq c) i hx hy R X Y F) =
      some (cfg (cq (f (readTapeBit X hx) (readTapeBit Y hy) c).2) (i + 1) (hx + 1) (hy + 1) R
        (if wr then writeTapeBit X hx (f (readTapeBit X hx) (readTapeBit Y hy) c).1 else X) Y F) := by
  have h12 : (cq c).val = 1 ∨ (cq c).val = 2 := by cases c <;> simp [cq]
  have h0 : (cq c).val ≠ 0 := by cases c <;> simp [cq]
  simp only [step, machine, cfg, Configuration.scanned]
  simp only [h0, h12, ↓reduceIte, cq_val]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, hR, ↓reduceIte,
    Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> cases wr <;> simp [applyAction]

theorem turn_step (f : Bool → Bool → Bool → Bool × Bool) (c0 wr c : Bool) (i hx hy : ℕ) (R X Y F : List Bool)
    (hR : readTapeBit R i = false) :
    step (machine f c0 wr) (cfg (cq c) i hx hy R X Y F) =
      some (cfg (rq c) (i - 1) (hx - 1) (hy - 1) R X Y F) := by
  have h12 : (cq c).val = 1 ∨ (cq c).val = 2 := by cases c <;> simp [cq]
  have h0 : (cq c).val ≠ 0 := by cases c <;> simp [cq]
  simp only [step, machine, cfg, Configuration.scanned]
  simp only [h0, h12, ↓reduceIte, cq_val]
  simp only [Fin.isValue, Matrix.cons_val_zero, hR, Bool.false_eq_true, ↓reduceIte, Option.map_some,
    Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem back_step (f : Bool → Bool → Bool → Bool × Bool) (c0 wr c : Bool) (i hx hy : ℕ) (R X Y F : List Bool)
    (hR : readTapeBit R i = true) :
    step (machine f c0 wr) (cfg (rq c) i hx hy R X Y F) =
      some (cfg (rq c) (i - 1) (hx - 1) (hy - 1) R X Y F) := by
  have h34 : (rq c).val = 3 ∨ (rq c).val = 4 := by cases c <;> simp [rq]
  have h0 : (rq c).val ≠ 0 := by cases c <;> simp [rq]
  have h12 : ¬ ((rq c).val = 1 ∨ (rq c).val = 2) := by cases c <;> simp [rq]
  simp only [step, machine, cfg, Configuration.scanned]
  simp only [h0, h12, h34, ↓reduceIte]
  simp only [Fin.isValue, Matrix.cons_val_zero, hR, ↓reduceIte, Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem end_step (f : Bool → Bool → Bool → Bool × Bool) (c0 wr c : Bool) (i hx hy : ℕ) (R X Y F : List Bool)
    (hR : readTapeBit R i = false) :
    step (machine f c0 wr) (cfg (rq c) i hx hy R X Y F) =
      some (cfg 5 i hx hy R X Y (writeTapeBit F 0 c)) := by
  have h34 : (rq c).val = 3 ∨ (rq c).val = 4 := by cases c <;> simp [rq]
  have h0 : (rq c).val ≠ 0 := by cases c <;> simp [rq]
  have h12 : ¬ ((rq c).val = 1 ∨ (rq c).val = 2) := by cases c <;> simp [rq]
  simp only [step, machine, cfg, Configuration.scanned]
  simp only [h0, h12, h34, ↓reduceIte, rq_val]
  simp only [Fin.isValue, Matrix.cons_val_zero, hR, Bool.false_eq_true, ↓reduceIte, Option.map_some,
    Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem cq_ne {f : Bool → Bool → Bool → Bool × Bool} {c0 wr : Bool} (c : Bool) :
    (machine f c0 wr).halted (cq c) = false := by cases c <;> rfl
theorem rq_ne {f : Bool → Bool → Bool → Bool × Bool} {c0 wr : Bool} (c : Bool) :
    (machine f c0 wr).halted (rq c) = false := by cases c <;> rfl

/-- Conditional successive writes. -/
def upd (wr : Bool) (X : List Bool) (p : ℕ) (os : List Bool) : List Bool := if wr then writes X p os else X

theorem upd_nil (wr : Bool) (X : List Bool) (p : ℕ) : upd wr X p [] = X := by cases wr <;> rfl

theorem upd_cons (wr : Bool) (X : List Bool) (p : ℕ) (o : Bool) (os : List Bool) :
    upd wr X p (o :: os) = upd wr (if wr then writeTapeBit X p o else X) (p + 1) os := by
  cases wr <;> rfl

/-- The processing pass over `m` marked cells. -/
theorem proc_loop (f : Bool → Bool → Bool → Bool × Bool) (c0 wr : Bool) (R Y F : List Bool) (px py : ℕ) :
    ∀ (m i : ℕ) (c : Bool) (X : List Bool), (∀ k, k < m → readTapeBit R (i + k) = true) →
      Timed (machine f c0 wr) m (cfg (cq c) i (px + i) (py + i) R X Y F)
        (cfg (cq (sw f c (fun k => readTapeBit X (px + i + k)) (fun k => readTapeBit Y (py + i + k)) m).2)
          (i + m) (px + i + m) (py + i + m) R
          (upd wr X (px + i)
            (sw f c (fun k => readTapeBit X (px + i + k)) (fun k => readTapeBit Y (py + i + k)) m).1)
          Y F) := by
  intro m
  induction m with
  | zero =>
    intro i c X _
    simp only [sw, Nat.add_zero, upd_nil]
    exact Timed.refl _ _
  | succ m ih =>
    intro i c X hR
    have s1 := Timed.single (cq_ne (f := f) (c0 := c0) (wr := wr) c)
      (proc_step f c0 wr c i (px + i) (py + i) R X Y F (by simpa using hR 0 (by omega)))
    have hR' : ∀ k, k < m → readTapeBit R ((i + 1) + k) = true := by
      intro k hk
      have := hR (k + 1) (by omega)
      rwa [show i + (k + 1) = i + 1 + k by omega] at this
    have s2 := ih (i + 1) (f (readTapeBit X (px + i)) (readTapeBit Y (py + i)) c).2
      (if wr then writeTapeBit X (px + i) (f (readTapeBit X (px + i)) (readTapeBit Y (py + i)) c).1 else X) hR'
    rw [show px + (i + 1) = px + i + 1 by omega, show py + (i + 1) = py + i + 1 by omega] at s2
    have hread : (fun k => readTapeBit
        (if wr then writeTapeBit X (px + i) (f (readTapeBit X (px + i)) (readTapeBit Y (py + i)) c).1 else X)
        (px + i + 1 + k)) = (fun k => readTapeBit X (px + i + (k + 1))) := by
      funext k
      split_ifs
      · rw [read_write, if_neg (by omega), show px + i + 1 + k = px + i + (k + 1) by omega]
      · rw [show px + i + 1 + k = px + i + (k + 1) by omega]
    have hready : (fun k => readTapeBit Y (py + i + 1 + k)) = (fun k => readTapeBit Y (py + i + (k + 1))) := by
      funext k; rw [show py + i + 1 + k = py + i + (k + 1) by omega]
    rw [hread, hready] at s2
    have h := s1.trans s2
    have e0 : readTapeBit X (px + i + 0) = readTapeBit X (px + i) := by rw [Nat.add_zero]
    have e1 : readTapeBit Y (py + i + 0) = readTapeBit Y (py + i) := by rw [Nat.add_zero]
    have hsw : sw f c (fun k => readTapeBit X (px + i + k)) (fun k => readTapeBit Y (py + i + k)) (m + 1) =
        ((f (readTapeBit X (px + i)) (readTapeBit Y (py + i)) c).1 ::
          (sw f (f (readTapeBit X (px + i)) (readTapeBit Y (py + i)) c).2
            (fun k => readTapeBit X (px + i + (k + 1))) (fun k => readTapeBit Y (py + i + (k + 1))) m).1,
          (sw f (f (readTapeBit X (px + i)) (readTapeBit Y (py + i)) c).2
            (fun k => readTapeBit X (px + i + (k + 1))) (fun k => readTapeBit Y (py + i + (k + 1))) m).2) := by
      simp only [sw, e0, e1]
    rw [hsw, upd_cons]
    have ep : px + i + 1 + m = px + i + (m + 1) := by omega
    have eq : py + i + 1 + m = py + i + (m + 1) := by omega
    have ei : i + 1 + m = i + (m + 1) := by omega
    rw [ep, eq, ei, show 1 + m = m + 1 by omega] at h
    exact h

/-- The rewinding pass over `m` marked cells. -/
theorem back_loop (f : Bool → Bool → Bool → Bool × Bool) (c0 wr c : Bool) (R X Y F : List Bool) (px py : ℕ) :
    ∀ m, (∀ k, 1 ≤ k → k ≤ m → readTapeBit R k = true) →
      Timed (machine f c0 wr) m (cfg (rq c) m (px + m) (py + m) R X Y F) (cfg (rq c) 0 px py R X Y F) := by
  intro m
  induction m with
  | zero => intro _; exact Timed.refl _ _
  | succ m ih =>
    intro hR
    have s1 := Timed.single (rq_ne (f := f) (c0 := c0) (wr := wr) c)
      (back_step f c0 wr c (m + 1) (px + (m + 1)) (py + (m + 1)) R X Y F (hR (m + 1) (by omega) (le_refl _)))
    have s2 := ih (fun k hk1 hk2 => hR k hk1 (by omega))
    simp only [Nat.add_sub_cancel, show px + (m + 1) - 1 = px + m by omega,
      show py + (m + 1) - 1 = py + m by omega] at s1
    have h := s1.trans s2
    rwa [show 1 + m = m + 1 by omega] at h

/-- The generic sweep: `2W+3` steps, every head returned. -/
theorem run (f : Bool → Bool → Bool → Bool × Bool) (c0 wr : Bool) (W px py : ℕ) (R X Y F : List Bool)
    (hR0 : readTapeBit R 0 = false) (hR : ∀ j, 1 ≤ j → j ≤ W → readTapeBit R j = true)
    (hRW : readTapeBit R (W + 1) = false) :
    Step (machine f c0 wr) (2 * W + 3) ![0, px, py, 0] ![R, X, Y, F] ![0, px, py, 0]
      ![R, upd wr X (px + 1)
          (sw f c0 (fun k => readTapeBit X (px + 1 + k)) (fun k => readTapeBit Y (py + 1 + k)) W).1, Y,
        writeTapeBit F 0
          (sw f c0 (fun k => readTapeBit X (px + 1 + k)) (fun k => readTapeBit Y (py + 1 + k)) W).2] := by
  set res := sw f c0 (fun k => readTapeBit X (px + 1 + k)) (fun k => readTapeBit Y (py + 1 + k)) W with hres
  set X' := upd wr X (px + 1) res.1 with hX'
  have s0 := Timed.single (by rfl : (machine f c0 wr).halted 0 = false) (start_step f c0 wr px py R X Y F)
  have s1 := proc_loop f c0 wr R Y F px py W 1 c0 X (fun k hk => hR (1 + k) (by omega) (by omega))
  rw [← hres, ← hX'] at s1
  have s2 := Timed.single (cq_ne (f := f) (c0 := c0) (wr := wr) res.2)
    (turn_step f c0 wr res.2 (1 + W) (px + 1 + W) (py + 1 + W) R X' Y F (by rwa [Nat.add_comm]))
  simp only [show 1 + W - 1 = W by omega, show px + 1 + W - 1 = px + W by omega,
    show py + 1 + W - 1 = py + W by omega] at s2
  have s3 := back_loop f c0 wr res.2 R X' Y F px py W hR
  have s4 := Timed.single (rq_ne (f := f) (c0 := c0) (wr := wr) res.2)
    (end_step f c0 wr res.2 0 px py R X' Y F hR0)
  have h := (((s0.trans s1).trans s2).trans s3).trans s4
  obtain ⟨r, hr, hf, hs⟩ := h.run (by rfl)
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · have e : 1 + W + 1 + W + 1 = 2 * W + 3 := by omega
    rw [e] at hr
    exact hr
  · rw [hf]; rfl
  · rw [hf]; rfl
  · omega

end Sweep

/-! ## The ruler walk -/

namespace Walk

end Walk

end NearCubicWires.PacketsMeta

