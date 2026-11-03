import Proof.Packets.PacketsMetaLoops

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
open NearCubicWires.SupplierPrime
noncomputable section

namespace Tail

abbrev rl : Fin 17 := 0
abbrev fl : Fin 17 := 1
abbrev zo : Fin 17 := 2
abbrev rF : Fin 17 := 3
abbrev rC : Fin 17 := 4
abbrev rT : Fin 17 := 5
abbrev rP : Fin 17 := 6
abbrev rE : Fin 17 := 7
abbrev rF1 : Fin 17 := 8
abbrev rD : Fin 17 := 9
abbrev rV : Fin 17 := 10
abbrev rS : Fin 17 := 11
abbrev r24 : Fin 17 := 12
abbrev rK : Fin 17 := 13
abbrev rt : Fin 17 := 14
abbrev rm : Fin 17 := 15
abbrev ou : Fin 17 := 16

/-- The tail's roles. -/
def tst (F C T P E F1 D V S K24 K : ℕ) (b : Bool) (o : ℕ) : Fin 17 → TS :=
  ![.ruler, .flag b, .reg 0, .reg F, .reg C, .reg T, .reg P, .reg E, .reg F1, .reg D, .reg V, .reg S,
    .reg K24, .reg K, .reg 0, .reg 0, .out o]

def cpyI (x y : Fin 17) := swAt copyF false true rl x y fl
def incI (x : Fin 17) := swAt addF true true rl x zo fl
def decI (x : Fin 17) := swAt subF true true rl x zo fl
def ltI (x y : Fin 17) := swAt subF false false rl x y fl
def shlI (x : Fin 17) := swAt shlF false true rl x zo fl
def addI (x y : Fin 17) := swAt addF false true rl x y fl
def mulI (x y z : Fin 17) := RecoveryFocus.machine ![rl, x, y, z, rt, rm, fl, zo] Mul.machine
def appI := RecoveryFocus.machine ![ou] append

/-! ## The output loop: `K` in unary -/

theorem app_at {W : ℕ} (σ : Fin 17 → TS) (n : ℕ) (h : σ ou = .out n) :
    LRuns W appI 1 σ (Function.update σ ou (.out (n + 1))) :=
  (append_lruns W n).dockK ![ou] (by decide) σ (by intro j; fin_cases j; exact h) [0]
    (by intro j hj; fin_cases j; simp at hj)

def outLoop := Loop (ltI zo rK) (Composition.machine (decI rK) appI) fl

theorem outLoop_run {W : ℕ} (F C T P E F1 D V S K24 K : ℕ) (b : Bool) (hK : K < 2 ^ W) :
    LRuns W outLoop ((K + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + 1) + 2))
      (tst F C T P E F1 D V S K24 K b 0) (tst F C T P E F1 D V S K24 0 false K) := by
  have h := Loop.runs (W := W) (ltI zo rK) (Composition.machine (decI rK) appI) fl
    (fun i => tst F C T P E F1 D V S K24 (K - i) (if i = 0 then b else false) i)
    (fun i => tst F C T P E F1 D V S K24 (K - i) (decide (i < K)) i) K
    (fun i hi => by
      have h := lt_at (W := W) (tst F C T P E F1 D V S K24 (K - i) (if i = 0 then b else false) i) rl zo rK fl
        (by decide) 0 (K - i) _ rfl rfl rfl rfl (Nat.two_pow_pos W) (by omega)
      refine h.congr_out ?_
      have hd : decide (0 < K - i) = decide (i < K) := decide_eq_decide.mpr (by omega)
      rw [hd]
      funext j
      fin_cases j <;> rfl)
    (fun i _ => rfl)
    (fun i hi => by
      have h1 := dec_at (W := W) (tst F C T P E F1 D V S K24 (K - i) (decide (i < K)) i) rl rK zo fl
        (by decide) (K - i) 0 _ rfl rfl rfl rfl rfl (by omega) (by omega)
      have h2 := app_at (W := W) (Function.update (Function.update
        (tst F C T P E F1 D V S K24 (K - i) (decide (i < K)) i) rK (.reg (K - i - 1))) fl (.flag false)) i rfl
      refine (h1.seq h2).congr_out ?_
      have e : K - i - 1 = K - (i + 1) := by omega
      rw [e]
      funext j
      fin_cases j <;> rfl)
  have e0 : tst F C T P E F1 D V S K24 (K - 0) (if 0 = 0 then b else false) 0 = tst F C T P E F1 D V S K24 K b 0 := by
    simp
  have eK : tst F C T P E F1 D V S K24 (K - K) (decide (K < K)) K = tst F C T P E F1 D V S K24 0 false K := by
    simp
  rw [e0, eK] at h
  exact h

/-! ## Exact doubling -/

theorem shl_at' {N W : ℕ} (σ : Fin N → TS) (r x y fl : Fin N) (hd : D4 r x y fl) (a b : ℕ) (c : Bool)
    (hr : σ r = .ruler) (hx : σ x = .reg a) (hy : σ y = .reg b) (hf : σ fl = .flag c) (ha : 2 * a < 2 ^ W) :
    LRuns W (swAt shlF false true r x y fl) (2 * W + 3) σ
      (Function.update (Function.update σ x (.reg (2 * a))) fl (.flag false)) := by
  have h := shl_at (W := W) σ r x y fl hd a b c hr hx hy hf (by omega)
  rw [Nat.mod_eq_of_lt ha, decide_eq_false (by omega)] at h
  exact h

/-! ## Segment A: `F1 := F + 1`, `POW := 1` -/

def segA := Composition.machine (cpyI rF1 rF) (Composition.machine (incI rF1) (incI rP))

theorem segA_run {W : ℕ} (F C T : ℕ) (b : Bool) (hF : F + 1 < 2 ^ W) (hW : 1 ≤ W) :
    LRuns W segA ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + (2 * W + 3)))
      (tst F C T 0 0 0 0 0 0 0 0 b 0) (tst F C T 1 0 (F + 1) 0 0 0 0 0 false 0) := by
  have h2W : 2 ≤ 2 ^ W := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have hall := (cpy_at (W := W) (tst F C T 0 0 0 0 0 0 0 0 b 0) rl rF1 rF fl (by decide) 0 F b rfl rfl rfl rfl
      (by omega)).seq
    ((inc_at (W := W) _ rl rF1 zo fl (by decide) F 0 false (by rfl) (by rfl) (by rfl) (by rfl) rfl hF).seq
    (inc_at (W := W) _ rl rP zo fl (by decide) 0 0 false (by rfl) (by rfl) (by rfl) (by rfl) rfl (by omega)))
  refine hall.congr_out ?_
  funext j
  fin_cases j <;> rfl

/-! ## Segment B: `E := clog₂ (F + 1)` -/

def segB := Loop (ltI rP rF1) (Composition.machine (shlI rP) (incI rE)) fl

theorem pow_clog_lt (x i : ℕ) (hx : 1 ≤ x) (hi : i ≤ Nat.clog 2 x) : 2 ^ i < 2 * x := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    simp
    omega
  · have h1 : i - 1 < Nat.clog 2 x := by omega
    have h2 := (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mp h1
    have e : 2 ^ i = 2 * 2 ^ (i - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega

theorem segB_run {W : ℕ} (F C T : ℕ) (hF : 2 * (F + 1) ≤ 2 ^ W) :
    LRuns W segB ((Nat.clog 2 (F + 1) + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + (2 * W + 3)) + 2))
      (tst F C T 1 0 (F + 1) 0 0 0 0 0 false 0)
      (tst F C T (2 ^ Nat.clog 2 (F + 1)) (Nat.clog 2 (F + 1)) (F + 1) 0 0 0 0 0 false 0) := by
  set k := Nat.clog 2 (F + 1) with hk
  have h := Loop.runs (W := W) (ltI rP rF1) (Composition.machine (shlI rP) (incI rE)) fl
    (fun i => tst F C T (2 ^ i) i (F + 1) 0 0 0 0 0 false 0)
    (fun i => tst F C T (2 ^ i) i (F + 1) 0 0 0 0 0 (decide (i < k)) 0) k
    (fun i hi => by
      have hp := pow_clog_lt (F + 1) i (by omega) hi
      have h := lt_at (W := W) (tst F C T (2 ^ i) i (F + 1) 0 0 0 0 0 false 0) rl rP rF1 fl
        (by decide) (2 ^ i) (F + 1) false rfl rfl rfl rfl (by omega) (by omega)
      refine h.congr_out ?_
      have hd : decide (2 ^ i < F + 1) = decide (i < k) :=
        decide_eq_decide.mpr (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).symm
      rw [hd]
      funext j
      fin_cases j <;> rfl)
    (fun i _ => rfl)
    (fun i hi => by
      have hp : 2 ^ i < F + 1 := (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mp hi
      have hi' : i ≤ 2 ^ i := (Nat.lt_two_pow_self).le
      have hall := (shl_at' (W := W) (tst F C T (2 ^ i) i (F + 1) 0 0 0 0 0 (decide (i < k)) 0) rl rP zo fl
        (by decide) (2 ^ i) 0 _ rfl rfl rfl rfl (by omega)).seq
        (inc_at (W := W) _ rl rE zo fl (by decide) i 0 false (by rfl) (by rfl) (by rfl) (by rfl) rfl (by omega))
      refine hall.congr_out ?_
      rw [show 2 * 2 ^ i = 2 ^ (i + 1) by ring]
      funext j
      fin_cases j <;> rfl)
  have eK : tst F C T (2 ^ k) k (F + 1) 0 0 0 0 0 (decide (k < k)) 0 =
      tst F C T (2 ^ k) k (F + 1) 0 0 0 0 0 false 0 := by
    simp
  rw [eK] at h
  exact h

/-! ## Segment C: the denominator, the scale, the square -/

def segC1 := Composition.machine (incI rE) (Composition.machine (incI rT)
  (Composition.machine (mulI rC rT rD) (Composition.machine (shlI rD) (incI rD))))

theorem segC1_run {W : ℕ} (F C T P k F1 : ℕ) (hW : 1 ≤ W) (hk : k + 1 < 2 ^ W) (hT : T + 1 < 2 ^ W)
    (hd : 2 * (C * (T + 1)) + 1 < 2 ^ W) :
    LRuns W segC1 ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((13 * W * W + 60 * W + 40) + 1 +
      ((2 * W + 3) + 1 + (2 * W + 3)))))
      (tst F C T P k F1 0 0 0 0 0 false 0)
      (tst F C (T + 1) P (k + 1) F1 (2 * (C * (T + 1)) + 1) 0 0 0 0 false 0) := by
  have hall := (inc_at (W := W) (tst F C T P k F1 0 0 0 0 0 false 0) rl rE zo fl (by decide) k 0 false rfl rfl rfl rfl
      rfl hk).seq
    ((inc_at (W := W) _ rl rT zo fl (by decide) T 0 false (by rfl) (by rfl) (by rfl) (by rfl) rfl hT).seq
    ((Mul.at_run (W := W) _ rl rC rT rD rt rm fl zo (by decide) C (T + 1) 0 0 0 false (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hT (by omega) hW).seq
    ((shl_at' (W := W) _ rl rD zo fl (by decide) (C * (T + 1)) 0 false (by rfl) (by rfl) (by rfl) (by rfl)
      (by omega)).seq
    (inc_at (W := W) _ rl rD zo fl (by decide) (2 * (C * (T + 1))) 0 false (by rfl) (by rfl) (by rfl) (by rfl) rfl
      hd))))
  refine hall.congr_out ?_
  funext j
  fin_cases j <;> rfl

def segC2 := Composition.machine (mulI rE rD rV) (Composition.machine (cpyI rS rV)
  (Composition.machine (shlI rS) (Composition.machine (addI rS rV) (shlI rS))))

theorem segC2_run {W : ℕ} (F C T P E F1 D : ℕ) (hW : 1 ≤ W) (hD : D < 2 ^ W)
    (hV : 2 * (2 * (E * D) + E * D) < 2 ^ W) :
    LRuns W segC2 ((13 * W * W + 60 * W + 40) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 +
      ((2 * W + 3) + 1 + (2 * W + 3)))))
      (tst F C T P E F1 D 0 0 0 0 false 0)
      (tst F C T P E F1 D (E * D) (2 * (2 * (E * D) + E * D)) 0 0 false 0) := by
  have hall := (Mul.at_run (W := W) (tst F C T P E F1 D 0 0 0 0 false 0) rl rE rD rV rt rm fl zo (by decide) E D 0 0 0
      false rfl rfl rfl rfl rfl rfl rfl rfl hD (by omega) hW).seq
    ((cpy_at (W := W) _ rl rS rV fl (by decide) 0 (E * D) false (by rfl) (by rfl) (by rfl) (by rfl) (by omega)).seq
    ((shl_at' (W := W) _ rl rS zo fl (by decide) (E * D) 0 false (by rfl) (by rfl) (by rfl) (by rfl) (by omega)).seq
    ((add_at (W := W) _ rl rS rV fl (by decide) (2 * (E * D)) (E * D) false (by rfl) (by rfl) (by rfl) (by rfl)
      (by omega) (by omega) (by omega)).seq
    (shl_at' (W := W) _ rl rS zo fl (by decide) (2 * (E * D) + E * D) 0 false (by rfl) (by rfl) (by rfl) (by rfl)
      hV))))
  refine hall.congr_out ?_
  funext j
  fin_cases j <;> rfl

def segC3 := Composition.machine (incI r24) (Composition.machine (incI r24) (Composition.machine (incI r24)
  (Composition.machine (shlI r24) (Composition.machine (shlI r24) (shlI r24)))))

theorem segC3_run {W : ℕ} (F C T P E F1 D V S : ℕ) (hW : 5 ≤ W) :
    LRuns W segC3 ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 +
      ((2 * W + 3) + 1 + (2 * W + 3))))))
      (tst F C T P E F1 D V S 0 0 false 0) (tst F C T P E F1 D V S 24 0 false 0) := by
  have h32 : 32 ≤ 2 ^ W := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have hall := (inc_at (W := W) (tst F C T P E F1 D V S 0 0 false 0) rl r24 zo fl (by decide) 0 0 false rfl rfl rfl
      rfl rfl (by omega)).seq
    ((inc_at (W := W) _ rl r24 zo fl (by decide) 1 0 false (by rfl) (by rfl) (by rfl) (by rfl) rfl (by omega)).seq
    ((inc_at (W := W) _ rl r24 zo fl (by decide) 2 0 false (by rfl) (by rfl) (by rfl) (by rfl) rfl (by omega)).seq
    ((shl_at' (W := W) _ rl r24 zo fl (by decide) 3 0 false (by rfl) (by rfl) (by rfl) (by rfl) (by omega)).seq
    ((shl_at' (W := W) _ rl r24 zo fl (by decide) 6 0 false (by rfl) (by rfl) (by rfl) (by rfl) (by omega)).seq
    (shl_at' (W := W) _ rl r24 zo fl (by decide) 12 0 false (by rfl) (by rfl) (by rfl) (by rfl) (by omega))))))
  refine hall.congr_out ?_
  funext j
  fin_cases j <;> rfl

def segC4 := Composition.machine (Ite (ltI rS r24) (cpyI rS r24) (nop 17) fl)
  (Composition.machine (cpyI rV rS) (mulI rS rV rK))

theorem segC4_run {W : ℕ} (F C T P E F1 D V S : ℕ) (hW : 5 ≤ W)
    (hS : max 24 S * max 24 S < 2 ^ W) :
    LRuns W segC4 (((2 * W + 3) + (2 * W + 3) + 0 + 2) + 1 + ((2 * W + 3) + 1 + (13 * W * W + 60 * W + 40)))
      (tst F C T P E F1 D V S 24 0 false 0)
      (tst F C T P E F1 D (max 24 S) (max 24 S) 24 (max 24 S * max 24 S) false 0) := by
  have h32 : 32 ≤ 2 ^ W := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have hM1 : 1 ≤ max 24 S := le_trans (by norm_num) (le_max_left 24 S)
  have hM : max 24 S < 2 ^ W := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hM1) hS
  have hSS : S < 2 ^ W := lt_of_le_of_lt (le_max_right 24 S) hM
  have hI : LRuns W (Ite (ltI rS r24) (cpyI rS r24) (nop 17) fl) ((2 * W + 3) + (2 * W + 3) + 0 + 2)
      (tst F C T P E F1 D V S 24 0 false 0) (tst F C T P E F1 D V (max 24 S) 24 0 false 0) :=
    Ite.runs (W := W) (nc := 2 * W + 3) (np := 2 * W + 3) (nq := 0) (ltI rS r24) (cpyI rS r24) (nop 17) fl
      (decide (S < 24))
      (lt_at (W := W) (tst F C T P E F1 D V S 24 0 false 0) rl rS r24 fl (by decide) S 24 false rfl rfl rfl rfl
        hSS (by omega)) rfl
      (fun hb => by
        have hb' : S < 24 := by simpa using hb
        have h := cpy_at (W := W) (Function.update (Function.update (tst F C T P E F1 D V S 24 0 false 0) rS (.reg S))
          fl (.flag (decide (S < 24)))) rl rS r24 fl (by decide) S 24 _ rfl rfl rfl rfl (by omega)
        refine h.congr_out ?_
        rw [max_eq_left hb'.le]
        funext j
        fin_cases j <;> rfl)
      (fun hb => by
        have hb' : ¬ S < 24 := by simpa using hb
        have h := nop_lruns (W := W) (Function.update (Function.update (tst F C T P E F1 D V S 24 0 false 0) rS
          (.reg S)) fl (.flag (decide (S < 24))))
        refine h.congr_out ?_
        rw [max_eq_right (by omega), hb]
        funext j
        fin_cases j <;> rfl)
  have hall := hI.seq
    ((cpy_at (W := W) (tst F C T P E F1 D V (max 24 S) 24 0 false 0) rl rV rS fl (by decide) V (max 24 S) false
      rfl rfl rfl rfl hM).seq
    (Mul.at_run (W := W) _ rl rS rV rK rt rm fl zo (by decide) (max 24 S) (max 24 S) 0 0 0 false (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hM hS (by omega)))
  refine hall.congr_out ?_
  funext j
  fin_cases j <;> rfl

/-! ## The two tails -/

/-- The cutoff tail. -/
def tailM := Composition.machine segA (Composition.machine segB (Composition.machine segC1
  (Composition.machine segC2 (Composition.machine segC3 (Composition.machine segC4 outLoop)))))

/-- The cutoff value the tail writes. -/
def cutOf (F C T : ℕ) : ℕ := canonicalPrimeCutoff (Nat.clog 2 (F + 1)) (2 * C * (T + 1))

/-- The scale `max 24 (6(e+1)(d+1))`. -/
def scaleOf (F C T : ℕ) : ℕ :=
  max 24 (2 * (2 * ((Nat.clog 2 (F + 1) + 1) * (2 * (C * (T + 1)) + 1)) +
    (Nat.clog 2 (F + 1) + 1) * (2 * (C * (T + 1)) + 1)))

theorem cutOf_eq (F C T : ℕ) : cutOf F C T = scaleOf F C T * scaleOf F C T := by
  have e : 2 * (2 * ((Nat.clog 2 (F + 1) + 1) * (2 * (C * (T + 1)) + 1)) +
      (Nat.clog 2 (F + 1) + 1) * (2 * (C * (T + 1)) + 1)) =
      6 * (Nat.clog 2 (F + 1) + 1) * (2 * C * (T + 1) + 1) := by ring
  unfold cutOf scaleOf canonicalPrimeCutoff canonicalPrimeScale
  rw [e, sq]

def tailCost (W F C T : ℕ) : ℕ :=
  ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + (2 * W + 3))) + 1 +
  (((Nat.clog 2 (F + 1) + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + (2 * W + 3)) + 2)) + 1 +
  (((2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((13 * W * W + 60 * W + 40) + 1 + ((2 * W + 3) + 1 + (2 * W + 3))))) + 1 +
  (((13 * W * W + 60 * W + 40) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + (2 * W + 3))))) + 1 +
  (((2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + (2 * W + 3)))))) + 1 +
  ((((2 * W + 3) + (2 * W + 3) + 0 + 2) + 1 + ((2 * W + 3) + 1 + (13 * W * W + 60 * W + 40))) + 1 +
  ((cutOf F C T + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + 1) + 2)))))))

/-- **The cutoff tail.** -/
theorem tail_run {W : ℕ} (F C T : ℕ) (b : Bool) (hW : 5 ≤ W) (hF : 2 * (F + 1) ≤ 2 ^ W) (hT : T + 1 < 2 ^ W)
    (hcut : cutOf F C T < 2 ^ W) :
    LRuns W tailM (tailCost W F C T) (tst F C T 0 0 0 0 0 0 0 0 b 0)
      (tst F C (T + 1) (2 ^ Nat.clog 2 (F + 1)) (Nat.clog 2 (F + 1) + 1) (F + 1)
        (2 * (C * (T + 1)) + 1) (scaleOf F C T) (scaleOf F C T) 24 0 false (cutOf F C T)) := by
  set k := Nat.clog 2 (F + 1) with hk
  set d1 := 2 * (C * (T + 1)) + 1 with hd1
  set V0 := (k + 1) * d1 with hV0
  have hW1 : 1 ≤ W := by omega
  have hSc : scaleOf F C T = max 24 (2 * (2 * V0 + V0)) := rfl
  have hcut' := hcut
  rw [cutOf_eq] at hcut'
  have hM1 : 1 ≤ scaleOf F C T := le_trans (by norm_num) (le_max_left _ _)
  have hMc : scaleOf F C T ≤ scaleOf F C T * scaleOf F C T := Nat.le_mul_of_pos_left _ hM1
  have h6 : 2 * (2 * V0 + V0) ≤ scaleOf F C T := by rw [hSc]; exact le_max_right _ _
  have hk1 : k + 1 ≤ V0 := Nat.le_mul_of_pos_right _ (by omega)
  have hdV : d1 ≤ V0 := Nat.le_mul_of_pos_left _ (by omega)
  have hA := segA_run (W := W) F C T b (by omega) hW1
  have hB := segB_run (W := W) F C T hF
  have hC1 := segC1_run (W := W) F C T (2 ^ k) k (F + 1) hW1 (by omega) hT (by omega)
  have hC2 := segC2_run (W := W) F C (T + 1) (2 ^ k) (k + 1) (F + 1) d1 hW1 (by omega) (by omega)
  have hC3 := segC3_run (W := W) F C (T + 1) (2 ^ k) (k + 1) (F + 1) d1 V0 (2 * (2 * V0 + V0)) hW
  have hC4 := segC4_run (W := W) F C (T + 1) (2 ^ k) (k + 1) (F + 1) d1 V0 (2 * (2 * V0 + V0)) hW
    (by rw [← hSc]; exact hcut')
  have hO := outLoop_run (W := W) F C (T + 1) (2 ^ k) (k + 1) (F + 1) d1 (max 24 (2 * (2 * V0 + V0)))
    (max 24 (2 * (2 * V0 + V0))) 24 (max 24 (2 * (2 * V0 + V0)) * max 24 (2 * (2 * V0 + V0))) false
    (by rw [← hSc]; exact hcut')
  have hall := hA.seq (hB.seq (hC1.seq (hC2.seq (hC3.seq (hC4.seq hO)))))
  rw [← hSc, ← cutOf_eq] at hall
  exact hall

/-- The `|Sel|` tail: `CNT` in unary. -/
def selTailM := Composition.machine (cpyI rK rC) outLoop

theorem selTail_run {W : ℕ} (F C T : ℕ) (b : Bool) (hC : C < 2 ^ W) :
    LRuns W selTailM ((2 * W + 3) + 1 + (C + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + 1) + 2))
      (tst F C T 0 0 0 0 0 0 0 0 b 0) (tst F C T 0 0 0 0 0 0 0 0 false C) := by
  have h1 := cpy_at (W := W) (tst F C T 0 0 0 0 0 0 0 0 b 0) rl rK rC fl (by decide) 0 C b rfl rfl rfl rfl hC
  have e : Function.update (Function.update (tst F C T 0 0 0 0 0 0 0 0 b 0) rK (.reg C)) fl (.flag false) =
      tst F C T 0 0 0 0 0 0 0 C false 0 := by
    funext j
    fin_cases j <;> rfl
  rw [e] at h1
  exact h1.seq (outLoop_run (W := W) F C T 0 0 0 0 0 0 0 C false hC)

end Tail

end
end NearCubicWires.PacketsMeta

