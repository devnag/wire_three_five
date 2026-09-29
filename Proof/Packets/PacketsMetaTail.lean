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
abbrev rP : Fin 17 := 6
abbrev rE : Fin 17 := 7
abbrev rF1 : Fin 17 := 8
abbrev rK : Fin 17 := 13
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

/-! ## The two tails -/

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

