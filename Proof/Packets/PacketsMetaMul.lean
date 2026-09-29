import Proof.Packets.PacketsMetaUnframe

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

namespace Mul

/-! ## The arithmetic of one round -/

/-- The shifted multiplier after `i` rounds. -/
def tv (W Y i : ℕ) : ℕ := Y % 2 ^ (W - i) * 2 ^ i
/-- The partial product after `i` rounds. -/
def zv (W X Y i : ℕ) : ℕ := X * (Y / 2 ^ (W - i))
/-- The mask after `i` rounds. -/
def mv (W i : ℕ) : ℕ := 2 ^ i % 2 ^ W
/-- The bit consumed in round `i`. -/
def bv (W Y i : ℕ) : Bool := decide (Y / 2 ^ (W - i - 1) % 2 = 1)

theorem round_facts (W Y i : ℕ) (hi : i < W) :
    2 * tv W Y i % 2 ^ W = tv W Y (i + 1) ∧ decide (2 ^ W ≤ 2 * tv W Y i) = bv W Y i ∧
      Y / 2 ^ (W - (i + 1)) = 2 * (Y / 2 ^ (W - i)) + (bv W Y i).toNat := by
  set k := W - i - 1 with hk
  have hWi : W - i = k + 1 := by omega
  have hWi1 : W - (i + 1) = k := by omega
  have hW : W = k + i + 1 := by omega
  have hmod : Y % 2 ^ (k + 1) = Y % 2 ^ k + 2 ^ k * (Y / 2 ^ k % 2) := Nat.mod_pow_succ
  have hb2 : Y / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hr : Y % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have hpk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hpW : 2 ^ W = 2 ^ k * 2 ^ (i + 1) := by rw [hW, show k + i + 1 = k + (i + 1) by omega, pow_add]
  have hpi : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
  have htv : tv W Y i = (Y % 2 ^ k + 2 ^ k * (Y / 2 ^ k % 2)) * 2 ^ i := by
    unfold tv; rw [hWi, hmod]
  have htv1 : tv W Y (i + 1) = Y % 2 ^ k * 2 ^ (i + 1) := by unfold tv; rw [hWi1]
  have h2t : 2 * tv W Y i = Y % 2 ^ k * 2 ^ (i + 1) + 2 ^ W * (Y / 2 ^ k % 2) := by
    rw [htv, hpW, hpi]; ring
  have hlow : Y % 2 ^ k * 2 ^ (i + 1) < 2 ^ W := by
    rw [hpW]; exact Nat.mul_lt_mul_of_pos_right hr (Nat.two_pow_pos _)
  refine ⟨?_, ?_, ?_⟩
  · rw [h2t, htv1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
  · unfold bv
    rw [show W - i - 1 = k from rfl]
    apply dec_congr
    rw [h2t]
    constructor
    · intro h
      by_contra hne
      have h0 : Y / 2 ^ k % 2 = 0 := by omega
      rw [h0, Nat.mul_zero, Nat.add_zero] at h
      omega
    · intro h
      rw [h]
      omega
  · unfold bv
    rw [hWi1, hWi, Nat.add_sub_cancel]
    have e1 : Y / 2 ^ (k + 1) = Y / 2 ^ k / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
    have e2 := Nat.div_add_mod (Y / 2 ^ k) 2
    rw [e1]
    by_cases h : Y / 2 ^ k % 2 = 1
    · simp [h]; omega
    · have h0 : Y / 2 ^ k % 2 = 0 := by omega
      simp [h0]; omega

theorem mv_succ (W i : ℕ) (hi : i < W) : 2 * mv W i % 2 ^ W = mv W (i + 1) := by
  unfold mv
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hi), ← pow_succ']

theorem mv_pos (W i : ℕ) (hi : i ≤ W) : decide (0 < mv W i) = decide (i < W) := by
  unfold mv
  apply dec_congr
  by_cases h : i < W
  · rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h)]
    exact ⟨fun _ => h, fun _ => Nat.two_pow_pos i⟩
  · have hiW : i = W := by omega
    subst hiW
    simp

theorem zv_zero (W X Y : ℕ) (hY : Y < 2 ^ W) : zv W X Y 0 = 0 := by
  unfold zv; rw [Nat.sub_zero, Nat.div_eq_of_lt hY, Nat.mul_zero]

theorem zv_W (W X Y : ℕ) : zv W X Y W = X * Y := by unfold zv; simp

theorem tv_zero (W Y : ℕ) (hY : Y < 2 ^ W) : tv W Y 0 = Y := by unfold tv; simp [Nat.mod_eq_of_lt hY]

theorem zv_le (W X Y i : ℕ) : zv W X Y i ≤ X * Y := by
  unfold zv; exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)

theorem zv_step (W X Y i : ℕ) (hi : i < W) :
    zv W X Y (i + 1) = 2 * zv W X Y i + (if bv W Y i then X else 0) := by
  obtain ⟨_, _, h3⟩ := round_facts W Y i hi
  unfold zv; rw [h3]
  cases bv W Y i <;> simp <;> ring

theorem tv_lt (W Y i : ℕ) (hi : i ≤ W) : tv W Y i < 2 ^ W := by
  unfold tv
  have h1 : Y % 2 ^ (W - i) < 2 ^ (W - i) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h2 : 2 ^ W = 2 ^ (W - i) * 2 ^ i := by rw [← pow_add]; congr 1; omega
  rw [h2]; exact Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)

theorem mv_lt (W i : ℕ) : mv W i < 2 ^ W := Nat.mod_lt _ (Nat.two_pow_pos W)

/-! ## The machine -/

abbrev rl : Fin 8 := 0
abbrev xr : Fin 8 := 1
abbrev yr : Fin 8 := 2
abbrev zr : Fin 8 := 3
abbrev tr : Fin 8 := 4
abbrev mr : Fin 8 := 5
abbrev fl : Fin 8 := 6
abbrev zo : Fin 8 := 7

def body :=
  Composition.machine (swAt shlF false true rl mr zo fl)
    (Composition.machine (swAt shlF false true rl zr zo fl)
      (Composition.machine (swAt shlF false true rl tr zo fl)
        (Ite (nop 8) (swAt addF false true rl zr xr fl) (nop 8) fl)))

def test := swAt subF false false rl zo mr fl

def loop := Loop test body fl

def machine :=
  Composition.machine
    (Composition.machine (swAt zeroF false true rl zr zo fl)
      (Composition.machine (swAt copyF false true rl tr yr fl)
        (Composition.machine (swAt zeroF false true rl mr zo fl) (swAt addF true true rl mr zo fl)))) loop

/-- The roles at the start of round `i`. -/
def st (W X Y : ℕ) (i : ℕ) (b : Bool) : Fin 8 → TS :=
  ![.ruler, .reg X, .reg Y, .reg (zv W X Y i), .reg (tv W Y i), .reg (mv W i), .flag b, .reg 0]

theorem test_run (W X Y i : ℕ) (hi : i ≤ W) :
    LRuns W test (2 * W + 3) (st W X Y i false) (st W X Y i (decide (i < W))) := by
  have h := lt_at (W := W) (st W X Y i false) rl zo mr fl (by decide) 0 (mv W i) false rfl rfl rfl rfl
    (Nat.two_pow_pos W) (mv_lt W i)
  refine h.congr_out ?_
  rw [mv_pos W i hi]
  funext j; fin_cases j <;> rfl

theorem body_run (W X Y i : ℕ) (hi : i < W) (hXY : X * Y < 2 ^ W) :
    LRuns W body (4 * (2 * W + 3) + 5) (st W X Y i true) (st W X Y (i + 1) false) := by
  obtain ⟨ht1, ht2, _⟩ := round_facts W Y i hi
  have hz1 := zv_le W X Y (i + 1)
  have hzs := zv_step W X Y i hi
  have hzW : 2 * zv W X Y i < 2 ^ W := by
    cases h : bv W Y i <;> simp [h] at hzs <;> omega
  have hz0 : zv W X Y i < 2 ^ W := by omega
  have hzm : 2 * zv W X Y i % 2 ^ W = 2 * zv W X Y i := Nat.mod_eq_of_lt hzW
  have hall := (shl_at (W := W) (st W X Y i true) rl mr zo fl (by decide) (mv W i) 0 true rfl rfl rfl rfl
    (mv_lt W i)).seq ((shl_at (W := W) _ rl zr zo fl (by decide) (zv W X Y i) 0 _ (by rfl) (by rfl) (by rfl)
    (by rfl) hz0).seq ((shl_at (W := W) _ rl tr zo fl (by decide) (tv W Y i) 0 _ (by rfl) (by rfl) (by rfl)
    (by rfl) (tv_lt W Y i hi.le)).seq
    (Ite.runs (W := W) (nop 8) (swAt addF false true rl zr xr fl) (nop 8) fl
      (decide (2 ^ W ≤ 2 * tv W Y i)) (nop_lruns _) (by rfl) (ρ := st W X Y (i + 1) false)
      (fun hb => by
        have hb' : bv W Y i = true := ht2 ▸ hb
        rw [hb'] at hzs
        simp only [if_true] at hzs
        exact (add_at (W := W) _ rl zr xr fl (by decide) (2 * zv W X Y i % 2 ^ W) X _ (by rfl) (by rfl)
          (by rfl) (by rfl) (Nat.mod_lt _ (Nat.two_pow_pos W)) (by omega) (by rw [hzm]; omega)).congr_out (by
            funext j; fin_cases j
            · rfl
            · rfl
            · rfl
            · exact congrArg TS.reg (by rw [hzm, hzs])
            · exact congrArg TS.reg ht1
            · exact congrArg TS.reg (mv_succ W i hi)
            · rfl
            · rfl))
      (fun hb => by
        have hb' : bv W Y i = false := ht2 ▸ hb
        rw [hb'] at hzs
        simp only [Bool.false_eq_true, if_false, Nat.add_zero] at hzs
        exact (nop_lruns _).congr_out (by
            funext j; fin_cases j
            · rfl
            · rfl
            · rfl
            · exact congrArg TS.reg (by rw [hzm, hzs])
            · exact congrArg TS.reg ht1
            · exact congrArg TS.reg (mv_succ W i hi)
            · exact congrArg TS.flag hb
            · rfl)))))
  exact hall.enlarge (by omega)

theorem loop_run (W X Y : ℕ) (hXY : X * Y < 2 ^ W) :
    LRuns W loop ((W + 1) * ((2 * W + 3) + (4 * (2 * W + 3) + 5) + 2)) (st W X Y 0 false)
      (st W X Y W false) := by
  have h := Loop.runs test body fl (fun i => st W X Y i false) (fun i => st W X Y i (decide (i < W))) W
    (fun i hi => test_run W X Y i hi) (fun i _ => rfl)
    (fun i hi => by
      have hb := body_run W X Y i hi hXY
      rwa [show decide (i < W) = true by simp [hi]])
  refine h.weaken ?_
  intro j H A hj
  fin_cases j <;> simp [st] at hj ⊢ <;> exact hj

theorem mv_zero (W : ℕ) (hW : 1 ≤ W) : mv W 0 = 1 := by
  unfold mv; rw [pow_zero, Nat.mod_eq_of_lt (Nat.one_lt_two_pow_iff.mpr (by omega))]

/-- The whole multiplication. -/
theorem run (W X Y z t m : ℕ) (b : Bool) (hY : Y < 2 ^ W) (hXY : X * Y < 2 ^ W) (hW : 1 ≤ W) :
    LRuns W machine (13 * W * W + 60 * W + 40)
      ![.ruler, .reg X, .reg Y, .reg z, .reg t, .reg m, .flag b, .reg 0]
      ![.ruler, .reg X, .reg Y, .reg (X * Y), .reg (tv W Y W), .reg (mv W W), .flag false, .reg 0] := by
  have h1W : 0 + 1 < 2 ^ W := by have := Nat.one_lt_two_pow_iff.mpr (show W ≠ 0 by omega); omega
  have s1234 := (zero_at (W := W) (![.ruler, .reg X, .reg Y, .reg z, .reg t, .reg m, .flag b, .reg 0] : Fin 8 → TS)
    rl zr zo fl (by decide) z 0 b rfl rfl rfl rfl).seq ((cpy_at (W := W) _ rl tr yr fl (by decide) t Y _
      (by rfl) (by rfl) (by rfl) (by rfl) hY).seq ((zero_at (W := W) _ rl mr zo fl (by decide) m 0 _
      (by rfl) (by rfl) (by rfl) (by rfl)).seq (inc_at (W := W) _ rl mr zo fl (by decide) 0 0 _
      (by rfl) (by rfl) (by rfl) (by rfl) rfl h1W)))
  have hall := (s1234.congr_out (σ'' := st W X Y 0 false) (by
      funext j; fin_cases j
      · rfl
      · rfl
      · rfl
      · exact congrArg TS.reg (zv_zero W X Y hY).symm
      · exact congrArg TS.reg (tv_zero W Y hY).symm
      · exact congrArg TS.reg (mv_zero W hW).symm
      · rfl
      · rfl)).seq (loop_run W X Y hXY)
  refine (hall.congr_out ?_).enlarge ?_
  · funext j; fin_cases j
    · rfl
    · rfl
    · rfl
    · exact congrArg TS.reg (zv_W W X Y)
    · rfl
    · rfl
    · rfl
    · rfl
  · nlinarith

theorem tv_W (W Y : ℕ) : tv W Y W = 0 := by unfold tv; simp [Nat.mod_one]
theorem mv_W (W : ℕ) : mv W W = 0 := by unfold mv; simp

/-- The multiplication docked at eight ambient slots: `z := x·y`; the two scratch registers end at `0`. -/
theorem at_run {N W : ℕ} (σ : Fin N → TS) (r x y z t m f o : Fin N)
    (hi : Function.Injective ![r, x, y, z, t, m, f, o]) (X Y z0 t0 m0 : ℕ) (b : Bool)
    (hr : σ r = .ruler) (hx : σ x = .reg X) (hy : σ y = .reg Y) (hz : σ z = .reg z0) (ht : σ t = .reg t0)
    (hm : σ m = .reg m0) (hf : σ f = .flag b) (ho : σ o = .reg 0)
    (hY : Y < 2 ^ W) (hXY : X * Y < 2 ^ W) (hW : 1 ≤ W) :
    LRuns W (RecoveryFocus.machine ![r, x, y, z, t, m, f, o] machine) (13 * W * W + 60 * W + 40) σ
      (Function.update (Function.update (Function.update (Function.update σ z (.reg (X * Y))) t (.reg 0))
        m (.reg 0)) f (.flag false)) := by
  have h := (run W X Y z0 t0 m0 b hY hXY hW).dockK ![r, x, y, z, t, m, f, o] hi σ
    (by intro j; fin_cases j
        · exact hr
        · exact hx
        · exact hy
        · exact hz
        · exact ht
        · exact hm
        · exact hf
        · exact ho) [6, 5, 4, 3]
    (by intro j hj; fin_cases j <;> simp at hj ⊢)
  rw [tv_W, mv_W] at h
  exact h

end Mul

end
end NearCubicWires.PacketsMeta

