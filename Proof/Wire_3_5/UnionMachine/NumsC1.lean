import Proof.Wire_3_5.UnionMachine.NumsPh2Base
import Proof.Wire_3_5.Primitive.Writers.UnaryArith
import Proof.Wire_3_5.Primitive.Writers.StarNums

/-! # NW phase (c), part 1: the register kit (a power by repeated multiplication, a list of clears)

Phase (c) computes `T_f = KT·(n+2)^{ZT}` (the numbers' width, `Sd.R.Tf`) in a register: `mulStep` (`a := a·m` by
PA's `UnaryArith.mulAddW` into an accumulator, then the accumulator moved back), `powN k` (`a := a·m^k`), and cleans
its scratch registers (`clearL`). Every run is stated by the registers it changes, the rest of the state kept.

* `mulCost`, **`mulStep_spec`**; **`powN_spec`** (`a := a·m^k`, within `k·(60(B+1)(m+1)+1)` steps when every partial
  power is `≤ B ≤ cap`); **`clearL_spec`** (the listed registers `0`, within `|rs|·(3B+2)` steps).

Paper quantity of the main types: the numbers' width `T_f = KT·(n+2)^{ZT}` (the width of `Den`'s binary word,
P3:3044-3048). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsC
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

section Kit
variable {ns nr : ℕ} (cap : ℕ)

/-- `mulAddW`'s five registers `(a, m, t, w, v)` among `R = (a, m, t, u, w, v)`. -/
def eM : Fin 5 ↪ Fin 6 := ⟨![0, 1, 2, 4, 5], by decide⟩

/-- **`a := a·m`**: `t := a·m` (`mulAddW`), `a := 0`, `a := t` (`wcopyR` via `u`), `t := 0`; `R = (a, m, t, u, w, v)`,
the scratch `t, u, w, v` at `0`. -/
def mulStep (R : Fin 6 ↪ Fin nr) : WM ns nr :=
  .seq (UnaryArith.mulAddW (eM.trans R))
    (.seq (WM.clear (R 0)) (.seq (FinalPass.Hash4.wcopyR (R 2) (R 0) (R 3)) (WM.clear (R 2))))

/-- One multiplication's steps. -/
def mulCost (a m : ℕ) : ℕ :=
  m * (18 * a + 8) + 18 * m + 10 + 1 + ((3 * a + 1) + 1 + ((18 * (0 + a * m) + 3) + 1 + (3 * (0 + a * m) + 1)))

theorem mulCost_le (a m B : ℕ) (ha : a ≤ B) : mulCost a m ≤ 60 * (B + 1) * (m + 1) := by
  unfold mulCost
  have h1 : m * (18 * a + 8) = 18 * (a * m) + 8 * m := by ring
  have h2 : 60 * (B + 1) * (m + 1) = 60 * (B * m) + 60 * B + 60 * m + 60 := by ring
  have h3 : a * m ≤ B * m := Nat.mul_le_mul_right _ ha
  rw [h1, h2]
  omega

theorem mulStep_spec (R : Fin 6 ↪ Fin nr) (σ : WState ns nr) (ht : σ.val (R 2) = 0) (hu : σ.val (R 3) = 0)
    (hw : σ.val (R 4) = 0) (hv : σ.val (R 5) = 0) (hcap : σ.val (R 0) * σ.val (R 1) ≤ cap)
    (ha : σ.val (R 0) ≤ cap) (hm : σ.val (R 1) ≤ cap) :
    WExec cap (mulStep R) σ (σ.setv (R 0) (σ.val (R 0) * σ.val (R 1))) (mulCost (σ.val (R 0)) (σ.val (R 1))) := by
  have hne : ∀ {i j : Fin 6}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have n02 := hne (show (0 : Fin 6) ≠ 2 by decide)
  have n20 := hne (show (2 : Fin 6) ≠ 0 by decide)
  have n30 := hne (show (3 : Fin 6) ≠ 0 by decide)
  have n32 := hne (show (3 : Fin 6) ≠ 2 by decide)
  have e0 : (eM.trans R) 0 = R 0 := rfl
  have e1 : (eM.trans R) 1 = R 1 := rfl
  have e2 : (eM.trans R) 2 = R 2 := rfl
  have e3 : (eM.trans R) 3 = R 4 := rfl
  have e4 : (eM.trans R) 4 = R 5 := rfl
  obtain ⟨a, had⟩ : ∃ v, v = σ.val (R 0) := ⟨_, rfl⟩
  obtain ⟨m, hmd⟩ : ∃ v, v = σ.val (R 1) := ⟨_, rfl⟩
  have h1 := UnaryArith.mulAddW_spec cap (eM.trans R) σ (by rw [e3]; exact hw) (by rw [e4]; exact hv)
    (by rw [e1]; exact hm) (by rw [e2, e0, e1, ht]; omega) (by rw [e0]; exact ha)
  rw [e0, e1, e2, ht, ← had, ← hmd] at h1
  obtain ⟨σ1, hσ1⟩ : ∃ s, s = σ.setv (R 2) (0 + a * m) := ⟨_, rfl⟩
  rw [← hσ1] at h1
  have v10 : σ1.val (R 0) = a := by rw [hσ1]; simp [n02, had]
  have v13 : σ1.val (R 3) = 0 := by rw [hσ1]; simp [n32, hu]
  have h2 := wclear_spec cap (R 0) a σ1 v10 (by rw [v10, had]; exact ha)
  obtain ⟨σ2, hσ2⟩ : ∃ s, s = σ1.setv (R 0) 0 := ⟨_, rfl⟩
  rw [← hσ2] at h2
  have v22 : σ2.val (R 2) = 0 + a * m := by rw [hσ2, hσ1]; simp [n20]
  have v20 : σ2.val (R 0) = 0 := by rw [hσ2]; simp
  have v23 : σ2.val (R 3) = 0 := by rw [hσ2]; simp [n30, v13]
  have h3 := FinalPass.Hash4.wcopyR_spec cap (R 2) (R 0) (R 3) n20 (hne (by decide)) (hne (by decide))
    σ2 v20 v23 (by rw [v22, had, hmd]; omega)
  rw [v22] at h3
  obtain ⟨σ3, hσ3⟩ : ∃ s, s = σ2.setv (R 0) (0 + a * m) := ⟨_, rfl⟩
  rw [← hσ3] at h3
  have v32 : σ3.val (R 2) = 0 + a * m := by rw [hσ3]; simp [n20, v22]
  have h4 := wclear_spec cap (R 2) (0 + a * m) σ3 v32 (by rw [v32, had, hmd]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ ?_
  · rw [hσ3, hσ2, hσ1, ← had, ← hmd]
    wgen_eq [n02, n20, ht]
  · rw [← had, ← hmd]; unfold mulCost; omega

/-- **`a := a·m^k`**. -/
def powN (R : Fin 6 ↪ Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | k + 1 => .seq (powN R k) (mulStep R)

theorem powN_spec (R : Fin 6 ↪ Fin nr) (B : ℕ) (hBc : B ≤ cap) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val (R 2) = 0 → σ.val (R 3) = 0 → σ.val (R 4) = 0 → σ.val (R 5) = 0 →
      σ.val (R 1) ≤ cap → (∀ j, j ≤ k → σ.val (R 0) * σ.val (R 1) ^ j ≤ B) →
      ∃ c, WExec cap (powN R k) σ (σ.setv (R 0) (σ.val (R 0) * σ.val (R 1) ^ k)) c ∧
        c ≤ k * (60 * (B + 1) * (σ.val (R 1) + 1) + 1)
  | 0, σ, _, _, _, _, _, _ => by
    refine ⟨0, ?_, by simp⟩
    rw [pow_zero, Nat.mul_one, wsetv_same]
    exact WExec.skip σ
  | k + 1, σ, ht, hu, hw, hv, hm, hB => by
    have hne : ∀ {i j : Fin 6}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
    obtain ⟨c, h1, hc⟩ := powN_spec R B hBc k σ ht hu hw hv hm (fun j hj => hB j (by omega))
    obtain ⟨a, had⟩ : ∃ v, v = σ.val (R 0) := ⟨_, rfl⟩
    obtain ⟨m, hmd⟩ : ∃ v, v = σ.val (R 1) := ⟨_, rfl⟩
    rw [← had, ← hmd] at h1
    rw [← hmd] at hc hm
    have hB' : ∀ j, j ≤ k + 1 → a * m ^ j ≤ B := fun j hj => by rw [had, hmd]; exact hB j hj
    obtain ⟨σ1, hσ1⟩ : ∃ s, s = σ.setv (R 0) (a * m ^ k) := ⟨_, rfl⟩
    rw [← hσ1] at h1
    have w0 : σ1.val (R 0) = a * m ^ k := by rw [hσ1]; simp
    have w1 : σ1.val (R 1) = m := by rw [hσ1]; simp [hne (show (1 : Fin 6) ≠ 0 by decide), hmd]
    have w2 : σ1.val (R 2) = 0 := by rw [hσ1]; simp [hne (show (2 : Fin 6) ≠ 0 by decide), ht]
    have w3 : σ1.val (R 3) = 0 := by rw [hσ1]; simp [hne (show (3 : Fin 6) ≠ 0 by decide), hu]
    have w4 : σ1.val (R 4) = 0 := by rw [hσ1]; simp [hne (show (4 : Fin 6) ≠ 0 by decide), hw]
    have w5 : σ1.val (R 5) = 0 := by rw [hσ1]; simp [hne (show (5 : Fin 6) ≠ 0 by decide), hv]
    have hk : a * m ^ k ≤ B := hB' k (by omega)
    have hk1 : a * m ^ k * m ≤ B := by
      have := hB' (k + 1) le_rfl
      rw [pow_succ, ← Nat.mul_assoc] at this
      exact this
    have h2 := mulStep_spec cap R σ1 w2 w3 w4 w5 (by rw [w0, w1]; omega) (by rw [w0]; omega) (by rw [w1]; exact hm)
    rw [w0, w1] at h2
    refine ⟨_, WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl, ?_⟩
    · rw [hσ1, wsetv_setv, pow_succ, ← Nat.mul_assoc, ← had, ← hmd]
    · rw [← hmd]
      have := mulCost_le (a * m ^ k) m B hk
      have e : (k + 1) * (60 * (B + 1) * (m + 1) + 1) = k * (60 * (B + 1) * (m + 1) + 1) +
          (60 * (B + 1) * (m + 1) + 1) := by ring
      rw [e]
      omega

/-- **Clear a list of registers.** -/
def clearL : List (Fin nr) → WM ns nr
  | [] => .skip
  | r :: rs => .seq (WM.clear r) (clearL rs)

/-- The state with the listed registers `0`. -/
def zeroL (σ : WState ns nr) (rs : List (Fin nr)) : WState ns nr :=
  ⟨σ.sh, σ.st, fun q => if q ∈ rs then 0 else σ.val q, σ.cell⟩

theorem clearL_spec (B : ℕ) (hBc : B ≤ cap) :
    ∀ (rs : List (Fin nr)) (σ : WState ns nr), (∀ r ∈ rs, σ.val r ≤ B) →
      ∃ c, WExec cap (clearL rs) σ (zeroL σ rs) c ∧ c ≤ rs.length * (3 * B + 2)
  | [], σ, _ => ⟨0, by
      have e : zeroL σ [] = σ := by
        refine WState.eq rfl rfl ?_ rfl
        funext q; simp [zeroL]
      rw [e]; exact WExec.skip σ, by simp⟩
  | r :: rs, σ, hB => by
    have h1 := wclear_spec cap r (σ.val r) σ rfl (le_trans (hB r (by simp)) hBc)
    obtain ⟨c, h2, hc⟩ := clearL_spec B hBc rs (σ.setv r 0) (fun q hq => by
      simp only [WState.setv_val, Function.update_apply]
      split_ifs
      · exact Nat.zero_le _
      · exact hB q (by simp [hq]))
    refine ⟨_, WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl, ?_⟩
    · refine WState.eq rfl rfl ?_ rfl
      funext q
      simp only [zeroL, WState.setv_val, Function.update_apply, List.mem_cons]
      by_cases hq : q = r
      · subst hq; simp
      · by_cases hq' : q ∈ rs <;> simp [hq, hq']
    · have := hB r (by simp)
      simp only [List.length_cons]
      nlinarith

end Kit

end NearCubicWires.WireExponent3_5.UnionMachine.NumsC
