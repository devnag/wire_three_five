import Proof.Wire_3_5.Primitive.SeedFix.C4KWo
import Proof.Wire_3_5.UnionMachine.EwLevel

/-! # C4KW, part 15: stage B2's level loop (the factors `W_j^{2t}` over a range of levels)

B2's layout (`WState 5 48`): streams `0` the output, `1 2 3` the inputs `1^t, 1^J, 1^{B*}`, `4 5` the words `P`, `C`;
registers `0 … 19` the level window's (`EwLevel.twW`: `t`, `s = ⌊√(t·B*)⌋`, the level `j`, the window out on `7`),
`20 … 25` the square root's, `26 … 33` the binary writer's, `34 35` the passes' flag and counter, then
`J, B*, 2t`, the level counters, the power counter, the addition counter, the factor `w`, two temporaries, the
held-back zeros. **`rng_step`**, **`rng_loop`**: for `n` levels from `j₀`, `P := p₀·Π_{i<n} W_{j₀+i}^{2t}`
(`W_j = twOf t s j = 16t + 20((s+1)/2^{⌊j/2⌋} + 1)`, filt:majorant, P3:2150-2157).

Paper quantity of the main type: the cleared weights' factors `W_j^{2t}` (P3:2280-2281). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires.WireExponent3_5.UnionMachine.EwLevel (twW twW_spec twOf twMax twOf_le twCost)

/-! ## The layout -/

abbrev sP : Fin 6 := 4
abbrev sC : Fin 6 := 5

/-- The level window's registers `0 … 19`. -/
def Vr : Fin 20 ↪ Fin 48 := ⟨fun i => ⟨i.val, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

@[simp] theorem Vr_apply (i : Fin 20) : Vr i = ⟨i.val, by omega⟩ := rfl

abbrev rF : Fin 48 := 34
abbrev rR : Fin 48 := 35
abbrev rJ : Fin 48 := 36
abbrev rB : Fin 48 := 37
abbrev rt2 : Fin 48 := 38
abbrev rL : Fin 48 := 39
abbrev rl : Fin 48 := 40
abbrev rE : Fin 48 := 41
abbrev rk : Fin 48 := 42
abbrev rc : Fin 48 := 43
abbrev rW : Fin 48 := 44
abbrev rT : Fin 48 := 45
abbrev rU : Fin 48 := 46
abbrev rz : Fin 48 := 47

/-- One level: its window into `w`, `P := P·w^{2t}`, `w := 0`, the next level. -/
def jBody : WM 5 48 :=
  .seq (.dec rE) (.seq (twW Vr) (.seq (WM.move (Vr 7) rW) (.seq (powU sP sC rF rR rW rc rT rk rt2)
    (.seq (WM.clear rW) (.inc (Vr 2))))))

/-- The levels loop. -/
def rngW : WM 5 48 := .whr rE jBody

/-- The product of the factors over `n` levels from `j₀`. -/
def fac (t s j0 n : ℕ) : ℕ := ∏ i ∈ Finset.range n, twOf t s (j0 + i) ^ (2 * t)

/-- **The levels loop's invariant** after `k` of its `n` levels (relative to its entry `σ`). -/
structure RJ (σ : WState 5 48) (wd t s j0 n p0 k : ℕ) (τ : WState 5 48) : Prop where
  P : NumOn τ sP wd (p0 * fac t s j0 k)
  C : NumOn τ sC wd (p0 * fac t s j0 k)
  j : τ.val (Vr 2) = j0 + k
  e : τ.val rE = n - k
  vl : ∀ r, r ≠ Vr 2 → r ≠ rE → τ.val r = σ.val r
  st : ∀ i, i ≠ sP → i ≠ sC → τ.st i = σ.st i
  sh : ∀ i, i ≠ sP → i ≠ sC → τ.sh i = σ.sh i
  cl : τ.cell = σ.cell

/-- The loop's entry conditions on `σ`. -/
structure RJin (σ : WState 5 48) (t s : ℕ) : Prop where
  t0 : σ.val (Vr 0) = t
  s1 : σ.val (Vr 1) = s
  z : ∀ i : Fin 20, 3 ≤ i.val → σ.val (Vr i) = 0
  f : σ.val rF = 0
  r : σ.val rR = 0
  w : σ.val rW = 0
  c : σ.val rc = 0
  tt : σ.val rT = 0
  k : σ.val rk = 0
  m : σ.val rt2 = 2 * t

/-- The loop's per-level cost. -/
def jCost (wd t s J : ℕ) : ℕ :=
  twCost t s J + 7 * twMax t s + powUCost wd (twMax t s) (2 * t) + 3 * twMax t s + 20

theorem fac_succ (t s j0 k : ℕ) : fac t s j0 (k + 1) = fac t s j0 k * twOf t s (j0 + k) ^ (2 * t) := by
  unfold fac; rw [Finset.prod_range_succ]

theorem powUCost_mono (W v v' e : ℕ) (h : v ≤ v') : powUCost W v e ≤ powUCost W v' e := by
  unfold powUCost mulUCost
  have : (v + 3) * (41 * W + 30) ≤ (v' + 3) * (41 * W + 30) := Nat.mul_le_mul_right _ (by omega)
  have : e * ((v + 3) * (41 * W + 30) + 18 * v + 4) ≤ e * ((v' + 3) * (41 * W + 30) + 18 * v' + 4) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **One level.** -/
theorem rng_step (cap : ℕ) (σ : WState 5 48) (wd t s J j0 n p0 k : ℕ) (hin : RJin σ t s) (hk : k < n)
    (hJ : j0 + n ≤ J + 1) (hlt : p0 * fac t s j0 (k + 1) < 2 ^ wd)
    (hcap : 2 ^ (J + 1) + J + s + 1000 * (t + s + 2) + 2 * wd + 2 * t + twMax t s + 1 ≤ cap)
    (τ : WState 5 48) (h : RJ σ wd t s j0 n p0 k τ) :
    ∃ τ' : WState 5 48, ∃ c, WExec cap jBody τ τ' c ∧ c ≤ jCost wd t s J ∧ RJ σ wd t s j0 n p0 (k + 1) τ' := by
  have hW1 : 1 ≤ twOf t s (j0 + k) := by
    have : 20 ≤ 20 * ((s + 1) / 2 ^ ((j0 + k) / 2) + 1) := Nat.le_mul_of_pos_right 20 (Nat.succ_pos _)
    unfold twOf; omega
  have hWm := twOf_le t s (j0 + k)
  have hjJ : j0 + k ≤ J := by omega
  have hpow : 2 ^ (j0 + k + 1) ≤ 2 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have g1 : 1 ≤ 2 ^ (J + 1) := Nat.one_le_two_pow
  have g2 : 1 ≤ 2 ^ (j0 + k + 1) := Nat.one_le_two_pow
  have hJc : J + 1 ≤ cap := by omega
  have hWc : twMax t s + 1 ≤ cap := by omega
  have hwdc : 2 * wd + 1 ≤ cap := by omega
  have htc : 2 * t + 1 ≤ cap := by omega
  have htw : 2 ^ (j0 + k + 1) + (j0 + k) + s + 1000 * (t + s + 2) ≤ cap := by omega
  -- dec
  have t1 := WExec.dec (cap := cap) rE τ (by rw [h.e]; exact le_trans (Nat.sub_le n k) (by omega))
  set τ1 := τ.setv rE (τ.val rE - 1) with hτ1
  -- the window
  obtain ⟨n2, t2, hn2⟩ := twW_spec cap Vr τ1 t s (j0 + k)
    (by rw [hτ1]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), h.vl _ (by decide) (by decide),
      hin.t0])
    (by rw [hτ1]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), h.vl _ (by decide) (by decide),
      hin.s1])
    (by rw [hτ1]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), h.j])
    (fun i hi => by
      rw [hτ1]; simp only [WState.setv_val]
      rw [Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega),
        h.vl _ (by intro e; have := congrArg Fin.val e; simp at this; omega)
          (by intro e; have := congrArg Fin.val e; simp at this; omega), hin.z i hi])
    htw
  set τ2 := τ1.setv (Vr 7) (twOf t s (j0 + k)) with hτ2
  -- move the window into `w`
  have hτ2w : τ2.val rW = 0 := by
    rw [hτ2, hτ1]; simp (config := {decide := true}) only [WState.setv_val, Function.update_apply, Vr_apply, ite_false]
    rw [h.vl _ (by decide) (by decide), hin.w]
  have hτ27 : τ2.val (Vr 7) = twOf t s (j0 + k) := by rw [hτ2]; simp
  have t3 := wmove_spec cap (Vr 7) rW (by decide) (twOf t s (j0 + k)) τ2 hτ27 (by rw [hτ27]; omega)
    (by rw [hτ2w, hτ27]; omega)
  set τ3 := (τ2.setv (Vr 7) 0).setv rW (τ2.val rW + τ2.val (Vr 7)) with hτ3
  have hτ3w : τ3.val rW = twOf t s (j0 + k) := by
    rw [hτ3]; simp only [WState.setv_val, Function.update_self]; rw [hτ2w, hτ27, Nat.zero_add]
  have hv3 : ∀ r, r ≠ rW → r ≠ Vr 7 → r ≠ rE → τ3.val r = τ.val r := fun r h1 h2 h3 => by
    rw [hτ3, hτ2, hτ1]; simp only [WState.setv_val]
    rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h2, Function.update_of_ne h3]
  -- the power
  have t4 := powU_spec cap wd (P := sP) (C := sC) (F := rF) (R := rR) (w := rW) (c := rc) (T := rT) (k := rk) (m := rt2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    τ3 (p0 * fac t s j0 k) (twOf t s (j0 + k)) (2 * t) hW1 h.P h.C
    (by rw [hv3 _ (by decide) (by decide) (by decide), h.vl _ (by decide) (by decide), hin.f])
    (by rw [hv3 _ (by decide) (by decide) (by decide), h.vl _ (by decide) (by decide), hin.r]) hτ3w
    (by rw [hv3 _ (by decide) (by decide) (by decide), h.vl _ (by decide) (by decide), hin.c])
    (by rw [hv3 _ (by decide) (by decide) (by decide), h.vl _ (by decide) (by decide), hin.tt])
    (by rw [hv3 _ (by decide) (by decide) (by decide), h.vl _ (by decide) (by decide), hin.k])
    (by rw [hv3 _ (by decide) (by decide) (by decide), h.vl _ (by decide) (by decide), hin.m])
    (by rw [Nat.mul_assoc, ← fac_succ]; exact hlt) (by omega) (by omega) (by omega)
  set v' := p0 * fac t s j0 k * twOf t s (j0 + k) ^ (2 * t) with hv'
  set τ4 := (τ3.sets sC (frame (binary wd v'))).sets sP (frame (binary wd v')) with hτ4
  -- clear `w`, next level
  have hτ4w : τ4.val rW = twOf t s (j0 + k) := hτ3w
  have t5 := wclear_spec cap rW (twOf t s (j0 + k)) τ4 hτ4w (by rw [hτ4w]; omega)
  set τ5 := τ4.setv rW 0 with hτ5
  have hv5 : ∀ r, r ≠ rW → r ≠ Vr 7 → r ≠ rE → τ5.val r = τ.val r := fun r h1 h2 h3 => by
    rw [hτ5]; simp only [WState.setv_val]; rw [Function.update_of_ne h1]; exact hv3 r h1 h2 h3
  have hτ5j : τ5.val (Vr 2) = j0 + k := by rw [hv5 _ (by decide) (by decide) (by decide), h.j]
  have t6 := WExec.inc (cap := cap) (Vr 2) τ5 (by rw [hτ5j]; omega)
  refine ⟨_, _, WExec.seq t1 (WExec.seq t2 (WExec.seq t3 (WExec.seq t4 (WExec.seq t5 t6)))), ?_, ?_⟩
  · have hpc := powUCost_mono wd (twOf t s (j0 + k)) (twMax t s) (2 * t) hWm
    have htc := UnionMachine.EwLevel.twCost_mono t s (j0 + k) J (by omega)
    unfold jCost; omega
  · have e4 : v' = p0 * fac t s j0 (k + 1) := by rw [hv', fac_succ, Nat.mul_assoc]
    have hτ5E : τ5.val rE = n - (k + 1) := by
      rw [hτ5]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide)]
      show τ3.val rE = _
      rw [hτ3]; simp only [WState.setv_val]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hτ2]
      simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), hτ1]
      simp only [WState.setv_val, Function.update_self]; rw [h.e]; omega
    have hτ5W : τ5.val rW = σ.val rW := by rw [hτ5]; simp [hin.w]
    have hτ57 : τ5.val (Vr 7) = σ.val (Vr 7) := by
      rw [hτ5]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide)]
      show τ3.val (Vr 7) = _
      rw [hτ3]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_self,
        hin.z 7 (by decide)]
    refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_, ?_⟩
    · rw [← e4]; exact ⟨by simp [hτ5, hτ4, WState.sets], h.P.2⟩
    · rw [← e4]; exact ⟨by simp [hτ5, hτ4, WState.sets, Function.update_apply], h.C.2⟩
    · simp only [WState.setv_val, Function.update_self]; omega
    · simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), hτ5E]
    · simp only [WState.setv_val]
      rw [Function.update_of_ne h1]
      by_cases hr : r = rW
      · rw [hr, hτ5W]
      · by_cases h7 : r = Vr 7
        · rw [h7, hτ57]
        · rw [hv5 r hr h7 h2, h.vl r h1 h2]
    · show ((τ3.sets sC (frame (binary wd v'))).sets sP (frame (binary wd v'))).st i = σ.st i
      simp only [WState.sets_st]
      rw [Function.update_of_ne h1, Function.update_of_ne h2]
      exact h.st i h1 h2
    · exact h.sh i h1 h2
    · exact h.cl

theorem fac_mono (t s j0 a b : ℕ) (h : a ≤ b) : fac t s j0 a ≤ fac t s j0 b := by
  unfold fac
  apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.range_subset_range.mpr h)
  intro i _ _
  have : 1 ≤ twOf t s (j0 + i) := by
    have : 20 ≤ 20 * ((s + 1) / 2 ^ ((j0 + i) / 2) + 1) := Nat.le_mul_of_pos_right 20 (Nat.succ_pos _)
    unfold twOf; omega
  exact Nat.one_le_pow _ _ this

/-- **The levels loop.** -/
theorem rng_loop (cap : ℕ) (σ : WState 5 48) (wd t s J j0 n p0 : ℕ) (hin : RJin σ t s) (hJ : j0 + n ≤ J + 1)
    (hlt : p0 * fac t s j0 n < 2 ^ wd)
    (hcap : 2 ^ (J + 1) + J + s + 1000 * (t + s + 2) + 2 * wd + 2 * t + twMax t s + 1 ≤ cap) :
    ∀ (m k : ℕ) (τ : WState 5 48), k + m = n → RJ σ wd t s j0 n p0 k τ →
      ∃ τ' : WState 5 48, WExec cap rngW τ τ' (m * (jCost wd t s J + 2) + 1) ∧ RJ σ wd t s j0 n p0 n τ'
  | 0, k, τ, hkm, h => by
    have hk : k = n := by omega
    subst hk
    exact ⟨τ, WExec.mono (WExec.whrF (by rw [h.e]; omega)) (by omega), h⟩
  | m + 1, k, τ, hkm, h => by
    have hl : p0 * fac t s j0 (k + 1) < 2 ^ wd :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ (fac_mono t s j0 _ _ (by omega))) hlt
    obtain ⟨τ1, c, t1, hc, h1⟩ := rng_step cap σ wd t s J j0 n p0 k hin (by omega) hJ hl hcap τ h
    obtain ⟨τ2, t2, h2⟩ := rng_loop cap σ wd t s J j0 n p0 hin hJ hlt hcap m (k + 1) τ1 (by omega) h1
    refine ⟨τ2, WExec.mono (WExec.whrT (by rw [h.e]; omega) t1 t2) ?_, h2⟩
    rw [Nat.add_mul, Nat.one_mul]; omega

end NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
