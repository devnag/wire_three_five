import Proof.Wire_3_5.Primitive.SeedFix.C4HkB

/-! # The HASH stage, part 3: the pre-loop writer's word program

P3:3011-3016 ("The processor writes [...] before the loop") and P3:2327-2336 (the loop's `s_h = 2t·ℓ₀` decisions):
before the decision loop the HASH stage needs, next to the setup's exit bank (C4H-a's `HBank2`), the loop's initial prefix
`frame [] = [false]`, its counter word `false :: 1^{s_h}` (`CompareMachine.word s_h`), and a copy of the framed request
for the finisher. **`preW`** (streams: `0` the framed request, `1` its copy, `2` the Hb bank's ruler `frame 1^L`,
`L = T2 + T2·ℓ`, `3` its `frame 1^{T2}`, `4` the prefix, `5` the counter): the copy (`plW` and a terminator), the
prefix, then the counter from the ruler with its first `T2` ones skipped in lockstep with `1^{T2}` (`lockW`).

* `lockW`, `lock_loop`, `lock_spec`, `preW`, `preSt`, **`preW_spec`**.

Paper quantity of the main type: the loop's entry words (the prefix, the counter `s_h`) and the request's copy. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hk
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ}

/-- Skip the pairs of the framed word on `t`, moving `s` in lockstep. -/
def lockW (t s : Fin (ns + 1)) : WM ns nr := .whs t (.seq (.fwd t) (.seq (.fwd t) (.seq (.fwd s) (.fwd s))))

theorem lock_loop (cap : ℕ) (σ : WState ns nr) (t s : Fin (ns + 1)) (hts : t ≠ s) (y : List Bool)
    (hy : σ.st t = frame y) (a : ℕ) :
    ∀ (v u : List Bool), u ++ v = y →
      WExec cap (lockW t s) ((σ.seth t (2 * u.length)).seth s (a + 2 * u.length))
        ((σ.seth t (2 * y.length)).seth s (a + 2 * y.length)) (9 * v.length + 1)
  | [], u, hu => by
    rw [List.append_nil] at hu
    subst hu
    refine WExec.whsF ?_
    show readTapeBit (((σ.seth t (2 * u.length)).seth s (a + 2 * u.length)).st t)
      (((σ.seth t (2 * u.length)).seth s (a + 2 * u.length)).sh t) = false
    simp only [WState.seth_st, WState.seth_sh, Function.update_of_ne hts, Function.update_self]
    rw [hy]
    have e : frame u = u.flatMap (fun b => [true, b]) ++ [false] := by
      have := C4Hf.frame_append_pairs u []
      rw [List.append_nil] at this
      exact this
    rw [e]
    have := C4Hf.read_pairs u [false] 0
    rw [Nat.add_zero] at this
    rw [this]; rfl
  | b :: v, u, hu => by
    have hw : σ.st t = u.flatMap (fun b => [true, b]) ++ (true :: b :: frame v) := by
      rw [hy, ← hu, C4Hf.frame_append_pairs]; rfl
    have r0 : readTapeBit (σ.st t) (2 * u.length) = true := by
      rw [hw]; have := C4Hf.read_pairs u (true :: b :: frame v) 0; rw [Nat.add_zero] at this; rw [this]; rfl
    set σ0 := (σ.seth t (2 * u.length)).seth s (a + 2 * u.length) with hσ0
    have t1 := WExec.fwd (cap := cap) t σ0
    have t2 := WExec.fwd (cap := cap) t (σ0.seth t (σ0.sh t + 1))
    have t3 := WExec.fwd (cap := cap) s ((σ0.seth t (σ0.sh t + 1)).seth t ((σ0.seth t (σ0.sh t + 1)).sh t + 1))
    have t4 := WExec.fwd (cap := cap) s (((σ0.seth t (σ0.sh t + 1)).seth t ((σ0.seth t (σ0.sh t + 1)).sh t + 1)).seth s
      (((σ0.seth t (σ0.sh t + 1)).seth t ((σ0.seth t (σ0.sh t + 1)).sh t + 1)).sh s + 1))
    have hend : ((((σ0.seth t (σ0.sh t + 1)).seth t ((σ0.seth t (σ0.sh t + 1)).sh t + 1)).seth s
        (((σ0.seth t (σ0.sh t + 1)).seth t ((σ0.seth t (σ0.sh t + 1)).sh t + 1)).sh s + 1)).seth s
        ((((σ0.seth t (σ0.sh t + 1)).seth t ((σ0.seth t (σ0.sh t + 1)).sh t + 1)).seth s
        (((σ0.seth t (σ0.sh t + 1)).seth t ((σ0.seth t (σ0.sh t + 1)).sh t + 1)).sh s + 1)).sh s + 1)) =
        (σ.seth t (2 * (u ++ [b]).length)).seth s (a + 2 * (u ++ [b]).length) := by
      rw [hσ0]
      apply WState.eq
      · funext j
        by_cases hjs : j = s
        · subst hjs; simp [WState.seth, Ne.symm hts]; ring
        · by_cases hjt : j = t
          · subst hjt; simp [WState.seth, hjs]; ring
          · simp [WState.seth, hjs, hjt]
      · rfl
      · rfl
      · rfl
    rw [hend] at t4
    have tb : WExec cap (.seq (.fwd t) (.seq (.fwd t) (.seq (.fwd s) (.fwd s))) : WM ns nr) σ0
        ((σ.seth t (2 * (u ++ [b]).length)).seth s (a + 2 * (u ++ [b]).length)) 7 :=
      WExec.cast cap (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 t4))) rfl (by omega)
    have hw0 : wbit σ0 t = true := by
      show readTapeBit (σ0.st t) (σ0.sh t) = true
      rw [hσ0]
      simp only [WState.seth_st, WState.seth_sh, Function.update_of_ne hts, Function.update_self]
      exact r0
    have hu' : (u ++ [b]) ++ v = y := by rw [← hu]; simp
    have ih := lock_loop cap σ t s hts y hy a v (u ++ [b]) hu'
    refine WExec.cast cap (WExec.whsT hw0 tb ih) rfl ?_
    simp only [List.length_cons]
    omega

/-- **The lockstep skip**: from `t`'s head at `0` and `s`'s at `a`, both advanced by `2|y|`. -/
theorem lock_spec (cap : ℕ) (σ : WState ns nr) (t s : Fin (ns + 1)) (hts : t ≠ s) (y : List Bool)
    (hy : σ.st t = frame y) (ht0 : σ.sh t = 0) (a : ℕ) (hsa : σ.sh s = a) :
    WExec cap (lockW t s) σ ((σ.seth t (2 * y.length)).seth s (a + 2 * y.length)) (9 * y.length + 1) := by
  have e : (σ.seth t (2 * ([] : List Bool).length)).seth s (a + 2 * ([] : List Bool).length) = σ := by
    apply WState.eq
    · funext j
      by_cases hjs : j = s
      · subst hjs; simp [WState.seth, hsa]
      · by_cases hjt : j = t
        · subst hjt; simp [WState.seth, hjs, ht0]
        · simp [WState.seth, hjs, hjt]
    · rfl
    · rfl
    · rfl
  have h := lock_loop cap σ t s hts y hy a y [] rfl
  rw [e] at h
  exact h

/-- **The pre-loop writer** (streams: `0` the request, `1` its copy, `2` the ruler, `3` `1^{T2}`, `4` the prefix,
`5` the counter). -/
def preW : WM 5 0 :=
  .seq (plW 0 1 [true]) (.seq (wlist 1 [false]) (.seq (wlist 4 [false]) (.seq (wlist 5 [false])
    (.seq (lockW 3 2) (plW 2 5 [])))))

/-- The writer's entry state. -/
def preSt (w : List Bool) (L T2 : ℕ) : WState 5 0 :=
  ⟨fun _ => 0, ![frame w, [], frame (List.replicate L true), frame (List.replicate T2 true), [], []], Fin.elim0,
    false⟩

/-- The writer's steps. -/
def preCost (w : List Bool) (T2 m : ℕ) : ℕ := 15 * w.length + 9 * T2 + 11 * m + 21

theorem preW_spec (w : List Bool) (T2 m : ℕ) :
    ∃ τ : WState 5 0, WExec 0 preW (preSt w (T2 + m) T2) τ (preCost w T2 m) ∧
      τ.st 0 = frame w ∧ τ.st 1 = frame w ∧ τ.st 2 = frame (List.replicate (T2 + m) true) ∧
      τ.st 3 = frame (List.replicate T2 true) ∧ τ.st 4 = [false] ∧ τ.st 5 = false :: List.replicate m true := by
  set σ0 := preSt w (T2 + m) T2 with hσ0
  -- the copy
  have t1 := pl_spec 0 σ0 0 1 (by decide) [true] w rfl rfl rfl
  set σ1 := pSt σ0 0 1 [true] 0 w with hσ1
  have s1_1 : σ1.sh 1 = (σ1.st 1).length := by
    rw [hσ1]; simp only [pSt, WState.seth_sh, WState.seth_st]
    rw [Function.update_of_ne (by decide), apd_sh_d, apd_st_d, List.length_append]
  have t2 := wlist_spec 0 1 [false] σ1 s1_1
  set σ2 := apd σ1 1 [false] with hσ2
  have s2_4 : σ2.sh 4 = (σ2.st 4).length := by
    rw [hσ2, apd_sh_ne _ _ _ (by decide), apd_st_ne _ _ _ (by decide), hσ1]
    simp only [pSt, WState.seth_sh, WState.seth_st]
    rw [Function.update_of_ne (by decide), apd_sh_ne _ _ _ (by decide), apd_st_ne _ _ _ (by decide)]; rfl
  have t3 := wlist_spec 0 4 [false] σ2 s2_4
  set σ3 := apd σ2 4 [false] with hσ3
  have s3_5 : σ3.sh 5 = (σ3.st 5).length := by
    rw [hσ3, apd_sh_ne _ _ _ (by decide), apd_st_ne _ _ _ (by decide), hσ2, apd_sh_ne _ _ _ (by decide),
      apd_st_ne _ _ _ (by decide), hσ1]
    simp only [pSt, WState.seth_sh, WState.seth_st]
    rw [Function.update_of_ne (by decide), apd_sh_ne _ _ _ (by decide), apd_st_ne _ _ _ (by decide)]; rfl
  have t4 := wlist_spec 0 5 [false] σ3 s3_5
  set σ4 := apd σ3 5 [false] with hσ4
  -- the streams 2, 3 are untouched so far
  have st2 : σ4.st 2 = frame (List.replicate (T2 + m) true) := by
    rw [hσ4, apd_st_ne _ _ _ (by decide), hσ3, apd_st_ne _ _ _ (by decide), hσ2, apd_st_ne _ _ _ (by decide), hσ1]
    simp only [pSt, WState.seth_st]; rw [apd_st_ne _ _ _ (by decide)]; rfl
  have st3 : σ4.st 3 = frame (List.replicate T2 true) := by
    rw [hσ4, apd_st_ne _ _ _ (by decide), hσ3, apd_st_ne _ _ _ (by decide), hσ2, apd_st_ne _ _ _ (by decide), hσ1]
    simp only [pSt, WState.seth_st]; rw [apd_st_ne _ _ _ (by decide)]; rfl
  have sh2 : σ4.sh 2 = 0 := by
    rw [hσ4, apd_sh_ne _ _ _ (by decide), hσ3, apd_sh_ne _ _ _ (by decide), hσ2, apd_sh_ne _ _ _ (by decide), hσ1]
    simp only [pSt, WState.seth_sh]; rw [Function.update_of_ne (by decide), apd_sh_ne _ _ _ (by decide)]; rfl
  have sh3 : σ4.sh 3 = 0 := by
    rw [hσ4, apd_sh_ne _ _ _ (by decide), hσ3, apd_sh_ne _ _ _ (by decide), hσ2, apd_sh_ne _ _ _ (by decide), hσ1]
    simp only [pSt, WState.seth_sh]; rw [Function.update_of_ne (by decide), apd_sh_ne _ _ _ (by decide)]; rfl
  -- the lockstep skip
  have t5 := lock_spec 0 σ4 3 2 (by decide) (List.replicate T2 true) st3 sh3 0 sh2
  simp only [List.length_replicate, Nat.zero_add] at t5
  set σ5 := (σ4.seth 3 (2 * T2)).seth 2 (2 * T2) with hσ5
  -- the counter
  have st2' : σ5.st 2 = frame (List.replicate T2 true ++ List.replicate m true) := by
    rw [hσ5]; simp only [WState.seth_st]; rw [st2, List.replicate_add]
  have t6 := pl_loop 0 σ5 2 5 (by decide) [] (List.replicate T2 true) (List.replicate m true) st2'
    (List.replicate m true) [] rfl
  have e5 : pSt σ5 2 5 [] (List.replicate T2 true).length [] = σ5 := by
    have h55 : σ5.sh 5 = (σ5.st 5).length := by
      rw [hσ5]; simp only [WState.seth_sh, WState.seth_st]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hσ4, apd_sh_d, apd_st_d,
        List.length_append]
    unfold pSt
    simp only [List.flatMap_nil, List.length_nil, List.length_replicate, Nat.add_zero]
    rw [apd_nil σ5 5 h55]
    apply WState.eq
    · funext j; by_cases hj : j = 2
      · subst hj; simp [WState.seth, hσ5]
      · simp [WState.seth, Function.update_of_ne hj]
    · rfl
    · rfl
    · rfl
  rw [e5] at t6
  refine ⟨_, WExec.cast 0 (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 (WExec.seq t4 (WExec.seq t5 t6))))) rfl
    (by simp [preCost]; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [pSt, WState.seth_st]
    rw [apd_st_ne _ _ _ (by decide), hσ5]
    simp only [WState.seth_st]
    rw [hσ4, apd_st_ne _ _ _ (by decide), hσ3, apd_st_ne _ _ _ (by decide), hσ2, apd_st_ne _ _ _ (by decide), hσ1]
    simp only [pSt, WState.seth_st]; rw [apd_st_ne _ _ _ (by decide)]; rfl
  · simp only [pSt, WState.seth_st]
    rw [apd_st_ne _ _ _ (by decide), hσ5]
    simp only [WState.seth_st]
    rw [hσ4, apd_st_ne _ _ _ (by decide), hσ3, apd_st_ne _ _ _ (by decide), hσ2, apd_st_d, hσ1]
    simp only [pSt, WState.seth_st]
    rw [apd_st_d]
    have := C4Hf.frame_append_pairs w []
    rw [List.append_nil] at this
    rw [this, hσ0]
    rfl
  · simp only [pSt, WState.seth_st]
    rw [apd_st_ne _ _ _ (by decide), hσ5]
    simp only [WState.seth_st]
    exact st2
  · simp only [pSt, WState.seth_st]
    rw [apd_st_ne _ _ _ (by decide), hσ5]
    simp only [WState.seth_st]
    exact st3
  · simp only [pSt, WState.seth_st]
    rw [apd_st_ne _ _ _ (by decide), hσ5]
    simp only [WState.seth_st]
    rw [hσ4, apd_st_ne _ _ _ (by decide), hσ3, apd_st_d, hσ2, apd_st_ne _ _ _ (by decide), hσ1]
    simp only [pSt, WState.seth_st]; rw [apd_st_ne _ _ _ (by decide)]; rfl
  · simp only [pSt, WState.seth_st]
    rw [apd_st_d, hσ5]
    simp only [WState.seth_st]
    rw [hσ4, apd_st_d, hσ3, apd_st_ne _ _ _ (by decide), hσ2, apd_st_ne _ _ _ (by decide), hσ1]
    simp only [pSt, WState.seth_st]; rw [apd_st_ne _ _ _ (by decide)]
    simp [preSt, List.flatMap_replicate]
    rw [hσ0]
    rfl

end NearCubicWires.WireExponent3_5.PrimT.C4Hk
