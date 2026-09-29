import Proof.Wire_3_5.Primitive.SeedFix.C4HfP

/-! # The HASH stage, part 1: the finisher's word program

`filt:soft`, P3:2327-2336 ("the printed decisions are the fixed hash's bits") and the THR writer's input
(`thrIn = req.word ++ frame hashBits`): the HASH stage ends with `frame (w ++ frame bits)` on its output,
from the framed request `frame w` and the loop's framed decisions `frame bits`. This part is the word program:
`wlist d k` (append the fixed bits `k` to stream `d`), `plW s d k` (for every bit `b` of the framed word on `s`, append
`k ++ [b]` to `d`), and **`finW`** (`plW` on the request with `k = [true]`, on the decisions with `k = [true, true, true]`,
then `[true, false, false]`), with **`finW_spec`**: the output stream holds `frame (w ++ frame bits)`.

Paper quantity of the main type: the THR writer's input word `frame (w ++ frame bits)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hk
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ}

/-- Stream `d` extended by `x`, its head at the end. -/
def apd (σ : WState ns nr) (d : Fin (ns + 1)) (x : List Bool) : WState ns nr :=
  ⟨Function.update σ.sh d ((σ.st d).length + x.length), Function.update σ.st d (σ.st d ++ x), σ.val, σ.cell⟩

theorem apd_nil (σ : WState ns nr) (d : Fin (ns + 1)) (h : σ.sh d = (σ.st d).length) : apd σ d [] = σ := by
  apply WState.eq
  · funext j; by_cases hj : j = d
    · subst hj; simp [apd, h]
    · simp [apd, Function.update_of_ne hj]
  · funext j; by_cases hj : j = d
    · subst hj; simp [apd]
    · simp [apd, Function.update_of_ne hj]
  · rfl
  · rfl

theorem apd_apd (σ : WState ns nr) (d : Fin (ns + 1)) (x y : List Bool) :
    apd (apd σ d x) d y = apd σ d (x ++ y) := by
  apply WState.eq
  · funext j; by_cases hj : j = d
    · subst hj; simp [apd]; ring
    · simp [apd, Function.update_of_ne hj]
  · funext j; by_cases hj : j = d
    · subst hj; simp [apd]
    · simp [apd, Function.update_of_ne hj]
  · rfl
  · rfl

theorem apd_seth (σ : WState ns nr) (s d : Fin (ns + 1)) (hsd : s ≠ d) (x : ℕ) (y : List Bool) :
    apd (σ.seth s x) d y = (apd σ d y).seth s x := by
  apply WState.eq
  · funext j
    by_cases hjd : j = d
    · subst hjd; simp [apd, WState.seth, Ne.symm hsd]
    · by_cases hjs : j = s
      · subst hjs; simp [apd, WState.seth, hjd]
      · simp [apd, WState.seth, hjd, hjs]
  · funext j; simp [apd, WState.seth]
  · rfl
  · rfl

theorem apd_sh_d (σ : WState ns nr) (d : Fin (ns + 1)) (x : List Bool) :
    (apd σ d x).sh d = (σ.st d).length + x.length := by simp [apd]

theorem apd_st_d (σ : WState ns nr) (d : Fin (ns + 1)) (x : List Bool) : (apd σ d x).st d = σ.st d ++ x := by
  simp [apd]

theorem apd_st_ne (σ : WState ns nr) (d j : Fin (ns + 1)) (hj : j ≠ d) (x : List Bool) :
    (apd σ d x).st j = σ.st j := by simp [apd, Function.update_of_ne hj]

theorem apd_sh_ne (σ : WState ns nr) (d j : Fin (ns + 1)) (hj : j ≠ d) (x : List Bool) :
    (apd σ d x).sh j = σ.sh j := by simp [apd, Function.update_of_ne hj]

/-- A write at the end, then a move: the stream extended by one bit. -/
theorem wr_fwd_eq (σ : WState ns nr) (d : Fin (ns + 1)) (b : Bool) (h : σ.sh d = (σ.st d).length) :
    (σ.sets d (σ.st d ++ [b])).seth d (σ.sh d + 1) = apd σ d [b] := by
  apply WState.eq
  · funext j; by_cases hj : j = d
    · subst hj; simp [apd, WState.seth, WState.sets, h]
    · simp [apd, WState.seth, WState.sets, Function.update_of_ne hj]
  · funext j; by_cases hj : j = d
    · subst hj; simp [apd, WState.sets]
    · simp [apd, WState.sets, Function.update_of_ne hj]
  · rfl
  · rfl

/-- Append the fixed bits `k` to stream `d`. -/
def wlist (d : Fin (ns + 1)) : List Bool → WM ns nr
  | [] => .skip
  | c :: k => .seq (.wr d c) (.seq (.fwd d) (wlist d k))

theorem wlist_spec (cap : ℕ) (d : Fin (ns + 1)) : ∀ (k : List Bool) (σ : WState ns nr), σ.sh d = (σ.st d).length →
    WExec cap (wlist d k) σ (apd σ d k) (4 * k.length)
  | [], σ, h => by
    rw [apd_nil σ d h]
    exact WExec.skip σ
  | c :: k, σ, h => by
    have t1 := WExec.wr (cap := cap) d c σ
    rw [h, C4Pipe.write_end] at t1
    have t2 := WExec.fwd (cap := cap) d (σ.sets d (σ.st d ++ [c]))
    have e2 : (σ.sets d (σ.st d ++ [c])).seth d ((σ.sets d (σ.st d ++ [c])).sh d + 1) = apd σ d [c] := by
      rw [WState.sets_sh]; exact wr_fwd_eq σ d c h
    rw [e2] at t2
    have h1 : (apd σ d [c]).sh d = ((apd σ d [c]).st d).length := by
      rw [apd_sh_d, apd_st_d, List.length_append]
    have t3 := wlist_spec cap d k (apd σ d [c]) h1
    rw [apd_apd] at t3
    refine WExec.cast cap (WExec.seq t1 (WExec.seq t2 t3)) rfl ?_
    simp only [List.length_cons]; omega

/-- **Copy with a prefix**: for every bit `b` of the framed word on `s`, append `k ++ [b]` to `d`. -/
def plW (s d : Fin (ns + 1)) (k : List Bool) : WM ns nr :=
  .whs s (.seq (.fwd s) (.seq (wlist d k) (.seq (.ifs s (.wr d true) (.wr d false)) (.seq (.fwd d) (.fwd s)))))

/-- The state after the bits `u`, `o` pairs of `s` consumed before. -/
def pSt (σ : WState ns nr) (s d : Fin (ns + 1)) (k : List Bool) (o : ℕ) (u : List Bool) : WState ns nr :=
  (apd σ d (u.flatMap fun b => k ++ [b])).seth s (2 * (o + u.length))

theorem pl_loop (cap : ℕ) (σ : WState ns nr) (s d : Fin (ns + 1)) (hsd : s ≠ d) (k x w : List Bool)
    (hs : σ.st s = frame (x ++ w)) :
    ∀ (v u : List Bool), u ++ v = w →
      WExec cap (plW s d k) (pSt σ s d k x.length u) (pSt σ s d k x.length w) ((4 * k.length + 11) * v.length + 1)
  | [], u, hu => by
    rw [List.append_nil] at hu
    subst hu
    refine WExec.whsF ?_
    show readTapeBit ((pSt σ s d k x.length u).st s) ((pSt σ s d k x.length u).sh s) = false
    have e1 : (pSt σ s d k x.length u).st s = σ.st s := by
      simp only [pSt, WState.seth_st]; exact apd_st_ne σ d s hsd _
    have e2 : (pSt σ s d k x.length u).sh s = 2 * (x ++ u).length := by simp [pSt, WState.seth]
    rw [e1, e2, hs]
    have e : frame (x ++ u) = (x ++ u).flatMap (fun b => [true, b]) ++ [false] := by
      have := C4Hf.frame_append_pairs (x ++ u) []
      rw [List.append_nil] at this
      exact this
    rw [e]
    have := C4Hf.read_pairs (x ++ u) [false] 0
    rw [Nat.add_zero] at this
    rw [this]; rfl
  | b :: v, u, hu => by
    have hw : σ.st s = (x ++ u).flatMap (fun b => [true, b]) ++ (true :: b :: frame v) := by
      rw [hs, ← hu, ← List.append_assoc, C4Hf.frame_append_pairs]; rfl
    have r0 : readTapeBit (σ.st s) (2 * (x.length + u.length)) = true := by
      rw [hw]; have := C4Hf.read_pairs (x ++ u) (true :: b :: frame v) 0
      rw [Nat.add_zero, List.length_append] at this; rw [this]; rfl
    have r1 : readTapeBit (σ.st s) (2 * (x.length + u.length) + 1) = b := by
      have := C4Hf.read_pairs (x ++ u) (true :: b :: frame v) 1
      rw [List.length_append] at this
      rw [hw, this]; rfl
    set X := u.flatMap fun b => k ++ [b] with hX
    set σ0 := pSt σ s d k x.length u with hσ0
    have s0st : σ0.st s = σ.st s := by rw [hσ0]; simp only [pSt, WState.seth_st]; exact apd_st_ne σ d s hsd _
    have s0sh : σ0.sh s = 2 * (x.length + u.length) := by rw [hσ0]; simp [pSt, WState.seth]
    have s0d : σ0.sh d = (σ0.st d).length := by
      rw [hσ0]; simp only [pSt, WState.seth_st, WState.seth_sh]
      rw [Function.update_of_ne (Ne.symm hsd), apd_sh_d, apd_st_d, List.length_append]
    -- fwd s
    set σ1 := σ0.seth s (2 * (x.length + u.length) + 1) with hσ1
    have t1 : WExec cap (.fwd s : WM ns nr) σ0 σ1 1 := by
      have h := WExec.fwd (cap := cap) s σ0
      rwa [s0sh] at h
    have s1d : σ1.sh d = (σ1.st d).length := by
      rw [hσ1]; simp only [WState.seth_st, WState.seth_sh]; rw [Function.update_of_ne (Ne.symm hsd)]; exact s0d
    -- the prefix bits
    have t2 := wlist_spec cap d k σ1 s1d
    set σ2 := apd σ1 d k with hσ2
    have s2d : σ2.sh d = (σ2.st d).length := by rw [hσ2, apd_sh_d, apd_st_d, List.length_append]
    have s2b : wbit σ2 s = b := by
      show readTapeBit (σ2.st s) (σ2.sh s) = b
      rw [hσ2, apd_st_ne σ1 d s hsd, apd_sh_ne σ1 d s hsd, hσ1]
      simp only [WState.seth_st, WState.seth_sh, Function.update_self]
      rw [s0st]; exact r1
    -- the bit, then the moves
    have hwr : ∀ c : Bool, WExec cap (.wr d c : WM ns nr) σ2 (σ2.sets d (σ2.st d ++ [c])) 1 := by
      intro c
      have h := WExec.wr (cap := cap) d c σ2
      rwa [s2d, C4Pipe.write_end] at h
    have t3 : WExec cap (.ifs s (.wr d true) (.wr d false) : WM ns nr) σ2 (σ2.sets d (σ2.st d ++ [b])) 2 := by
      cases b
      · exact WExec.ifsF s2b (hwr false)
      · exact WExec.ifsT s2b (hwr true)
    have t4 := WExec.fwd (cap := cap) d (σ2.sets d (σ2.st d ++ [b]))
    rw [WState.sets_sh, wr_fwd_eq σ2 d b s2d] at t4
    have t5 := WExec.fwd (cap := cap) s (apd σ2 d [b])
    have hfin : (apd σ2 d [b]).seth s ((apd σ2 d [b]).sh s + 1) = pSt σ s d k x.length (u ++ [b]) := by
      rw [apd_sh_ne σ2 d s hsd, hσ2, apd_sh_ne σ1 d s hsd, hσ1]
      simp only [WState.seth_sh, Function.update_self]
      rw [apd_apd, apd_seth σ0 s d hsd, hσ0]
      unfold pSt
      rw [apd_seth _ s d hsd, apd_apd]
      apply WState.eq
      · funext j
        by_cases hjs : j = s
        · subst hjs; simp [WState.seth]; ring
        · simp [WState.seth, Function.update_of_ne hjs, List.flatMap_append]
      · funext j; simp [WState.seth, List.flatMap_append]
      · rfl
      · rfl
    rw [hfin] at t5
    have tb : WExec cap (.seq (.fwd s) (.seq (wlist d k) (.seq (.ifs s (.wr d true) (.wr d false))
        (.seq (.fwd d) (.fwd s)))) : WM ns nr) σ0 (pSt σ s d k x.length (u ++ [b])) (4 * k.length + 9) :=
      WExec.cast cap (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 (WExec.seq t4 t5)))) rfl (by omega)
    have hw0 : wbit σ0 s = true := by
      show readTapeBit (σ0.st s) (σ0.sh s) = true
      rw [s0st, s0sh]; exact r0
    have hu' : (u ++ [b]) ++ v = w := by rw [← hu]; simp
    have ih := pl_loop cap σ s d hsd k x w hs v (u ++ [b]) hu'
    refine WExec.cast cap (WExec.whsT hw0 tb ih) rfl ?_
    simp only [List.length_cons]
    ring_nf
    omega

/-- **The copy**: from the framed `w` on `s` (head `0`) and `d`'s head at its end, `d` extended by the bits of `w`, each
after `k`. -/
theorem pl_spec (cap : ℕ) (σ : WState ns nr) (s d : Fin (ns + 1)) (hsd : s ≠ d) (k w : List Bool)
    (hs : σ.st s = frame w) (hs0 : σ.sh s = 0) (hd : σ.sh d = (σ.st d).length) :
    WExec cap (plW s d k) σ (pSt σ s d k 0 w) ((4 * k.length + 11) * w.length + 1) := by
  have e : pSt σ s d k 0 [] = σ := by
    unfold pSt
    simp only [List.flatMap_nil, List.length_nil, Nat.mul_zero]
    rw [apd_nil σ d hd]
    apply WState.eq
    · funext j; by_cases hj : j = s
      · subst hj; simp [WState.seth, hs0]
      · simp [WState.seth, Function.update_of_ne hj]
    · rfl
    · rfl
    · rfl
  have h := pl_loop cap σ s d hsd k [] w (by rw [List.nil_append]; exact hs) w [] rfl
  simp only [List.length_nil] at h
  rw [e] at h
  exact h

end NearCubicWires.WireExponent3_5.PrimT.C4Hk
