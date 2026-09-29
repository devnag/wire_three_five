import Proof.Wire_3_5.Primitive.SeedFix.C4H2

/-! # The HASH child family, part 1: unframing a kept word onto a working stream

`filt:soft`, P3:2253-2290: the HASH child re-creates its working Hb bank at every child from the kept words, kept framed
(C4H-a): `unfW s d` copies the bits of the framed word on stream `s` onto the empty stream `d` (C5's word
programs), within `10·|w| + 1` steps (**`unf_spec`**, generic in the other streams).

Paper quantity of the main type: the kept word `w` itself, unframed (the Hb bank's tape). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ}

/-- **Unframe** stream `s` onto stream `d`: per pair `true b`, write `b`; stop at the terminator. -/
def unfW (s d : Fin (ns + 1)) : WM ns nr :=
  .whs s (.seq (.fwd s) (.seq (.ifs s (.wr d true) (.wr d false)) (.seq (.fwd d) (.fwd s))))

theorem frame_append_pairs (u v : List Bool) : frame (u ++ v) = u.flatMap (fun b => [true, b]) ++ frame v := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    rw [List.cons_append]
    show true :: b :: frame (u ++ v) = _
    rw [ih]; rfl

theorem read_pairs (u l : List Bool) (i : ℕ) :
    readTapeBit (u.flatMap (fun b => [true, b]) ++ l) (2 * u.length + i) = readTapeBit l i := by
  induction u with
  | nil => simp
  | cons b u ih =>
    rw [List.flatMap_cons, List.length_cons]
    have e : 2 * (u.length + 1) + i = 2 * u.length + i + 2 := by ring
    rw [e]
    show readTapeBit (true :: b :: (u.flatMap (fun b => [true, b]) ++ l)) (2 * u.length + i + 2) = _
    simpa [readTapeBit] using ih

/-- The state after the pairs of `u`: `d` holds `u`, the heads at `2|u|` and `|u|`. -/
def uSt (σ : WState ns nr) (s d : Fin (ns + 1)) (u : List Bool) : WState ns nr :=
  ⟨Function.update (Function.update σ.sh s (2 * u.length)) d u.length, Function.update σ.st d u, σ.val, σ.cell⟩

section U
variable (σ : WState ns nr) (s d : Fin (ns + 1)) (hsd : s ≠ d) (u : List Bool)
include hsd

theorem uSt_sh_s : (uSt σ s d u).sh s = 2 * u.length := by
  show Function.update (Function.update σ.sh s (2 * u.length)) d u.length s = _
  rw [Function.update_of_ne hsd, Function.update_self]

theorem uSt_st_s : (uSt σ s d u).st s = σ.st s := by
  show Function.update σ.st d u s = _
  rw [Function.update_of_ne hsd]

omit hsd in
theorem uSt_sh_d : (uSt σ s d u).sh d = u.length := by
  show Function.update (Function.update σ.sh s (2 * u.length)) d u.length d = _
  rw [Function.update_self]

omit hsd in
theorem uSt_st_d : (uSt σ s d u).st d = u := by
  show Function.update σ.st d u d = _
  rw [Function.update_self]

end U

theorem unf_loop (cap : ℕ) (σ : WState ns nr) (s d : Fin (ns + 1)) (hsd : s ≠ d) (w : List Bool)
    (hs : σ.st s = frame w) :
    ∀ (v u : List Bool), u ++ v = w → WExec cap (unfW s d) (uSt σ s d u) (uSt σ s d w) (10 * v.length + 1)
  | [], u, hu => by
    rw [List.append_nil] at hu
    subst hu
    refine WExec.whsF ?_
    show readTapeBit ((uSt σ s d u).st s) ((uSt σ s d u).sh s) = false
    rw [uSt_st_s σ s d hsd, uSt_sh_s σ s d hsd, hs]
    have e : frame u = u.flatMap (fun b => [true, b]) ++ [false] := by
      have := frame_append_pairs u []
      rw [List.append_nil] at this
      exact this
    rw [e]
    have := read_pairs u [false] 0
    rw [Nat.add_zero] at this
    rw [this]; rfl
  | b :: v, u, hu => by
    have hw : σ.st s = u.flatMap (fun b => [true, b]) ++ (true :: b :: frame v) := by
      rw [hs, ← hu, frame_append_pairs]; rfl
    have r0 : readTapeBit (σ.st s) (2 * u.length) = true := by
      rw [hw]; have := read_pairs u (true :: b :: frame v) 0; rw [Nat.add_zero] at this; rw [this]; rfl
    have r1 : readTapeBit (σ.st s) (2 * u.length + 1) = b := by
      rw [hw, read_pairs u (true :: b :: frame v) 1]; rfl
    set σ1 := (uSt σ s d u).seth s (2 * u.length + 1) with hσ1
    have t1 : WExec cap (.fwd s : WM ns nr) (uSt σ s d u) σ1 1 := by
      have h := WExec.fwd (cap := cap) s (uSt σ s d u)
      rwa [uSt_sh_s σ s d hsd] at h
    have e1 : σ1.st d = u := by rw [hσ1]; exact uSt_st_d σ s d u
    have e2 : σ1.sh d = u.length := by
      show Function.update (uSt σ s d u).sh s (2 * u.length + 1) d = _
      rw [Function.update_of_ne (Ne.symm hsd), uSt_sh_d]
    have hwr : ∀ c : Bool, WExec cap (.wr d c : WM ns nr) σ1 (σ1.sets d (u ++ [c])) 1 := by
      intro c
      have h := WExec.wr (cap := cap) d c σ1
      rw [e1, e2, C4Pipe.write_end] at h
      exact h
    have hb : wbit σ1 s = b := by
      show readTapeBit (σ1.st s) (σ1.sh s) = b
      have e3 : σ1.st s = σ.st s := uSt_st_s σ s d hsd u
      have e4 : σ1.sh s = 2 * u.length + 1 := by
        show Function.update (uSt σ s d u).sh s (2 * u.length + 1) s = _
        rw [Function.update_self]
      rw [e3, e4]; exact r1
    have t2 : WExec cap (.ifs s (.wr d true) (.wr d false) : WM ns nr) σ1 (σ1.sets d (u ++ [b])) 2 := by
      cases b
      · exact WExec.ifsF hb (hwr false)
      · exact WExec.ifsT hb (hwr true)
    have t3 : WExec cap (.seq (.fwd d) (.fwd s) : WM ns nr) (σ1.sets d (u ++ [b])) (uSt σ s d (u ++ [b])) 3 := by
      have h := WExec.seq (WExec.fwd (cap := cap) d (σ1.sets d (u ++ [b]))) (WExec.fwd (cap := cap) s _)
      refine WExec.cast cap h ?_ le_rfl
      apply WState.eq
      · funext j
        simp only [WState.seth, WState.sets, hσ1, uSt, Function.update_apply, List.length_append,
          List.length_singleton]
        by_cases hjs : j = s
        · subst hjs; simp [hsd]; ring
        · by_cases hjd : j = d
          · subst hjd; simp [hjs, Ne.symm hsd]
          · simp [hjs, hjd]
      · funext j; simp [WState.seth, WState.sets, hσ1, uSt, Function.update_apply]
      · rfl
      · rfl
    have tb : WExec cap (.seq (.fwd s) (.seq (.ifs s (.wr d true) (.wr d false)) (.seq (.fwd d) (.fwd s))) : WM ns nr)
        (uSt σ s d u) (uSt σ s d (u ++ [b])) 8 :=
      WExec.cast cap (WExec.seq t1 (WExec.seq t2 t3)) rfl (by omega)
    have hw0 : wbit (uSt σ s d u) s = true := by
      show readTapeBit ((uSt σ s d u).st s) ((uSt σ s d u).sh s) = true
      rw [uSt_st_s σ s d hsd, uSt_sh_s σ s d hsd]; exact r0
    have hu' : (u ++ [b]) ++ v = w := by rw [← hu]; simp
    have ih := unf_loop cap σ s d hsd w hs v (u ++ [b]) hu'
    refine WExec.cast cap (WExec.whsT hw0 tb ih) rfl ?_
    simp only [List.length_cons]; omega

/-- **The unframe**: from the framed `w` on `s` (head `0`) and an empty `d` (head `0`), `w` on `d`. -/
theorem unf_spec (cap : ℕ) (σ : WState ns nr) (s d : Fin (ns + 1)) (hsd : s ≠ d) (w : List Bool)
    (hs : σ.st s = frame w) (hs0 : σ.sh s = 0) (hd : σ.st d = []) (hd0 : σ.sh d = 0) :
    WExec cap (unfW s d) σ (uSt σ s d w) (10 * w.length + 1) := by
  have e : uSt σ s d [] = σ := by
    apply WState.eq
    · funext j
      show Function.update (Function.update σ.sh s (2 * 0)) d 0 j = σ.sh j
      by_cases hjd : j = d
      · subst hjd; rw [Function.update_self, hd0]
      · rw [Function.update_of_ne hjd]
        by_cases hjs : j = s
        · subst hjs; rw [Function.update_self, hs0]
        · rw [Function.update_of_ne hjs]
    · funext j
      show Function.update σ.st d [] j = σ.st j
      by_cases hjd : j = d
      · subst hjd; rw [Function.update_self, hd]
      · rw [Function.update_of_ne hjd]
    · rfl
    · rfl
  have h := unf_loop cap σ s d hsd w hs w [] rfl
  rw [e] at h
  exact h

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
