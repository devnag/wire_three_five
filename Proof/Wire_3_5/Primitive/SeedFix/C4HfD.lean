import Proof.Wire_3_5.Primitive.SeedFix.C4HfC

/-! # The HASH child family, part 4: the free-bit ruler of the working Hb bank

`filt:soft`, P3:2255-2262: at the child prefix of length `plen` the elimination's free-bit ruler is
`pad c_C (1^{2t·ℓ₀ − plen})`; from the kept `frame (pad c_C (1^{2t·ℓ₀}))` it is the unframed word without its first
`plen` bits, then `plen` falses (**`skip_spec`**: `skipW` at `k` counted on a register).

Paper quantity of the main type: the free-bit ruler of the child prefix's elimination. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ}

/-- The pair loop's body: skip the pair while `r0 ≠ 0` (moving the count to `r1`), else copy its bit. -/
def skipB (s d : Fin (ns + 1)) (r0 r1 : Fin nr) : WM ns nr :=
  .seq (.fwd s) (.seq (.ifr r0 (.seq (.dec r0) (.inc r1)) (.seq (.ifs s (.wr d true) (.wr d false)) (.fwd d)))
    (.fwd s))

/-- The append loop's body. -/
def appB (d : Fin (ns + 1)) (r1 : Fin nr) : WM ns nr := .seq (.wr d false) (.seq (.fwd d) (.dec r1))

/-- **Drop the first `k` bits, append `k` falses** (`k` on `r0`). -/
def skipW (s d : Fin (ns + 1)) (r0 r1 : Fin nr) : WM ns nr :=
  .seq (.whs s (skipB s d r0 r1)) (.whr r1 (appB d r1))

/-- The pair loop's state after the pairs of `u`. -/
def kSt (σ : WState ns nr) (s d : Fin (ns + 1)) (r0 r1 : Fin nr) (k : ℕ) (u : List Bool) : WState ns nr :=
  ⟨Function.update (Function.update σ.sh s (2 * u.length)) d (u.length - k), Function.update σ.st d (u.drop k),
    Function.update (Function.update σ.val r0 (k - u.length)) r1 (min u.length k), σ.cell⟩

theorem skip_loop (cap : ℕ) (σ : WState ns nr) (s d : Fin (ns + 1)) (hsd : s ≠ d) (r0 r1 : Fin nr) (hr : r0 ≠ r1)
    (k : ℕ) (w : List Bool) (hs : σ.st s = frame w) (hk : k < cap) :
    ∀ (v u : List Bool), u ++ v = w →
      WExec cap (.whs s (skipB s d r0 r1)) (kSt σ s d r0 r1 k u) (kSt σ s d r0 r1 k w) (12 * v.length + 1)
  | [], u, hu => by
    rw [List.append_nil] at hu
    subst hu
    refine WExec.whsF ?_
    show readTapeBit ((kSt σ s d r0 r1 k u).st s) ((kSt σ s d r0 r1 k u).sh s) = false
    have e1 : (kSt σ s d r0 r1 k u).st s = σ.st s := by
      show Function.update σ.st d _ s = _; rw [Function.update_of_ne hsd]
    have e2 : (kSt σ s d r0 r1 k u).sh s = 2 * u.length := by
      show Function.update (Function.update σ.sh s _) d _ s = _
      rw [Function.update_of_ne hsd, Function.update_self]
    rw [e1, e2, hs]
    have e : frame u = u.flatMap (fun b => [true, b]) ++ [false] := by
      have := frame_append_pairs u []; rw [List.append_nil] at this; exact this
    rw [e]
    have := read_pairs u [false] 0
    rw [Nat.add_zero] at this
    rw [this]; rfl
  | c :: v, u, hu => by
    have hw : σ.st s = u.flatMap (fun b => [true, b]) ++ (true :: c :: frame v) := by
      rw [hs, ← hu, frame_append_pairs]; rfl
    have r0' : readTapeBit (σ.st s) (2 * u.length) = true := by
      rw [hw]; have := read_pairs u (true :: c :: frame v) 0; rw [Nat.add_zero] at this; rw [this]; rfl
    have r1' : readTapeBit (σ.st s) (2 * u.length + 1) = c := by
      rw [hw, read_pairs u (true :: c :: frame v) 1]; rfl
    set s0 := kSt σ s d r0 r1 k u with hs0
    have g_sts : s0.st s = σ.st s := by show Function.update σ.st d _ s = _; rw [Function.update_of_ne hsd]
    have g_shs : s0.sh s = 2 * u.length := by
      show Function.update (Function.update σ.sh s _) d _ s = _
      rw [Function.update_of_ne hsd, Function.update_self]
    have g_std : s0.st d = u.drop k := by show Function.update σ.st d _ d = _; rw [Function.update_self]
    have g_shd : s0.sh d = u.length - k := by
      show Function.update (Function.update σ.sh s _) d _ d = _; rw [Function.update_self]
    have g_r0 : s0.val r0 = k - u.length := by
      show Function.update (Function.update σ.val r0 _) r1 _ r0 = _
      rw [Function.update_of_ne hr, Function.update_self]
    have g_r1 : s0.val r1 = min u.length k := by
      show Function.update (Function.update σ.val r0 _) r1 _ r1 = _; rw [Function.update_self]
    have a1 := WExec.fwd (cap := cap) s s0
    set s1 := s0.seth s (s0.sh s + 1)
    have hb : wbit s1 s = c := by
      show readTapeBit (s1.st s) (s1.sh s) = c
      have e1 : s1.st s = σ.st s := g_sts
      have e2 : s1.sh s = 2 * u.length + 1 := by
        show Function.update s0.sh s (s0.sh s + 1) s = _; rw [Function.update_self, g_shs]
      rw [e1, e2]; exact r1'
    -- the branch
    have hmid : ∃ s2 : WState ns nr, WExec cap (.ifr r0 (.seq (.dec r0) (.inc r1))
        (.seq (.ifs s (.wr d true) (.wr d false)) (.fwd d)) : WM ns nr) s1 s2 6 ∧
        s2.seth s (s2.sh s + 1) = kSt σ s d r0 r1 k (u ++ [c]) := by
      by_cases hlt : u.length < k
      · have hv : s1.val r0 ≠ 0 := by
          show s0.val r0 ≠ 0; rw [g_r0]; omega
        have b1 := WExec.dec (cap := cap) r0 s1 (by show s0.val r0 ≤ cap; rw [g_r0]; omega)
        set s1' := s1.setv r0 (s1.val r0 - 1)
        have hv1 : s1'.val r1 < cap := by
          show Function.update s1.val r0 _ r1 < cap
          rw [Function.update_of_ne (Ne.symm hr)]; show s0.val r1 < cap; rw [g_r1]; omega
        have b2 := WExec.inc (cap := cap) r1 s1' hv1
        refine ⟨_, WExec.cast cap (WExec.ifrT hv (WExec.seq b1 b2)) rfl (by omega), ?_⟩
        apply WState.eq
        · funext j
          simp only [s1', s1, hs0, kSt, WState.seth, WState.setv, Function.update_apply, List.length_append,
            List.length_singleton]
          by_cases hjs : j = s
          · subst hjs; simp [hsd]; ring
          · by_cases hjd : j = d
            · subst hjd; simp [hjs, Ne.symm hsd]; omega
            · simp [hjs, hjd]
        · funext j
          simp only [s1', s1, hs0, kSt, WState.seth, WState.setv, Function.update_apply]
          by_cases hjd : j = d
          · subst hjd
            simp only [if_pos]
            rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by simp; omega)]
          · simp [hjd]
        · funext j
          simp only [s1', s1, hs0, kSt, WState.seth, WState.setv, Function.update_apply, List.length_append,
            List.length_singleton]
          by_cases hj1 : j = r1
          · subst hj1; simp [Ne.symm hr]; omega
          · by_cases hj0 : j = r0
            · subst hj0; simp [hj1, hr]; omega
            · simp [hj1, hj0]
        · rfl
      · have hv : s1.val r0 = 0 := by
          show s0.val r0 = 0; rw [g_r0]; omega
        have e3d : s1.st d = u.drop k := g_std
        have e3h : s1.sh d = (u.drop k).length := by
          show Function.update s0.sh s (s0.sh s + 1) d = _
          rw [Function.update_of_ne (Ne.symm hsd), g_shd, List.length_drop]
        have a4 : ∀ x : Bool, WExec cap (.wr d x : WM ns nr) s1 (s1.sets d (u.drop k ++ [x])) 1 := by
          intro x
          have h := WExec.wr (cap := cap) d x s1
          rw [e3d, e3h, C4Pipe.write_end] at h
          exact h
        have a4' : WExec cap (.ifs s (.wr d true) (.wr d false) : WM ns nr) s1 (s1.sets d (u.drop k ++ [c])) 2 := by
          cases c
          · exact WExec.ifsF hb (a4 false)
          · exact WExec.ifsT hb (a4 true)
        have a5 := WExec.fwd (cap := cap) d (s1.sets d (u.drop k ++ [c]))
        refine ⟨_, WExec.cast cap (WExec.ifrF hv (WExec.seq a4' a5)) rfl (by omega), ?_⟩
        apply WState.eq
        · funext j
          simp only [s1, hs0, kSt, WState.seth, WState.sets, Function.update_apply, List.length_append,
            List.length_singleton]
          by_cases hjs : j = s
          · subst hjs; simp [hsd]; ring
          · by_cases hjd : j = d
            · subst hjd; simp [hjs, Ne.symm hsd]; omega
            · simp [hjs, hjd]
        · funext j
          simp only [s1, hs0, kSt, WState.seth, WState.sets, Function.update_apply]
          by_cases hjd : j = d
          · subst hjd; simp only [if_pos]; rw [List.drop_append_of_le_length (by omega)]
          · simp [hjd]
        · funext j
          simp only [s1, hs0, kSt, WState.seth, WState.sets, Function.update_apply, List.length_append,
            List.length_singleton]
          by_cases hj1 : j = r1
          · subst hj1; simp [Ne.symm hr]; omega
          · by_cases hj0 : j = r0
            · subst hj0; simp [hj1, hr]; omega
            · simp [hj1, hj0]
        · rfl
    obtain ⟨s2, a2, e2⟩ := hmid
    have a3 := WExec.fwd (cap := cap) s s2
    rw [e2] at a3
    have tb : WExec cap (skipB s d r0 r1) s0 (kSt σ s d r0 r1 k (u ++ [c])) 10 :=
      WExec.cast cap (WExec.seq a1 (WExec.seq a2 a3)) rfl (by omega)
    have hw0 : wbit s0 s = true := by
      show readTapeBit (s0.st s) (s0.sh s) = true
      rw [g_sts, g_shs]; exact r0'
    have hu' : (u ++ [c]) ++ v = w := by rw [← hu]; simp
    have ih := skip_loop cap σ s d hsd r0 r1 hr k w hs hk v (u ++ [c]) hu'
    refine WExec.cast cap (WExec.whsT hw0 tb ih) rfl ?_
    simp only [List.length_cons]; omega

/-- The append loop's state after `j` falses. -/
def aSt (σ : WState ns nr) (s d : Fin (ns + 1)) (r0 r1 : Fin nr) (k : ℕ) (w : List Bool) (j : ℕ) : WState ns nr :=
  ⟨Function.update (Function.update σ.sh s (2 * w.length)) d (w.length - k + j),
    Function.update σ.st d (w.drop k ++ List.replicate j false),
    Function.update (Function.update σ.val r0 0) r1 (k - j), σ.cell⟩

theorem app_loop (cap : ℕ) (σ : WState ns nr) (s d : Fin (ns + 1)) (hsd : s ≠ d) (r0 r1 : Fin nr) (hr : r0 ≠ r1)
    (k : ℕ) (w : List Bool) (hkw : k ≤ w.length) (hk : k ≤ cap) :
    ∀ i j : ℕ, i + j = k →
      WExec cap (.whr r1 (appB d r1)) (aSt σ s d r0 r1 k w j) (aSt σ s d r0 r1 k w k) (7 * i + 1)
  | 0, j, hij => by
    simp only [Nat.zero_add] at hij
    subst hij
    exact WExec.whrF (by show Function.update (Function.update σ.val r0 0) r1 (j - j) r1 = 0; simp)
  | i + 1, j, hij => by
    set s0 := aSt σ s d r0 r1 k w j with hs0
    have hv : s0.val r1 ≠ 0 := by
      show Function.update (Function.update σ.val r0 0) r1 (k - j) r1 ≠ 0
      rw [Function.update_self]; omega
    have g_std : s0.st d = w.drop k ++ List.replicate j false := by
      show Function.update σ.st d _ d = _; rw [Function.update_self]
    have g_shd : s0.sh d = (w.drop k ++ List.replicate j false).length := by
      show Function.update (Function.update σ.sh s _) d _ d = _
      rw [Function.update_self]
      simp only [List.length_append, List.length_drop, List.length_replicate]
    have a1 := WExec.wr (cap := cap) d false s0
    rw [g_std, g_shd, C4Pipe.write_end] at a1
    set s1 := s0.sets d (w.drop k ++ List.replicate j false ++ [false])
    have a2 := WExec.fwd (cap := cap) d s1
    set s2 := s1.seth d (s1.sh d + 1)
    have a3 := WExec.dec (cap := cap) r1 s2 (by
      show Function.update (Function.update σ.val r0 0) r1 (k - j) r1 ≤ cap
      rw [Function.update_self]; omega)
    have e3 : s2.setv r1 (s2.val r1 - 1) = aSt σ s d r0 r1 k w (j + 1) := by
      apply WState.eq
      · funext x
        simp only [s2, s1, hs0, aSt, WState.seth, WState.sets, WState.setv, Function.update_apply]
        by_cases hxd : x = d
        · subst hxd; simp [Ne.symm hsd]; omega
        · by_cases hxs : x = s
          · subst hxs; simp [hxd]
          · simp [hxd, hxs]
      · show Function.update (Function.update σ.st d (w.drop k ++ List.replicate j false)) d
            (w.drop k ++ List.replicate j false ++ [false]) = Function.update σ.st d (w.drop k ++ List.replicate (j + 1) false)
        rw [Function.update_idem, List.replicate_succ', List.append_assoc]
      · funext x
        simp only [s2, s1, hs0, aSt, WState.seth, WState.sets, WState.setv, Function.update_apply]
        by_cases hx1 : x = r1
        · subst hx1; simp; omega
        · simp [hx1]
      · rfl
    rw [e3] at a3
    have tb : WExec cap (appB d r1) s0 (aSt σ s d r0 r1 k w (j + 1)) 5 :=
      WExec.cast cap (WExec.seq a1 (WExec.seq a2 a3)) rfl (by omega)
    have ih := app_loop cap σ s d hsd r0 r1 hr k w hkw hk i (j + 1) (by omega)
    exact WExec.cast cap (WExec.whrT hv tb ih) rfl (by omega)

/-- The state after `skipW`. -/
def skipOut (σ : WState ns nr) (s d : Fin (ns + 1)) (r0 r1 : Fin nr) (k : ℕ) (w : List Bool) : WState ns nr :=
  aSt σ s d r0 r1 k w k

/-- **Drop `k`, append `k` falses**: from the framed `w` on `s`, an empty `d` (heads `0`), `k ≤ |w|` on `r0` and
`0` on `r1`: `w.drop k ++ 1^k`-falses on `d`, the registers back to `0`. -/
theorem skip_spec (cap : ℕ) (σ : WState ns nr) (s d : Fin (ns + 1)) (hsd : s ≠ d) (r0 r1 : Fin nr) (hr : r0 ≠ r1)
    (k : ℕ) (w : List Bool) (hs : σ.st s = frame w) (hs0 : σ.sh s = 0) (hd : σ.st d = []) (hd0 : σ.sh d = 0)
    (hv0 : σ.val r0 = k) (hv1 : σ.val r1 = 0) (hkw : k ≤ w.length) (hk : k < cap) :
    WExec cap (skipW s d r0 r1) σ (skipOut σ s d r0 r1 k w) (19 * w.length + 3) := by
  have e0 : kSt σ s d r0 r1 k [] = σ := by
    apply WState.eq
    · funext j
      show Function.update (Function.update σ.sh s (2 * 0)) d (0 - k) j = σ.sh j
      by_cases hjd : j = d
      · subst hjd; rw [Function.update_self, hd0]; simp
      · rw [Function.update_of_ne hjd]
        by_cases hjs : j = s
        · subst hjs; rw [Function.update_self, hs0]
        · rw [Function.update_of_ne hjs]
    · funext j
      show Function.update σ.st d (List.drop k []) j = σ.st j
      by_cases hjd : j = d
      · subst hjd; rw [Function.update_self, hd]; simp
      · rw [Function.update_of_ne hjd]
    · funext j
      show Function.update (Function.update σ.val r0 (k - 0)) r1 (min 0 k) j = σ.val j
      by_cases hj1 : j = r1
      · subst hj1; rw [Function.update_self, hv1]; simp
      · rw [Function.update_of_ne hj1]
        by_cases hj0 : j = r0
        · subst hj0; rw [Function.update_self, hv0]; rfl
        · rw [Function.update_of_ne hj0]
    · rfl
  have t1 := skip_loop cap σ s d hsd r0 r1 hr k w hs hk w [] rfl
  rw [e0] at t1
  have e1 : kSt σ s d r0 r1 k w = aSt σ s d r0 r1 k w 0 := by
    apply WState.eq
    · rfl
    · funext j; simp [kSt, aSt]
    · funext j
      simp only [kSt, aSt, Function.update_apply]
      by_cases hj1 : j = r1
      · subst hj1; simp; omega
      · by_cases hj0 : j = r0
        · subst hj0; simp [hj1, hr]; omega
        · simp [hj1, hj0]
    · rfl
  rw [e1] at t1
  have t2 := app_loop cap σ s d hsd r0 r1 hr k w hkw (by omega) k 0 rfl
  exact WExec.cast cap (WExec.seq t1 t2) rfl (by omega)

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
