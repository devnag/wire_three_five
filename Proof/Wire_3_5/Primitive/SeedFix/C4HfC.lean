import Proof.Wire_3_5.Primitive.SeedFix.C4HfB

/-! # The HASH child family, part 3: the prefix patches of the working Hb bank

`filt:soft`, P3:2255-2262 (the conditional probability given the prefix `p` of the hash seed): the Hb bank at the child
`p ++ [b]` differs from the kept one (at `plen = pfx = 0`) in two elimination tapes: the prefix word
`frame (binary plen pfx) = frame (p ++ [b])` and the free-bit ruler `pad c_C (1^{2t·ℓ₀ − plen})`.
* **`pfx_spec`**: `pfxW` writes `frame (p ++ [b])` from the framed prefix `frame p`, counting `plen = |p| + 1`;
* **`skip_spec`**: `skipW` unframes a framed word dropping its first `k` bits, then appends `k` falses.

Paper quantity of the main types: the child prefix's elimination words. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ}

/-! ## The prefix word -/

/-- Copy the pairs of the framed prefix on `P` to `d` (counting them on `r`), then the pair `true b` and the
terminator. -/
def pfxW (P d : Fin (ns + 1)) (r : Fin nr) (b : Bool) : WM ns nr :=
  .seq (.whs P (.seq (.wr d true) (.seq (.fwd d) (.seq (.fwd P) (.seq (.ifs P (.wr d true) (.wr d false))
    (.seq (.fwd d) (.seq (.fwd P) (.inc r))))))))
    (.seq (.wr d true) (.seq (.fwd d) (.seq (.wr d b) (.seq (.fwd d) (.seq (.wr d false) (.inc r))))))

/-- The state after the pairs of `u`. -/
def pSt (σ : WState ns nr) (P d : Fin (ns + 1)) (r : Fin nr) (u : List Bool) : WState ns nr :=
  ⟨Function.update (Function.update σ.sh P (2 * u.length)) d (2 * u.length),
    Function.update σ.st d (u.flatMap fun b => [true, b]), Function.update σ.val r u.length, σ.cell⟩

theorem pairs_len (u : List Bool) : (u.flatMap fun b => [true, b]).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    rw [List.flatMap_cons, List.length_append, ih]
    simp only [List.length_cons, List.length_nil]
    ring

theorem pfx_loop (cap : ℕ) (σ : WState ns nr) (P d : Fin (ns + 1)) (hPd : P ≠ d) (r : Fin nr) (p : List Bool)
    (hP : σ.st P = frame p) (hcap : p.length < cap) :
    ∀ (v u : List Bool), u ++ v = p →
      WExec cap (.whs P (.seq (.wr d true) (.seq (.fwd d) (.seq (.fwd P) (.seq (.ifs P (.wr d true) (.wr d false))
        (.seq (.fwd d) (.seq (.fwd P) (.inc r)))))))) (pSt σ P d r u) (pSt σ P d r p) (18 * v.length + 1)
  | [], u, hu => by
    rw [List.append_nil] at hu
    subst hu
    refine WExec.whsF ?_
    show readTapeBit ((pSt σ P d r u).st P) ((pSt σ P d r u).sh P) = false
    have e1 : (pSt σ P d r u).st P = σ.st P := by
      show Function.update σ.st d _ P = _; rw [Function.update_of_ne hPd]
    have e2 : (pSt σ P d r u).sh P = 2 * u.length := by
      show Function.update (Function.update σ.sh P _) d _ P = _
      rw [Function.update_of_ne hPd, Function.update_self]
    rw [e1, e2, hP]
    have e : frame u = u.flatMap (fun b => [true, b]) ++ [false] := by
      have := frame_append_pairs u []; rw [List.append_nil] at this; exact this
    rw [e]
    have := read_pairs u [false] 0
    rw [Nat.add_zero] at this
    rw [this]; rfl
  | c :: v, u, hu => by
    have hw : σ.st P = u.flatMap (fun b => [true, b]) ++ (true :: c :: frame v) := by
      rw [hP, ← hu, frame_append_pairs]; rfl
    have r0 : readTapeBit (σ.st P) (2 * u.length) = true := by
      rw [hw]; have := read_pairs u (true :: c :: frame v) 0; rw [Nat.add_zero] at this; rw [this]; rfl
    have r1 : readTapeBit (σ.st P) (2 * u.length + 1) = c := by
      rw [hw, read_pairs u (true :: c :: frame v) 1]; rfl
    have hlen : (u ++ [c]).length ≤ p.length := by rw [← hu]; simp
    set W0 := u.flatMap fun b => [true, b] with hW0
    have hWl : W0.length = 2 * u.length := pairs_len u
    -- the states along one pair
    set s0 := pSt σ P d r u with hs0
    have g_stP : s0.st P = σ.st P := by show Function.update σ.st d _ P = _; rw [Function.update_of_ne hPd]
    have g_shP : s0.sh P = 2 * u.length := by
      show Function.update (Function.update σ.sh P _) d _ P = _
      rw [Function.update_of_ne hPd, Function.update_self]
    have g_std : s0.st d = W0 := by show Function.update σ.st d _ d = _; rw [Function.update_self]
    have g_shd : s0.sh d = 2 * u.length := by
      show Function.update (Function.update σ.sh P _) d _ d = _; rw [Function.update_self]
    have g_r : s0.val r = u.length := by show Function.update σ.val r _ r = _; rw [Function.update_self]
    have a1 := WExec.wr (cap := cap) d true s0
    rw [g_std, g_shd, ← hWl, C4Pipe.write_end] at a1
    set s1 := s0.sets d (W0 ++ [true])
    have a2 := WExec.fwd (cap := cap) d s1
    set s2 := s1.seth d (s1.sh d + 1)
    have a3 := WExec.fwd (cap := cap) P s2
    set s3 := s2.seth P (s2.sh P + 1)
    have hb : wbit s3 P = c := by
      show readTapeBit (s3.st P) (s3.sh P) = c
      have e1 : s3.st P = σ.st P := by
        show Function.update s0.st d _ P = _; rw [Function.update_of_ne hPd]; exact g_stP
      have e2 : s3.sh P = 2 * u.length + 1 := by
        show Function.update s2.sh P (s2.sh P + 1) P = _
        rw [Function.update_self]
        show Function.update s1.sh d (s1.sh d + 1) P + 1 = _
        rw [Function.update_of_ne hPd]
        show s0.sh P + 1 = _
        rw [g_shP]
      rw [e1, e2]; exact r1
    have e3d : s3.st d = W0 ++ [true] := by
      show Function.update s0.st d _ d = _; rw [Function.update_self]
    have e3h : s3.sh d = W0.length + 1 := by
      show Function.update s2.sh P (s2.sh P + 1) d = _
      rw [Function.update_of_ne (Ne.symm hPd)]
      show Function.update s1.sh d (s1.sh d + 1) d = _
      rw [Function.update_self]
      show s0.sh d + 1 = _
      rw [g_shd, hWl]
    have a4 : ∀ x : Bool, WExec cap (.wr d x : WM ns nr) s3 (s3.sets d (W0 ++ [true, x])) 1 := by
      intro x
      have h := WExec.wr (cap := cap) d x s3
      rw [e3d, e3h] at h
      have e : W0.length + 1 = (W0 ++ [true]).length := by simp
      rw [e, C4Pipe.write_end] at h
      rw [List.append_assoc] at h
      exact h
    have a4' : WExec cap (.ifs P (.wr d true) (.wr d false) : WM ns nr) s3 (s3.sets d (W0 ++ [true, c])) 2 := by
      cases c
      · exact WExec.ifsF hb (a4 false)
      · exact WExec.ifsT hb (a4 true)
    set s4 := s3.sets d (W0 ++ [true, c])
    have a5 := WExec.fwd (cap := cap) d s4
    set s5 := s4.seth d (s4.sh d + 1)
    have a6 := WExec.fwd (cap := cap) P s5
    set s6 := s5.seth P (s5.sh P + 1)
    have hr6 : s6.val r < cap := by
      have e : s6.val r = u.length := g_r
      rw [e]
      have := hlen
      simp only [List.length_append, List.length_singleton] at this
      omega
    have a7 := WExec.inc (cap := cap) r s6 hr6
    have e7 : s6.setv r (s6.val r + 1) = pSt σ P d r (u ++ [c]) := by
      apply WState.eq
      · funext j
        simp only [s6, s5, s4, s3, s2, s1, hs0, pSt, WState.seth, WState.sets, WState.setv, Function.update_apply,
          List.length_append, List.length_singleton]
        by_cases hjP : j = P
        · subst hjP; simp [hPd]; ring
        · by_cases hjd : j = d
          · subst hjd; simp [hjP, Ne.symm hPd, hWl]; ring
          · simp [hjP, hjd]
      · funext j
        simp only [s6, s5, s4, s3, s2, s1, hs0, pSt, WState.seth, WState.sets, WState.setv, Function.update_apply,
          List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        by_cases hjd : j = d
        · subst hjd; simp [hW0]
        · simp [hjd]
      · funext j
        simp only [s6, s5, s4, s3, s2, s1, hs0, pSt, WState.seth, WState.sets, WState.setv, Function.update_apply,
          List.length_append, List.length_singleton]
        by_cases hjr : j = r
        · subst hjr; simp
        · simp [hjr]
      · rfl
    rw [e7] at a7
    have tb := WExec.seq a1 (WExec.seq a2 (WExec.seq a3 (WExec.seq a4' (WExec.seq a5 (WExec.seq a6 a7)))))
    have hw0 : wbit s0 P = true := by
      show readTapeBit (s0.st P) (s0.sh P) = true
      rw [g_stP, g_shP]; exact r0
    have hu' : (u ++ [c]) ++ v = p := by rw [← hu]; simp
    have ih := pfx_loop cap σ P d hPd r p hP hcap v (u ++ [c]) hu'
    refine WExec.cast cap (WExec.whsT hw0 tb ih) rfl ?_
    simp only [List.length_cons]; omega

/-- The state after the prefix word. -/
def pfxOut (σ : WState ns nr) (P d : Fin (ns + 1)) (r : Fin nr) (p : List Bool) (b : Bool) : WState ns nr :=
  ⟨Function.update (Function.update σ.sh P (2 * p.length)) d (2 * p.length + 2),
    Function.update σ.st d (frame (p ++ [b])), Function.update σ.val r (p.length + 1), σ.cell⟩

/-- **The prefix word**: from `frame p` on `P` and an empty `d` (heads `0`, `r = 0`), `frame (p ++ [b])` on `d` and
`|p| + 1` on `r`. -/
theorem pfx_spec (cap : ℕ) (σ : WState ns nr) (P d : Fin (ns + 1)) (hPd : P ≠ d) (r : Fin nr) (p : List Bool)
    (b : Bool) (hP : σ.st P = frame p) (hP0 : σ.sh P = 0) (hd : σ.st d = []) (hd0 : σ.sh d = 0) (hr : σ.val r = 0)
    (hcap : p.length + 1 < cap) :
    WExec cap (pfxW P d r b) σ (pfxOut σ P d r p b) (18 * p.length + 20) := by
  have e0 : pSt σ P d r [] = σ := by
    apply WState.eq
    · funext j
      show Function.update (Function.update σ.sh P (2 * 0)) d (2 * 0) j = σ.sh j
      by_cases hjd : j = d
      · subst hjd; rw [Function.update_self, hd0]
      · rw [Function.update_of_ne hjd]
        by_cases hjP : j = P
        · subst hjP; rw [Function.update_self, hP0]
        · rw [Function.update_of_ne hjP]
    · funext j
      show Function.update σ.st d [] j = σ.st j
      by_cases hjd : j = d
      · subst hjd; rw [Function.update_self, hd]
      · rw [Function.update_of_ne hjd]
    · funext j
      show Function.update σ.val r 0 j = σ.val j
      by_cases hjr : j = r
      · subst hjr; rw [Function.update_self, hr]
      · rw [Function.update_of_ne hjr]
    · rfl
  have t1 := pfx_loop cap σ P d hPd r p hP (by omega) p [] rfl
  rw [e0] at t1
  set s0 := pSt σ P d r p with hs0
  have g_std : s0.st d = p.flatMap fun b => [true, b] := by
    show Function.update σ.st d _ d = _; rw [Function.update_self]
  have g_shd : s0.sh d = (p.flatMap fun b => [true, b]).length := by
    show Function.update (Function.update σ.sh P _) d _ d = _; rw [Function.update_self, pairs_len]
  have a1 := WExec.wr (cap := cap) d true s0
  rw [g_std, g_shd, C4Pipe.write_end] at a1
  set s1 := s0.sets d ((p.flatMap fun b => [true, b]) ++ [true])
  have a2 := WExec.fwd (cap := cap) d s1
  set s2 := s1.seth d (s1.sh d + 1)
  have e2d : s2.st d = (p.flatMap fun b => [true, b]) ++ [true] := by
    show Function.update s0.st d _ d = _; rw [Function.update_self]
  have e2h : s2.sh d = ((p.flatMap fun b => [true, b]) ++ [true]).length := by
    show Function.update s1.sh d (s1.sh d + 1) d = _
    rw [Function.update_self]; show s0.sh d + 1 = _; rw [g_shd]; simp
  have a3 := WExec.wr (cap := cap) d b s2
  rw [e2d, e2h, C4Pipe.write_end] at a3
  set s3 := s2.sets d ((p.flatMap fun b => [true, b]) ++ [true] ++ [b])
  have a4 := WExec.fwd (cap := cap) d s3
  set s4 := s3.seth d (s3.sh d + 1)
  have e4d : s4.st d = (p.flatMap fun b => [true, b]) ++ [true] ++ [b] := by
    show Function.update s2.st d _ d = _; rw [Function.update_self]
  have e4h : s4.sh d = ((p.flatMap fun b => [true, b]) ++ [true] ++ [b]).length := by
    show Function.update s3.sh d (s3.sh d + 1) d = _
    rw [Function.update_self]; show s2.sh d + 1 = _; rw [e2h]; simp
  have a5 := WExec.wr (cap := cap) d false s4
  rw [e4d, e4h, C4Pipe.write_end] at a5
  set s5 := s4.sets d ((p.flatMap fun b => [true, b]) ++ [true] ++ [b] ++ [false])
  have hr5 : s5.val r < cap := by
    have e : s5.val r = p.length := by
      show Function.update σ.val r p.length r = _; rw [Function.update_self]
    rw [e]; omega
  have a6 := WExec.inc (cap := cap) r s5 hr5
  have e6 : s5.setv r (s5.val r + 1) = pfxOut σ P d r p b := by
    apply WState.eq
    · funext j
      simp only [s5, s4, s3, s2, s1, hs0, pSt, pfxOut, WState.seth, WState.sets, WState.setv, Function.update_apply,
        pairs_len]
      by_cases hjP : j = P
      · subst hjP; simp [hPd]
      · by_cases hjd : j = d
        · subst hjd; simp [hjP, Ne.symm hPd]
        · simp [hjP, hjd]
    · funext j
      simp only [s5, s4, s3, s2, s1, hs0, pSt, pfxOut, WState.seth, WState.sets, WState.setv, Function.update_apply]
      by_cases hjd : j = d
      · subst hjd; simp [frame_append_pairs]; rfl
      · simp [hjd]
    · funext j
      simp only [s5, s4, s3, s2, s1, hs0, pSt, pfxOut, WState.seth, WState.sets, WState.setv, Function.update_apply]
      by_cases hjr : j = r
      · subst hjr; simp
      · simp [hjr]
    · rfl
  rw [e6] at a6
  exact WExec.cast cap (WExec.seq t1 (WExec.seq a1 (WExec.seq a2 (WExec.seq a3 (WExec.seq a4 (WExec.seq a5 a6))))))
    rfl (by omega)

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
