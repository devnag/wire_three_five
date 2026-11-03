import Proof.Wire_3_5.UnionMachine.RadScan
import Proof.Wire_3_5.UnionMachine.RadSpecBase
import Proof.Wire_3_5.Primitive.Writers.UnaryPow
import Proof.Wire_3_5.Primitive.Writers.StarNums

/-! # RADIX, stage 3 (2): Route B's numbers in registers (P3:2585-2623)

From the pool length `G`, the star row, `M`, `τ₀`, `J`, `p` and the windows' sum `S1` and the level records' length `S2`
in registers, one straight-line program with one loop (**`numsP`**) computes the RADIX setup's numbers:
`lb = 4·S1 + 1` (`= listBound D`), `Mlab = (4·row + 4)·G`, `lw = M + 2 + S2 + (J+1)·G` (`= |levelWord at G|`),
`X = (8G+2)^{3·lb+1} + M + τ + G + Mlab + lb + lw + p + 4` (`RadSpec.radX` at `Lmax = G`, `b₀ = 2`), `U = 2^20·X`,
`R = U^40`, `cap = U^45`, `Lg = R + 1` (**`numsP_spec`**: the exact final registers, the temporaries restored).

Paper quantity of the main type: Route B's capacities of the RADIX row (`RadSpec.reqB`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadNums
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryPow NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

variable {ns nr : ℕ} (cap : ℕ) (Q : Fin 48 ↪ Fin nr)

/-- Five of the program's registers. -/
def e5 (a b c d e : Fin 48) (h : Function.Injective ![a, b, c, d, e]) : Fin 5 ↪ Fin 48 := ⟨_, h⟩

theorem qne {i j : Fin 48} (h : i ≠ j) : Q i ≠ Q j := Q.injective.ne h

/-! ## Block A: `lb = 4·S1 + 1` -/

/-- `Q8 := 4·Q6 + 1` through `Q16, Q17, Q18`. -/
def blkA : WM ns nr :=
  .seq (StarNums.incN (Q 16) 4) (.seq (mulAddW ((e5 16 6 8 17 18 (by decide)).trans Q))
    (.seq (.inc (Q 8)) (WM.clear (Q 16))))

theorem blkA_spec (σ : WState ns nr) (h8 : σ.val (Q 8) = 0) (h16 : σ.val (Q 16) = 0) (h17 : σ.val (Q 17) = 0)
    (h18 : σ.val (Q 18) = 0) (hc : 4 * σ.val (Q 6) + 4 ≤ cap) :
    WExec cap (blkA Q) σ (σ.setv (Q 8) (4 * σ.val (Q 6) + 1)) (100 * (σ.val (Q 6) + 10)) := by
  have s1 := StarNums.incN_spec cap (Q 16) 4 σ (by omega)
  rw [h16, Nat.zero_add] at s1
  set σ1 := σ.setv (Q 16) 4 with hσ1
  have v1 : ∀ i : Fin 48, i ≠ 16 → σ1.val (Q i) = σ.val (Q i) := fun i hi => by
    simp [σ1, Function.update_of_ne (qne Q hi)]
  have s2 := mulAddW_spec cap ((e5 16 6 8 17 18 (by decide)).trans Q) σ1
    (by show σ1.val (Q 17) = 0; rw [v1 17 (by decide), h17])
    (by show σ1.val (Q 18) = 0; rw [v1 18 (by decide), h18])
    (by show σ1.val (Q 6) ≤ cap; rw [v1 6 (by decide)]; omega)
    (by show σ1.val (Q 8) + σ1.val (Q 16) * σ1.val (Q 6) ≤ cap
        rw [v1 8 (by decide), v1 6 (by decide), h8]; simp [σ1]; omega)
    (by show σ1.val (Q 16) ≤ cap; simp [σ1]; omega)
  have e2 : σ1.val (((e5 16 6 8 17 18 (by decide)).trans Q) 2) + σ1.val (((e5 16 6 8 17 18 (by decide)).trans Q) 0) *
      σ1.val (((e5 16 6 8 17 18 (by decide)).trans Q) 1) = 4 * σ.val (Q 6) := by
    show σ1.val (Q 8) + σ1.val (Q 16) * σ1.val (Q 6) = _
    rw [v1 8 (by decide), v1 6 (by decide), h8]; simp [σ1]
  have ec2 : σ1.val (((e5 16 6 8 17 18 (by decide)).trans Q) 1) = σ.val (Q 6) := by
    show σ1.val (Q 6) = _; rw [v1 6 (by decide)]
  have ec0 : σ1.val (((e5 16 6 8 17 18 (by decide)).trans Q) 0) = 4 := by show σ1.val (Q 16) = 4; simp [σ1]
  rw [e2, ec2, ec0] at s2
  have hq2 : ((e5 16 6 8 17 18 (by decide)).trans Q) 2 = Q 8 := rfl
  rw [hq2] at s2
  set σ2 := σ1.setv (Q 8) (4 * σ.val (Q 6)) with hσ2
  have s3 := WExec.inc (cap := cap) (Q 8) σ2 (by simp [σ2]; omega)
  set σ3 := σ2.setv (Q 8) (σ2.val (Q 8) + 1) with hσ3
  have s4 := wclear_spec cap (Q 16) (σ3.val (Q 16)) σ3 rfl (by simp [σ3, σ2, σ1, Function.update_of_ne (qne Q (show (16 : Fin 48) ≠ 8 by decide))]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ ?_
  · apply WState.eq
    · simp [σ3, σ2, σ1]
    · simp [σ3, σ2, σ1]
    · funext r
      simp only [σ3, σ2, σ1, WState.setv_val]
      by_cases hr16 : r = Q 16
      · subst hr16
        rw [Function.update_self, Function.update_of_ne (qne Q (show (16 : Fin 48) ≠ 8 by decide)), h16]
      · rw [Function.update_of_ne hr16]
        by_cases hr8 : r = Q 8
        · subst hr8; simp
        · simp [Function.update_of_ne hr8, Function.update_of_ne hr16]
    · simp [σ3, σ2, σ1]
  · simp [σ3, σ2, σ1]
    nlinarith

/-! ## Steps -/

theorem maQ (i j k t1 t2 : Fin 48) (hinj : Function.Injective ![i, j, k, t1, t2]) (σ : WState ns nr)
    (h1 : σ.val (Q t1) = 0) (h2 : σ.val (Q t2) = 0) (hab : σ.val (Q k) + σ.val (Q i) * σ.val (Q j) ≤ cap)
    (hi : σ.val (Q i) ≤ cap) (hj : σ.val (Q j) ≤ cap) :
    WExec cap (mulAddW ((e5 i j k t1 t2 hinj).trans Q)) σ (σ.setv (Q k) (σ.val (Q k) + σ.val (Q i) * σ.val (Q j)))
      (2 * UnaryPow.sq cap) := by
  have h := mulAddW_spec cap ((e5 i j k t1 t2 hinj).trans Q) σ h1 h2 hj hab hi
  have hs := lin_le_sq cap
  have e : σ.val (Q j) * (18 * σ.val (Q i) + 8) = 18 * (σ.val (Q i) * σ.val (Q j)) + 8 * σ.val (Q j) := by ring
  exact WExec.mono h (by show σ.val (Q j) * (18 * σ.val (Q i) + 8) + 18 * σ.val (Q j) + 10 ≤ _; omega)

theorem incQ (i : Fin 48) (c : ℕ) (σ : WState ns nr) (h : σ.val (Q i) + c ≤ cap) :
    WExec cap (StarNums.incN (Q i) c) σ (σ.setv (Q i) (σ.val (Q i) + c)) (4 * c) :=
  StarNums.incN_spec cap (Q i) c σ h

theorem clrQ (i : Fin 48) (σ : WState ns nr) (h : σ.val (Q i) ≤ cap) :
    WExec cap (WM.clear (Q i)) σ (σ.setv (Q i) 0) (3 * σ.val (Q i) + 1) :=
  wclear_spec cap (Q i) (σ.val (Q i)) σ rfl h

theorem addQ (a v t : Fin 48) (hav : a ≠ v) (hat : a ≠ t) (hvt : v ≠ t) (σ : WState ns nr) (ht : σ.val (Q t) = 0)
    (ha : σ.val (Q a) ≤ cap) (hv : σ.val (Q v) + σ.val (Q a) ≤ cap) :
    WExec cap (addTo (Q a) (Q v) (Q t)) σ (σ.setv (Q v) (σ.val (Q v) + σ.val (Q a))) (18 * σ.val (Q a) + 3) :=
  addTo_spec cap (Q a) (Q v) (Q t) (qne Q hav) (qne Q hat) (qne Q hvt) σ ht ha hv

/-! ## Block B: `Mlab = (4·row + 4)·G` -/

/-- `Q9 := (4·Q1 + 4)·Q0` through `Q16 … Q19`. -/
def blkB : WM ns nr :=
  .seq (StarNums.incN (Q 16) 4) (.seq (mulAddW ((e5 16 1 19 17 18 (by decide)).trans Q))
    (.seq (StarNums.incN (Q 19) 4) (.seq (mulAddW ((e5 19 0 9 17 18 (by decide)).trans Q))
      (.seq (WM.clear (Q 16)) (WM.clear (Q 19))))))

theorem blkB_spec (σ : WState ns nr) (h9 : σ.val (Q 9) = 0) (h16 : σ.val (Q 16) = 0) (h17 : σ.val (Q 17) = 0)
    (h18 : σ.val (Q 18) = 0) (h19 : σ.val (Q 19) = 0)
    (hc : (4 * σ.val (Q 1) + 4) * σ.val (Q 0) + 4 * σ.val (Q 1) + σ.val (Q 0) + 4 ≤ cap) :
    WExec cap (blkB Q) σ (σ.setv (Q 9) ((4 * σ.val (Q 1) + 4) * σ.val (Q 0))) (10 * UnaryPow.sq cap) := by
  have s1 := incQ cap Q 16 4 σ (by omega)
  set σ1 := σ.setv (Q 16) (σ.val (Q 16) + 4) with hσ1
  have s2 := maQ cap Q 16 1 19 17 18 (by decide) σ1 (by simp [σ1, Function.update_apply, h17])
    (by simp [σ1, Function.update_apply, h18]) (by simp [σ1, Function.update_apply, h19, h16]; nlinarith)
    (by simp [σ1, Function.update_apply, h16]; omega) (by simp [σ1, Function.update_apply]; omega)
  set σ2 := σ1.setv (Q 19) (σ1.val (Q 19) + σ1.val (Q 16) * σ1.val (Q 1)) with hσ2
  have v2_19 : σ2.val (Q 19) = 4 * σ.val (Q 1) := by simp [σ2, σ1, Function.update_apply, h19, h16]
  have s3 := incQ cap Q 19 4 σ2 (by rw [v2_19]; omega)
  set σ3 := σ2.setv (Q 19) (σ2.val (Q 19) + 4) with hσ3
  have s4 := maQ cap Q 19 0 9 17 18 (by decide) σ3 (by simp [σ3, σ2, σ1, Function.update_apply, h17])
    (by simp [σ3, σ2, σ1, Function.update_apply, h18])
    (by simp [σ3, σ2, σ1, Function.update_apply, h19, h16, h9]; omega)
    (by simp [σ3, σ2, σ1, Function.update_apply, h19, h16]; omega)
    (by simp [σ3, σ2, σ1, Function.update_apply]; omega)
  set σ4 := σ3.setv (Q 9) (σ3.val (Q 9) + σ3.val (Q 19) * σ3.val (Q 0)) with hσ4
  have s5 := clrQ cap Q 16 σ4 (by simp [σ4, σ3, σ2, σ1, Function.update_apply, h16]; omega)
  set σ5 := σ4.setv (Q 16) 0 with hσ5
  have s6 := clrQ cap Q 19 σ5 (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, h19, h16]; omega)
  have hs := sq_ge cap
  have hl := lin_le_sq cap
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) ?_ ?_
  · apply WState.eq
    · simp [σ5, σ4, σ3, σ2, σ1]
    · simp [σ5, σ4, σ3, σ2, σ1]
    · funext r
      simp only [σ5, σ4, σ3, σ2, σ1, WState.setv_val, Function.update_apply]
      by_cases a19 : r = Q 19
      · subst a19; simp [h19]
      · by_cases a16 : r = Q 16
        · subst a16; simp [h16]
        · by_cases a9 : r = Q 9
          · subst a9; simp [h9, h16, h19]
          · simp [a19, a16, a9]
    · simp [σ5, σ4, σ3, σ2, σ1]
  · simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, h16, h19]
    omega

/-! ## Block C: `lw = M + 2 + S2 + (J+1)·G` -/

/-- `Q10 := Q2 + 2 + Q7 + (Q4 + 1)·Q0` through `Q17, Q18, Q20`. -/
def blkC : WM ns nr :=
  .seq (addTo (Q 2) (Q 10) (Q 17)) (.seq (StarNums.incN (Q 10) 2) (.seq (addTo (Q 7) (Q 10) (Q 17))
    (.seq (addTo (Q 4) (Q 20) (Q 17)) (.seq (StarNums.incN (Q 20) 1)
      (.seq (mulAddW ((e5 20 0 10 17 18 (by decide)).trans Q)) (WM.clear (Q 20)))))))

theorem blkC_spec (σ : WState ns nr) (h10 : σ.val (Q 10) = 0) (h17 : σ.val (Q 17) = 0) (h18 : σ.val (Q 18) = 0)
    (h20 : σ.val (Q 20) = 0)
    (hc : σ.val (Q 2) + 2 + σ.val (Q 7) + (σ.val (Q 4) + 1) * σ.val (Q 0) + σ.val (Q 4) + σ.val (Q 0) + 2 ≤ cap) :
    WExec cap (blkC Q) σ (σ.setv (Q 10) (σ.val (Q 2) + 2 + σ.val (Q 7) + (σ.val (Q 4) + 1) * σ.val (Q 0)))
      (10 * UnaryPow.sq cap) := by
  have s1 := addQ cap Q 2 10 17 (by decide) (by decide) (by decide) σ h17 (by omega) (by omega)
  set σ1 := σ.setv (Q 10) (σ.val (Q 10) + σ.val (Q 2)) with hσ1
  have s2 := incQ cap Q 10 2 σ1 (by simp [σ1, h10]; omega)
  set σ2 := σ1.setv (Q 10) (σ1.val (Q 10) + 2) with hσ2
  have s3 := addQ cap Q 7 10 17 (by decide) (by decide) (by decide) σ2 (by simp [σ2, σ1, Function.update_apply, h17])
    (by simp [σ2, σ1, Function.update_apply]; omega) (by simp [σ2, σ1, Function.update_apply, h10]; omega)
  set σ3 := σ2.setv (Q 10) (σ2.val (Q 10) + σ2.val (Q 7)) with hσ3
  have s4 := addQ cap Q 4 20 17 (by decide) (by decide) (by decide) σ3
    (by simp [σ3, σ2, σ1, Function.update_apply, h17]) (by simp [σ3, σ2, σ1, Function.update_apply]; omega)
    (by simp [σ3, σ2, σ1, Function.update_apply, h20]; omega)
  set σ4 := σ3.setv (Q 20) (σ3.val (Q 20) + σ3.val (Q 4)) with hσ4
  have s5 := incQ cap Q 20 1 σ4 (by simp [σ4, σ3, σ2, σ1, Function.update_apply, h20]; omega)
  set σ5 := σ4.setv (Q 20) (σ4.val (Q 20) + 1) with hσ5
  have s6 := maQ cap Q 20 0 10 17 18 (by decide) σ5 (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, h17])
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, h18])
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, h10, h20]; omega)
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, h20]; omega)
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply]; omega)
  set σ6 := σ5.setv (Q 10) (σ5.val (Q 10) + σ5.val (Q 20) * σ5.val (Q 0)) with hσ6
  have s7 := clrQ cap Q 20 σ6 (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h20]; omega)
  have hs := sq_ge cap
  have hl := lin_le_sq cap
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    s7)))))) ?_ ?_
  · apply WState.eq
    · simp [σ6, σ5, σ4, σ3, σ2, σ1]
    · simp [σ6, σ5, σ4, σ3, σ2, σ1]
    · funext r
      simp only [σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_val, Function.update_apply]
      by_cases a20 : r = Q 20
      · subst a20; simp [h20]
      · by_cases a10 : r = Q 10
        · subst a10; simp [h10, h20]
        · simp [a20, a10]
    · simp [σ6, σ5, σ4, σ3, σ2, σ1]
  · simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h20]
    omega

/-! ## Block D: `X = (8G+2)^{3·lb+1} + M + τ + G + Mlab + lb + lw + p + 4` -/

/-- `Q21 := 8·Q0 + 2`, `Q22 := 3·Q8 + 1` through `Q16 … Q18`. -/
def blkD1 : WM ns nr :=
  .seq (StarNums.incN (Q 16) 8) (.seq (mulAddW ((e5 16 0 21 17 18 (by decide)).trans Q))
    (.seq (StarNums.incN (Q 21) 2) (.seq (WM.clear (Q 16)) (.seq (StarNums.incN (Q 16) 3)
      (.seq (mulAddW ((e5 16 8 22 17 18 (by decide)).trans Q)) (.seq (StarNums.incN (Q 22) 1) (WM.clear (Q 16))))))))

theorem blkD1_spec (σ : WState ns nr) (h16 : σ.val (Q 16) = 0) (h17 : σ.val (Q 17) = 0) (h18 : σ.val (Q 18) = 0)
    (h21 : σ.val (Q 21) = 0) (h22 : σ.val (Q 22) = 0) (hc : 8 * σ.val (Q 0) + 3 * σ.val (Q 8) + 10 ≤ cap) :
    WExec cap (blkD1 Q) σ ((σ.setv (Q 21) (8 * σ.val (Q 0) + 2)).setv (Q 22) (3 * σ.val (Q 8) + 1))
      (12 * UnaryPow.sq cap) := by
  have s1 := incQ cap Q 16 8 σ (by omega)
  set σ1 := σ.setv (Q 16) (σ.val (Q 16) + 8) with hσ1
  have s2 := maQ cap Q 16 0 21 17 18 (by decide) σ1 (by simp [σ1, Function.update_apply, h17])
    (by simp [σ1, Function.update_apply, h18]) (by simp [σ1, Function.update_apply, h21, h16]; omega)
    (by simp [σ1, Function.update_apply, h16]; omega) (by simp [σ1, Function.update_apply]; omega)
  set σ2 := σ1.setv (Q 21) (σ1.val (Q 21) + σ1.val (Q 16) * σ1.val (Q 0)) with hσ2
  have s3 := incQ cap Q 21 2 σ2 (by simp [σ2, σ1, Function.update_apply, h21, h16]; omega)
  set σ3 := σ2.setv (Q 21) (σ2.val (Q 21) + 2) with hσ3
  have s4 := clrQ cap Q 16 σ3 (by simp [σ3, σ2, σ1, Function.update_apply, h16]; omega)
  set σ4 := σ3.setv (Q 16) 0 with hσ4
  have s5 := incQ cap Q 16 3 σ4 (by simp [σ4]; omega)
  set σ5 := σ4.setv (Q 16) (σ4.val (Q 16) + 3) with hσ5
  have s6 := maQ cap Q 16 8 22 17 18 (by decide) σ5 (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, h17])
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, h18])
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, h22]; omega)
    (by simp [σ5, σ4]; omega) (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply]; omega)
  set σ6 := σ5.setv (Q 22) (σ5.val (Q 22) + σ5.val (Q 16) * σ5.val (Q 8)) with hσ6
  have s7 := incQ cap Q 22 1 σ6 (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h22]; omega)
  set σ7 := σ6.setv (Q 22) (σ6.val (Q 22) + 1) with hσ7
  have s8 := clrQ cap Q 16 σ7 (by simp [σ7, σ6, σ5, σ4, Function.update_apply]; omega)
  have hs := sq_ge cap
  have hl := lin_le_sq cap
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 s8))))))) ?_ ?_
  · apply WState.eq
    · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]
    · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]
    · funext r
      simp only [σ7, σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_val, Function.update_apply]
      by_cases a16 : r = Q 16
      · subst a16; simp [h16]
      · by_cases a22 : r = Q 22
        · subst a22; simp [h22]
        · by_cases a21 : r = Q 21
          · subst a21; simp [h21, h16]
          · simp [a16, a22, a21]
    · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h16]
    omega

/-- One power step: `Q22 −= 1`, `Q23 := Q23·Q21` through `Q24`. -/
def powBody : WM ns nr :=
  .seq (.dec (Q 22)) (.seq (mulAddW ((e5 23 21 24 17 18 (by decide)).trans Q))
    (.seq (WM.clear (Q 23)) (WM.move (Q 24) (Q 23))))

/-- `Q23 := Q23·Q21^{Q22}`, `Q22 := 0`. -/
def powLoop : WM ns nr := .whr (Q 22) (powBody Q)

theorem powLoop_spec : ∀ (k : ℕ) (σ : WState ns nr) (b m : ℕ), σ.val (Q 22) = k → σ.val (Q 21) = b →
    σ.val (Q 23) = b ^ m → σ.val (Q 24) = 0 → σ.val (Q 17) = 0 → σ.val (Q 18) = 0 → 1 ≤ b → b ^ (m + k) ≤ cap →
    b ≤ cap → k ≤ cap →
    WExec cap (powLoop Q) σ ((σ.setv (Q 22) 0).setv (Q 23) (b ^ (m + k))) (k * (4 * UnaryPow.sq cap) + 1)
  | 0, σ, b, m, h22, _, h23, _, _, _, _, _, _, _ => by
    have e : (σ.setv (Q 22) 0).setv (Q 23) (b ^ (m + 0)) = σ := by
      apply WState.eq
      · rfl
      · rfl
      · funext r
        simp only [WState.setv_val, Function.update_apply]
        by_cases a23 : r = Q 23
        · subst a23; simp [h23]
        · by_cases a22 : r = Q 22
          · subst a22; simp [h22]
          · simp [a23, a22]
      · rfl
    rw [e]
    exact WExec.mono (WExec.whrF h22) (by omega)
  | k + 1, σ, b, m, h22, h21, h23, h24, h17, h18, hb1, hcap, hb, hk => by
    have hpm : b ^ m ≤ b ^ (m + (k + 1)) := Nat.pow_le_pow_right hb1 (by omega)
    have hpm1 : b ^ (m + 1) ≤ b ^ (m + (k + 1)) := Nat.pow_le_pow_right hb1 (by omega)
    have s1 := WExec.dec (cap := cap) (Q 22) σ (by omega)
    set σ1 := σ.setv (Q 22) (σ.val (Q 22) - 1) with hσ1
    have s2 := maQ cap Q 23 21 24 17 18 (by decide) σ1 (by simp [σ1, Function.update_apply, h17])
      (by simp [σ1, Function.update_apply, h18])
      (by simp [σ1, Function.update_apply, h24, h23, h21]; rw [← pow_succ]; omega)
      (by simp [σ1, Function.update_apply, h23]; omega) (by simp [σ1, Function.update_apply, h21]; omega)
    set σ2 := σ1.setv (Q 24) (σ1.val (Q 24) + σ1.val (Q 23) * σ1.val (Q 21)) with hσ2
    have v24 : σ2.val (Q 24) = b ^ (m + 1) := by simp [σ2, σ1, Function.update_apply, h24, h23, h21, pow_succ]
    have s3 := clrQ cap Q 23 σ2 (by simp [σ2, σ1, Function.update_apply, h23]; omega)
    set σ3 := σ2.setv (Q 23) 0 with hσ3
    have s4 := wmove_spec cap (Q 24) (Q 23) (qne Q (by decide)) (b ^ (m + 1)) σ3
      (by simp [σ3, Function.update_apply]; exact v24) (by simp [σ3, Function.update_apply]; omega)
      (by simp [σ3, Function.update_apply]; omega)
    set σ4 := (σ3.setv (Q 24) 0).setv (Q 23) (σ3.val (Q 23) + σ3.val (Q 24)) with hσ4
    have ih := powLoop_spec k σ4 b (m + 1) (by simp [σ4, σ3, σ2, σ1, Function.update_apply, h22])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, h21]) (by simp [σ4, σ3, Function.update_apply]; exact v24)
      (by simp [σ4, Function.update_apply]) (by simp [σ4, σ3, σ2, σ1, Function.update_apply, h17])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, h18]) hb1 (by rw [show m + 1 + k = m + (k + 1) by omega]; exact hcap)
      hb (by omega)
    have hs := sq_ge cap
    have hl := lin_le_sq cap
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ih) ?_ ?_
    · apply WState.eq
      · rfl
      · rfl
      · funext r
        simp only [σ4, σ3, σ2, σ1, WState.setv_val, Function.update_apply]
        by_cases a23 : r = Q 23
        · subst a23; simp; ring_nf
        · by_cases a22 : r = Q 22
          · subst a22; simp
          · by_cases a24 : r = Q 24
            · subst a24; simp [a23, h24]
            · simp [a23, a22, a24]
      · rfl
    · simp [σ3, σ2, σ1, Function.update_apply, h23, v24]
      have e1 : (k + 1) * (4 * UnaryPow.sq cap) = k * (4 * UnaryPow.sq cap) + 4 * UnaryPow.sq cap := by ring
      omega

/-- `Q23 := Q21^{Q22}`, `Q22 := 0`. -/
def blkD2 : WM ns nr := .seq (StarNums.incN (Q 23) 1) (powLoop Q)

theorem blkD2_spec (σ : WState ns nr) (b e : ℕ) (h21 : σ.val (Q 21) = b) (h22 : σ.val (Q 22) = e)
    (h23 : σ.val (Q 23) = 0) (h24 : σ.val (Q 24) = 0) (h17 : σ.val (Q 17) = 0) (h18 : σ.val (Q 18) = 0) (hb1 : 1 ≤ b)
    (hcap : b ^ e ≤ cap) (hb : b ≤ cap) (he : e ≤ cap) :
    WExec cap (blkD2 Q) σ ((σ.setv (Q 22) 0).setv (Q 23) (b ^ e)) (e * (4 * UnaryPow.sq cap) + 10) := by
  have hp1 : 1 ≤ b ^ e := Nat.one_le_pow _ _ (by omega)
  have s1 := incQ cap Q 23 1 σ (by omega)
  set σ1 := σ.setv (Q 23) (σ.val (Q 23) + 1) with hσ1
  have s2 := powLoop_spec cap Q e σ1 b 0 (by simp [σ1, Function.update_apply, h22])
    (by simp [σ1, Function.update_apply, h21]) (by simp [σ1, h23]) (by simp [σ1, Function.update_apply, h24])
    (by simp [σ1, Function.update_apply, h17]) (by simp [σ1, Function.update_apply, h18]) hb1 (by simpa using hcap) hb he
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by omega)
  apply WState.eq
  · rfl
  · rfl
  · funext r
    simp only [σ1, WState.setv_val, Function.update_apply]
    by_cases a23 : r = Q 23
    · subst a23; simp
    · simp [a23]
  · rfl

/-- `Q11 := Q23 + Q2 + Q3 + Q0 + Q9 + Q8 + Q10 + Q5 + 4`, `Q23, Q21 := 0` through `Q17`. -/
def blkD4 : WM ns nr :=
  .seq (WM.move (Q 23) (Q 11)) (.seq (addTo (Q 2) (Q 11) (Q 17)) (.seq (addTo (Q 3) (Q 11) (Q 17))
    (.seq (addTo (Q 0) (Q 11) (Q 17)) (.seq (addTo (Q 9) (Q 11) (Q 17)) (.seq (addTo (Q 8) (Q 11) (Q 17))
      (.seq (addTo (Q 10) (Q 11) (Q 17)) (.seq (addTo (Q 5) (Q 11) (Q 17)) (.seq (StarNums.incN (Q 11) 4)
        (WM.clear (Q 21))))))))))

theorem blkD4_spec (σ : WState ns nr) (h11 : σ.val (Q 11) = 0) (h17 : σ.val (Q 17) = 0)
    (hc : σ.val (Q 23) + σ.val (Q 2) + σ.val (Q 3) + σ.val (Q 0) + σ.val (Q 9) + σ.val (Q 8) + σ.val (Q 10) +
      σ.val (Q 5) + 4 + σ.val (Q 21) ≤ cap) :
    WExec cap (blkD4 Q) σ (((σ.setv (Q 23) 0).setv (Q 11) (σ.val (Q 23) + σ.val (Q 2) + σ.val (Q 3) + σ.val (Q 0) +
      σ.val (Q 9) + σ.val (Q 8) + σ.val (Q 10) + σ.val (Q 5) + 4)).setv (Q 21) 0) (12 * UnaryPow.sq cap) := by
  have s1 := wmove_spec cap (Q 23) (Q 11) (qne Q (by decide)) (σ.val (Q 23)) σ rfl (by omega) (by omega)
  set σ1 := (σ.setv (Q 23) 0).setv (Q 11) (σ.val (Q 11) + σ.val (Q 23)) with hσ1
  have s2 := addQ cap Q 2 11 17 (by decide) (by decide) (by decide) σ1 (by simp [σ1, Function.update_apply, h17])
    (by simp [σ1, Function.update_apply]; omega) (by simp [σ1, Function.update_apply, h11]; omega)
  set σ2 := σ1.setv (Q 11) (σ1.val (Q 11) + σ1.val (Q 2)) with hσ2
  have s3 := addQ cap Q 3 11 17 (by decide) (by decide) (by decide) σ2 (by simp [σ2, σ1, Function.update_apply, h17])
    (by simp [σ2, σ1, Function.update_apply]; omega) (by simp [σ2, σ1, Function.update_apply, h11]; omega)
  set σ3 := σ2.setv (Q 11) (σ2.val (Q 11) + σ2.val (Q 3)) with hσ3
  have s4 := addQ cap Q 0 11 17 (by decide) (by decide) (by decide) σ3
    (by simp [σ3, σ2, σ1, Function.update_apply, h17])
    (by simp [σ3, σ2, σ1, Function.update_apply]; omega) (by simp [σ3, σ2, σ1, Function.update_apply, h11]; omega)
  set σ4 := σ3.setv (Q 11) (σ3.val (Q 11) + σ3.val (Q 0)) with hσ4
  have s5 := addQ cap Q 9 11 17 (by decide) (by decide) (by decide) σ4
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, h17])
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply]; omega)
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, h11]; omega)
  set σ5 := σ4.setv (Q 11) (σ4.val (Q 11) + σ4.val (Q 9)) with hσ5
  have s6 := addQ cap Q 8 11 17 (by decide) (by decide) (by decide) σ5
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, h17])
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply]; omega)
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, h11]; omega)
  set σ6 := σ5.setv (Q 11) (σ5.val (Q 11) + σ5.val (Q 8)) with hσ6
  have s7 := addQ cap Q 10 11 17 (by decide) (by decide) (by decide) σ6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h17])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; omega)
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h11]; omega)
  set σ7 := σ6.setv (Q 11) (σ6.val (Q 11) + σ6.val (Q 10)) with hσ7
  have s8 := addQ cap Q 5 11 17 (by decide) (by decide) (by decide) σ7
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h17])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; omega)
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h11]; omega)
  set σ8 := σ7.setv (Q 11) (σ7.val (Q 11) + σ7.val (Q 5)) with hσ8
  have s9 := incQ cap Q 11 4 σ8 (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h11]; omega)
  set σ9 := σ8.setv (Q 11) (σ8.val (Q 11) + 4) with hσ9
  have s10 := clrQ cap Q 21 σ9 (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; omega)
  have hs := sq_ge cap
  have hl := lin_le_sq cap
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 (WExec.seq s8 (WExec.seq s9 s10))))))))) ?_ ?_
  · apply WState.eq
    · simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]
    · simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]
    · funext r
      simp only [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_val, Function.update_apply]
      by_cases a21 : r = Q 21
      · subst a21; simp
      · by_cases a11 : r = Q 11
        · subst a11; simp [h11]
        · by_cases a23 : r = Q 23
          · subst a23; simp
          · simp [a21, a11, a23]
    · simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  · simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h11]
    omega

/-! ## Blocks E–H: `U = 2^20·X`, `R = U^40`, `cap = U^45`, `Lg = R + 1` -/

/-- `Q12 := 2^20·Q11`, `Q13 := Q12^40`, `Q14 := Q12^45`, `Q15 := Q13 + 1`. -/
def blkE : WM ns nr :=
  .seq (StarNums.incN (Q 16) 1048576) (.seq (mulAddW ((e5 16 11 12 17 18 (by decide)).trans Q))
    (.seq (WM.clear (Q 16)) (.seq (powConstW ((e5 12 13 25 26 27 (by decide)).trans Q) 40)
      (.seq (powConstW ((e5 12 14 25 26 27 (by decide)).trans Q) 45)
        (.seq (addTo (Q 13) (Q 15) (Q 17)) (StarNums.incN (Q 15) 1))))))

theorem blkE_spec (σ : WState ns nr) (h12 : σ.val (Q 12) = 0) (h13 : σ.val (Q 13) = 0) (h14 : σ.val (Q 14) = 0)
    (h15 : σ.val (Q 15) = 0) (h16 : σ.val (Q 16) = 0) (h17 : σ.val (Q 17) = 0) (h18 : σ.val (Q 18) = 0)
    (h25 : σ.val (Q 25) = 0) (h26 : σ.val (Q 26) = 0) (h27 : σ.val (Q 27) = 0)
    (hc : (1048576 * σ.val (Q 11)) ^ 45 + 1048576 ≤ cap) (hX : 1 ≤ σ.val (Q 11)) :
    WExec cap (blkE Q) σ ((((σ.setv (Q 12) (1048576 * σ.val (Q 11))).setv (Q 13) ((1048576 * σ.val (Q 11)) ^ 40)).setv
      (Q 14) ((1048576 * σ.val (Q 11)) ^ 45)).setv (Q 15) ((1048576 * σ.val (Q 11)) ^ 40 + 1)) (400 * UnaryPow.sq cap) := by
  set U := 1048576 * σ.val (Q 11) with hU
  have hU1 : 1 ≤ U := by rw [hU]; omega
  have hUk : ∀ k ≤ 45, U ^ k ≤ cap := fun k hk => le_trans (Nat.pow_le_pow_right hU1 hk) (by omega)
  have hU40 := hUk 40 (by norm_num)
  have hU1c := hUk 1 (by norm_num)
  rw [pow_one] at hU1c
  have hXU : σ.val (Q 11) ≤ U := by rw [hU]; omega
  have s1 := incQ cap Q 16 1048576 σ (by omega)
  set σ1 := σ.setv (Q 16) (σ.val (Q 16) + 1048576) with hσ1
  have s2 := maQ cap Q 16 11 12 17 18 (by decide) σ1 (by simp [σ1, Function.update_apply, h17])
    (by simp [σ1, Function.update_apply, h18]) (by simp [σ1, Function.update_apply, h12, h16]; omega)
    (by simp [σ1, Function.update_apply, h16]; omega) (by simp [σ1, Function.update_apply]; omega)
  set σ2 := σ1.setv (Q 12) (σ1.val (Q 12) + σ1.val (Q 16) * σ1.val (Q 11)) with hσ2
  have v2 : σ2.val (Q 12) = U := by simp [σ2, σ1, Function.update_apply, h12, h16, hU]
  have s3 := clrQ cap Q 16 σ2 (by simp [σ2, σ1, Function.update_apply, h16]; omega)
  set σ3 := σ2.setv (Q 16) 0 with hσ3
  have v3 : σ3.val (Q 12) = U := by simp [σ3, Function.update_apply, v2]
  have s4 := powConstW_spec cap ((e5 12 13 25 26 27 (by decide)).trans Q) 40 σ3
    (by show σ3.val (Q 13) = 0; simp [σ3, σ2, σ1, Function.update_apply, h13])
    (by show σ3.val (Q 25) = 0; simp [σ3, σ2, σ1, Function.update_apply, h25])
    (by show σ3.val (Q 26) = 0; simp [σ3, σ2, σ1, Function.update_apply, h26])
    (by show σ3.val (Q 27) = 0; simp [σ3, σ2, σ1, Function.update_apply, h27])
    (by omega) (by show σ3.val (Q 12) ≤ cap; rw [v3]; exact hU1c)
    (fun k hk => by show σ3.val (Q 12) ^ k ≤ cap; rw [v3]; exact hUk k (by omega))
  have e4 : ((e5 12 13 25 26 27 (by decide)).trans Q) 1 = Q 13 := rfl
  have e4' : ((e5 12 13 25 26 27 (by decide)).trans Q) 0 = Q 12 := rfl
  rw [e4, e4', v3] at s4
  set σ4 := σ3.setv (Q 13) (U ^ 40) with hσ4
  have v4 : σ4.val (Q 12) = U := by simp [σ4, Function.update_apply, v3]
  have s5 := powConstW_spec cap ((e5 12 14 25 26 27 (by decide)).trans Q) 45 σ4
    (by show σ4.val (Q 14) = 0; simp [σ4, σ3, σ2, σ1, Function.update_apply, h14])
    (by show σ4.val (Q 25) = 0; simp [σ4, σ3, σ2, σ1, Function.update_apply, h25])
    (by show σ4.val (Q 26) = 0; simp [σ4, σ3, σ2, σ1, Function.update_apply, h26])
    (by show σ4.val (Q 27) = 0; simp [σ4, σ3, σ2, σ1, Function.update_apply, h27])
    (by omega) (by show σ4.val (Q 12) ≤ cap; rw [v4]; exact hU1c)
    (fun k hk => by show σ4.val (Q 12) ^ k ≤ cap; rw [v4]; exact hUk k hk)
  have e5' : ((e5 12 14 25 26 27 (by decide)).trans Q) 1 = Q 14 := rfl
  have e5'' : ((e5 12 14 25 26 27 (by decide)).trans Q) 0 = Q 12 := rfl
  rw [e5', e5'', v4] at s5
  set σ5 := σ4.setv (Q 14) (U ^ 45) with hσ5
  have v5_13 : σ5.val (Q 13) = U ^ 40 := by simp [σ5, σ4, Function.update_apply]
  have v5_15 : σ5.val (Q 15) = 0 := by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, h15]
  have s6 := addQ cap Q 13 15 17 (by decide) (by decide) (by decide) σ5
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, h17])
    (by rw [v5_13]; exact hU40) (by rw [v5_13, v5_15]; omega)
  set σ6 := σ5.setv (Q 15) (σ5.val (Q 15) + σ5.val (Q 13)) with hσ6
  have hUlt : U ^ 40 < U ^ 45 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hU45 := hUk 45 le_rfl
  have v6 : σ6.val (Q 15) = U ^ 40 := by simp [σ6, Function.update_apply, v5_13, v5_15]
  have s7 := incQ cap Q 15 1 σ6 (by rw [v6]; omega)
  have hs := sq_ge cap
  have hl := lin_le_sq cap
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    s7)))))) ?_ ?_
  · apply WState.eq
    · simp [σ6, σ5, σ4, σ3, σ2, σ1]
    · simp [σ6, σ5, σ4, σ3, σ2, σ1]
    · funext r
      simp only [σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_val, Function.update_apply]
      by_cases a15 : r = Q 15
      · subst a15; simp [h15]
      · by_cases a14 : r = Q 14
        · subst a14; simp
        · by_cases a13 : r = Q 13
          · subst a13; simp
          · by_cases a16 : r = Q 16
            · subst a16; simp [h16]
            · by_cases a12 : r = Q 12
              · subst a12; simp [h12, h16, hU]
              · simp [a15, a14, a13, a16, a12]
    · simp [σ6, σ5, σ4, σ3, σ2, σ1]
  · have h2e : 1048576 ≤ cap := by omega
    simp [σ3, σ2, σ1, Function.update_apply, h16, v5_13]
    omega

/-! ## The whole program -/

/-- **Route B's numbers** (`Q0 … Q7` = `G`, row, `M`, `τ`, `J`, `p`, `S1`, `S2`; `Q8 … Q15` = `lb`, `Mlab`, `lw`, `X`,
`U`, `R`, `cap`, `Lg`; `Q16 … Q27` scratch). -/
def numsP : WM ns nr :=
  .seq (blkA Q) (.seq (blkB Q) (.seq (blkC Q) (.seq (blkD1 Q) (.seq (blkD2 Q) (.seq (blkD4 Q) (blkE Q))))))

/-- The program's final registers. -/
def numsOut (σ : WState ns nr) (lb Mlab lw X U : ℕ) : WState ns nr :=
  (((((((σ.setv (Q 8) lb).setv (Q 9) Mlab).setv (Q 10) lw).setv (Q 11) X).setv (Q 12) U).setv (Q 13) (U ^ 40)).setv
    (Q 14) (U ^ 45)).setv (Q 15) (U ^ 40 + 1)

/-- The program's cost. -/
def numsCost (c : ℕ) : ℕ := (c + 1000) * (4 * UnaryPow.sq c)

theorem numsP_spec (σ : WState ns nr) (G row M τ J p S1 S2 : ℕ) (h0 : σ.val (Q 0) = G) (h1 : σ.val (Q 1) = row)
    (h2 : σ.val (Q 2) = M) (h3 : σ.val (Q 3) = τ) (h4 : σ.val (Q 4) = J) (h5 : σ.val (Q 5) = p)
    (h6 : σ.val (Q 6) = S1) (h7 : σ.val (Q 7) = S2) (hz : ∀ i : Fin 48, 8 ≤ i.val → i.val < 28 → σ.val (Q i) = 0)
    (hcap : (1048576 * RadSpec.radX M τ G ((4 * row + 4) * G) (4 * S1 + 1) (M + 2 + S2 + (J + 1) * G) p 2) ^ 45 +
      1048576 + 4 * row + J + 8 ≤ cap) :
    WExec cap (numsP Q) σ (numsOut Q σ (4 * S1 + 1) ((4 * row + 4) * G) (M + 2 + S2 + (J + 1) * G)
      (RadSpec.radX M τ G ((4 * row + 4) * G) (4 * S1 + 1) (M + 2 + S2 + (J + 1) * G) p 2)
      (1048576 * RadSpec.radX M τ G ((4 * row + 4) * G) (4 * S1 + 1) (M + 2 + S2 + (J + 1) * G) p 2))
      (numsCost cap) := by
  obtain ⟨X, hXd⟩ : ∃ X, RadSpec.radX M τ G ((4 * row + 4) * G) (4 * S1 + 1) (M + 2 + S2 + (J + 1) * G) p 2 = X :=
    ⟨_, rfl⟩
  rw [hXd] at hcap ⊢
  have eX : X = (8 * G + 2) ^ (3 * (4 * S1 + 1) + 1) + M + τ + G + (4 * row + 4) * G + (4 * S1 + 1) +
      (M + 2 + S2 + (J + 1) * G) + p + 4 := by rw [← hXd]; unfold RadSpec.radX; omega
  have hP1 : 8 * G + 2 ≤ (8 * G + 2) ^ (3 * (4 * S1 + 1) + 1) := Nat.le_self_pow (by omega) _
  have hX1 : 1 ≤ X := by omega
  have hU45 : 1048576 * X ≤ (1048576 * X) ^ 45 := Nat.le_self_pow (by norm_num) _
  have z : ∀ i : Fin 48, 8 ≤ i.val → i.val < 28 → σ.val (Q i) = 0 := hz
  -- A
  have sA := blkA_spec cap Q σ (z 8 (by decide) (by decide)) (z 16 (by decide) (by decide))
    (z 17 (by decide) (by decide)) (z 18 (by decide) (by decide)) (by rw [h6]; omega)
  rw [h6] at sA
  set σA := σ.setv (Q 8) (4 * S1 + 1) with hσA
  have zA : ∀ i : Fin 48, 8 < i.val → i.val < 28 → σA.val (Q i) = 0 := fun i hi1 hi2 => by
    have hne : i ≠ 8 := fun h => by subst h; simp at hi1
    simp [σA, Function.update_of_ne (qne Q hne), z i (by omega) hi2]
  have vA : ∀ i : Fin 48, i.val < 8 → σA.val (Q i) = σ.val (Q i) := fun i h => by
    have hne : i ≠ 8 := fun h' => by subst h'; simp at h
    simp [σA, Function.update_of_ne (qne Q hne)]
  -- B
  have sB := blkB_spec cap Q σA (zA 9 (by decide) (by decide)) (zA 16 (by decide) (by decide))
    (zA 17 (by decide) (by decide)) (zA 18 (by decide) (by decide)) (zA 19 (by decide) (by decide))
    (by rw [vA 1 (by decide), vA 0 (by decide), h1, h0]; omega)
  rw [vA 1 (by decide), vA 0 (by decide), h1, h0] at sB
  set σB := σA.setv (Q 9) ((4 * row + 4) * G) with hσB
  have zB : ∀ i : Fin 48, 9 < i.val → i.val < 28 → σB.val (Q i) = 0 := fun i hi1 hi2 => by
    have hne : i ≠ 9 := fun h => by subst h; simp at hi1
    simp [σB, Function.update_of_ne (qne Q hne), zA i (by omega) hi2]
  have vB : ∀ i : Fin 48, i.val < 8 → σB.val (Q i) = σ.val (Q i) := fun i h => by
    have hne : i ≠ 9 := fun h' => by subst h'; simp at h
    simp [σB, Function.update_of_ne (qne Q hne), vA i h]
  -- C
  have sC := blkC_spec cap Q σB (zB 10 (by decide) (by decide)) (zB 17 (by decide) (by decide))
    (zB 18 (by decide) (by decide)) (zB 20 (by decide) (by decide))
    (by rw [vB 2 (by decide), vB 7 (by decide), vB 4 (by decide), vB 0 (by decide), h2, h7, h4, h0]; omega)
  rw [vB 2 (by decide), vB 7 (by decide), vB 4 (by decide), vB 0 (by decide), h2, h7, h4, h0] at sC
  set σC := σB.setv (Q 10) (M + 2 + S2 + (J + 1) * G) with hσC
  have zC : ∀ i : Fin 48, 10 < i.val → i.val < 28 → σC.val (Q i) = 0 := fun i hi1 hi2 => by
    have hne : i ≠ 10 := fun h => by subst h; simp at hi1
    simp [σC, Function.update_of_ne (qne Q hne), zB i (by omega) hi2]
  have vC : ∀ i : Fin 48, i.val < 8 → σC.val (Q i) = σ.val (Q i) := fun i h => by
    have hne : i ≠ 10 := fun h' => by subst h'; simp at h
    simp [σC, Function.update_of_ne (qne Q hne), vB i h]
  have vC8 : σC.val (Q 8) = 4 * S1 + 1 := by simp [σC, σB, σA, Function.update_apply]
  have vC9 : σC.val (Q 9) = (4 * row + 4) * G := by simp [σC, σB, Function.update_apply]
  have vC10 : σC.val (Q 10) = M + 2 + S2 + (J + 1) * G := by simp [σC]
  -- D1
  have sD1 := blkD1_spec cap Q σC (zC 16 (by decide) (by decide)) (zC 17 (by decide) (by decide))
    (zC 18 (by decide) (by decide)) (zC 21 (by decide) (by decide)) (zC 22 (by decide) (by decide))
    (by rw [vC 0 (by decide), vC8, h0]; omega)
  rw [vC 0 (by decide), vC8, h0] at sD1
  set σD1 := (σC.setv (Q 21) (8 * G + 2)).setv (Q 22) (3 * (4 * S1 + 1) + 1) with hσD1
  -- D2
  have sD2 := blkD2_spec cap Q σD1 (8 * G + 2) (3 * (4 * S1 + 1) + 1) (by simp [σD1, Function.update_apply])
    (by simp [σD1]) (by simp [σD1, Function.update_apply, zC 23 (by decide) (by decide)])
    (by simp [σD1, Function.update_apply, zC 24 (by decide) (by decide)])
    (by simp [σD1, Function.update_apply, zC 17 (by decide) (by decide)])
    (by simp [σD1, Function.update_apply, zC 18 (by decide) (by decide)]) (by omega) (by omega) (by omega) (by omega)
  set σD2 := (σD1.setv (Q 22) 0).setv (Q 23) ((8 * G + 2) ^ (3 * (4 * S1 + 1) + 1)) with hσD2
  -- D4
  have eD4 : ∀ i : Fin 48, i.val < 8 → σD2.val (Q i) = σ.val (Q i) := fun i h => by
    have h21 : i ≠ 21 := fun h' => by subst h'; simp at h
    have h22 : i ≠ 22 := fun h' => by subst h'; simp at h
    have h23 : i ≠ 23 := fun h' => by subst h'; simp at h
    simp [σD2, σD1, Function.update_of_ne (qne Q h21), Function.update_of_ne (qne Q h22),
      Function.update_of_ne (qne Q h23), vC i h]
  have wD8 : σD2.val (Q 8) = 4 * S1 + 1 := by simp [σD2, σD1, Function.update_apply, vC8]
  have wD9 : σD2.val (Q 9) = (4 * row + 4) * G := by simp [σD2, σD1, Function.update_apply, vC9]
  have wD10 : σD2.val (Q 10) = M + 2 + S2 + (J + 1) * G := by simp [σD2, σD1, Function.update_apply, vC10]
  have wD23 : σD2.val (Q 23) = (8 * G + 2) ^ (3 * (4 * S1 + 1) + 1) := by simp [σD2]
  have wD21 : σD2.val (Q 21) = 8 * G + 2 := by simp [σD2, σD1, Function.update_apply]
  have sD4 := blkD4_spec cap Q σD2 (by simp [σD2, σD1, Function.update_apply, zC 11 (by decide) (by decide)])
    (by simp [σD2, σD1, Function.update_apply, zC 17 (by decide) (by decide)])
    (by rw [wD23, eD4 2 (by decide), eD4 3 (by decide), eD4 0 (by decide), wD9, wD8, wD10, eD4 5 (by decide), wD21,
          h2, h3, h0, h5]
        omega)
  rw [wD23, eD4 2 (by decide), eD4 3 (by decide), eD4 0 (by decide), wD9, wD8, wD10, eD4 5 (by decide), h2, h3, h0,
    h5, ← eX] at sD4
  set σD4 := ((σD2.setv (Q 23) 0).setv (Q 11) X).setv (Q 21) 0 with hσD4
  -- E
  have wz : ∀ i : Fin 48, (i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 25 ∨ i = 26 ∨ i = 27) →
      σD4.val (Q i) = 0 := fun i hi => by
    have h11 : i ≠ 11 := by rcases hi with h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
    have h21 : i ≠ 21 := by rcases hi with h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
    have h22 : i ≠ 22 := by rcases hi with h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
    have h23 : i ≠ 23 := by rcases hi with h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
    have hi' : 10 < i.val ∧ i.val < 28 := by rcases hi with h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
    simp [σD4, σD2, σD1, Function.update_of_ne (qne Q h11), Function.update_of_ne (qne Q h21),
      Function.update_of_ne (qne Q h22), Function.update_of_ne (qne Q h23), zC i hi'.1 hi'.2]
  have wD11 : σD4.val (Q 11) = X := by simp [σD4, Function.update_apply]
  have sE := blkE_spec cap Q σD4 (wz 12 (by decide)) (wz 13 (by decide)) (wz 14 (by decide)) (wz 15 (by decide))
    (wz 16 (by decide)) (wz 17 (by decide)) (wz 18 (by decide)) (wz 25 (by decide)) (wz 26 (by decide))
    (wz 27 (by decide)) (by rw [wD11]; omega) (by rw [wD11]; omega)
  rw [wD11] at sE
  have hs := sq_ge cap
  have hl := lin_le_sq cap
  refine WExec.cast cap (WExec.seq sA (WExec.seq sB (WExec.seq sC (WExec.seq sD1 (WExec.seq sD2 (WExec.seq sD4
    sE)))))) ?_ ?_
  · apply WState.eq
    · simp [σD4, σD2, σD1, σC, σB, σA, numsOut]
    · simp [σD4, σD2, σD1, σC, σB, σA, numsOut]
    · funext r
      simp only [σD4, σD2, σD1, σC, σB, σA, numsOut, WState.setv_val, Function.update_apply]
      by_cases a21 : r = Q 21
      · subst a21; simp [z 21 (by decide) (by decide)]
      · by_cases a22 : r = Q 22
        · subst a22; simp [z 22 (by decide) (by decide)]
        · by_cases a23 : r = Q 23
          · subst a23; simp [z 23 (by decide) (by decide)]
          · simp [a21, a22, a23]
    · simp [σD4, σD2, σD1, σC, σB, σA, numsOut]
  · have e3 : 3 * (4 * S1 + 1) + 1 ≤ cap := by omega
    unfold numsCost
    have hmul : (3 * (4 * S1 + 1) + 1) * (4 * UnaryPow.sq cap) ≤ cap * (4 * UnaryPow.sq cap) :=
      Nat.mul_le_mul_right _ e3
    have e1 : 100 * (S1 + 10) ≤ UnaryPow.sq cap := by omega
    have e2 : (cap + 1000) * (4 * UnaryPow.sq cap) = cap * (4 * UnaryPow.sq cap) + 4000 * UnaryPow.sq cap := by ring
    omega

end NearCubicWires.WireExponent3_5.UnionMachine.RadNums
