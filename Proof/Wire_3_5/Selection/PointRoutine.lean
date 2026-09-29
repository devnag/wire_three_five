import Proof.Wire_3_5.Selection.PointBlock

/-! # C1.4: the point routine (P3:1339-1344, 1195-1197)

Paper: "For each gate and row, the four threshold predicates have integer scores of the form `a_j(z_L) + b_j(z_R)`"
(P3:1341-1342); a point of a half is valid only when every block's syndrome is the coset's code (P3:1195-1197). The
routine: `AC, AC' := init`, `OK := 1`; the coset word's head steps to segment `o`; the `h` blocks (`blk`); the free
positions (`posF`); if `OK = 0` the point is the null point (`AC, AC' := init`); every head returns. Main declarations:
**`blocks_spec`**, **`frees_spec`**, `pointR`, **`pointR_spec`**. Paper quantity: a half's pair of integer scores
(offset keys), or the null point. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit (cloop cloop_spec)

variable {ns nr : ℕ}

/-- The running coset test over the first `t` blocks. -/
def okB (c : ℕ → Bool) (b s o N : ℕ) : ℕ → Bool
  | 0 => true
  | t + 1 => okB c b s o N t && decide (synC c (t * b) b = N / 2 ^ (s * (o + t)) % 2 ^ s)

/-- The magnitude word after `P` positions (the last record read). -/
def wvAt (recs : List (Bool × ℕ)) (wv0 P : ℕ) : ℕ := if P = 0 then wv0 else (recAt recs (P - 1)).2

section Blocks
variable {S : Fin 12 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 20 → Fin nr} (hQ : Function.Injective Q)
variable (cap s W : ℕ) (σ0 : WState ns nr)
variable (h0C : σ0.sh (S 4) = 0) (h0Y : σ0.sh (S 5) = 0) (h0A : σ0.sh (S 6) = 0) (h0A' : σ0.sh (S 7) = 0)
  (h0V : σ0.sh (S 8) = 0) (h0F : σ0.val (Q 0) = 0) (h0R : σ0.val (Q 1) = 0)
include hS hQ h0C h0Y h0A h0A' h0V h0F h0R

/-- **The blocks of a half**: after `h` blocks, the sums over the `h·b` block positions and the coset test. -/
theorem blocks_spec (recs : List (Bool × ℕ)) (x wx u wu N wn hh b o wv0 : ℕ) (init : ℤ) (fl : ℕ → Bool)
    (hX : σ0.st (S 0) = frame (binary wx x)) (hU : σ0.st (S 1) = frame (binary wu u))
    (hN : σ0.st (S 2) = frame (binary wn N)) (hT : σ0.st (S 3) = tbl W recs)
    (hb : b < 2 ^ s) (hL : hh * b ≤ recs.length) (hLx : hh * b ≤ wx) (hLu : s * hh ≤ wu) (hLn : s * (o + hh) ≤ wn)
    (hfl : ∀ t < hh, ∀ j < b, decide (binary s (j + 1) = binary s (u / 2 ^ (s * t))) = fl (t * b + j))
    (hR : ∀ P ≤ hh * b, (0 ≤ accC init (zAt recs) x.testBit P ∧ accC init (zAt recs) x.testBit P < 2 ^ W) ∧
      (0 ≤ accC init (zAt recs) (fun p => xor (x.testBit p) (fl p)) P ∧
        accC init (zAt recs) (fun p => xor (x.testBit p) (fl p)) P < 2 ^ W))
    (hK9 : σ0.val (Q 9) = b) (hK10 : σ0.val (Q 10) = hh) (hK11 : σ0.val (Q 11) = s) (hT14 : σ0.val (Q 14) = 0)
    (hT15 : σ0.val (Q 15) = 0)
    (hcap : 2 * s + 1 ≤ cap) (hcapW : 2 * W + 1 ≤ cap) (hcapT : hh * b * (2 * W + 2) ≤ cap)
    (hcapX : 2 * (hh * b) ≤ cap) (hcapb : b ≤ cap) (hcaph : hh ≤ cap) (hcapU : 2 * (s * hh) ≤ cap)
    (hcapN : 2 * (s * (o + hh)) ≤ cap) :
    WExec cap (cloop (Q 10) (Q 14) (blk S Q))
      (mkP S Q s W σ0 0 0 0 (2 * (s * o)) 0 0 (accC init (zAt recs) x.testBit 0).toNat
        (accC init (zAt recs) (fun p => xor (x.testBit p) (fl p)) 0).toNat 1 0 0 wv0)
      (mkP S Q s W σ0 (2 * (hh * b)) (hh * b * (2 * W + 2)) (2 * (s * hh)) (2 * (s * (o + hh))) 0 0
        (accC init (zAt recs) x.testBit (hh * b)).toNat
        (accC init (zAt recs) (fun p => xor (x.testBit p) (fl p)) (hh * b)).toNat
        (okB x.testBit b s o N hh).toNat 0 0 (wvAt recs wv0 (hh * b)))
      (hh * (b * (180 * W + 125 * s + 118) + 3 + 7 * b + 1 + (180 * s + 40) + 8) + 1 + 1 + (7 * hh + 1)) := by
  set c' : ℕ → Bool := fun p => xor (x.testBit p) (fl p) with hc'
  let M : WState ns nr → ℕ → WState ns nr := fun σ t =>
    mkP S Q s W σ (2 * (t * b)) (t * b * (2 * W + 2)) (2 * (s * t)) (2 * (s * (o + t))) 0 0
      (accC init (zAt recs) x.testBit (t * b)).toNat (accC init (zAt recs) c' (t * b)).toNat
      (okB x.testBit b s o N t).toNat 0 0 (wvAt recs wv0 (t * b))
  have hl := cloopM cap (Q 10) (Q 14) (hQ.ne (by decide)) (blk S Q) M
    (fun σ j v w => mkP_setv2 hS hQ s W σ 10 14 (by decide) (by decide) v w _ _ _ _ _ _ _ _ _ _ _ _) σ0 hh
    (b * (180 * W + 125 * s + 118) + 3 + 7 * b + 1 + (180 * s + 40)) hK10 hT14 hcaph (by
      intro t ht v w
      set σv := (σ0.setv (Q 10) v).setv (Q 14) w with hσv
      have hQ0 : σv.val (Q 0) = 0 := by simp [hσv, Function.update_apply, hQ.eq_iff, h0F]
      have hQ1 : σv.val (Q 1) = 0 := by simp [hσv, Function.update_apply, hQ.eq_iff, h0R]
      have hQ9 : σv.val (Q 9) = b := by simp [hσv, Function.update_apply, hQ.eq_iff, hK9]
      have hQ11 : σv.val (Q 11) = s := by simp [hσv, Function.update_apply, hQ.eq_iff, hK11]
      have hQ15 : σv.val (Q 15) = 0 := by simp [hσv, Function.update_apply, hQ.eq_iff, hT15]
      have htb : t * b + b ≤ hh * b := by
        have := Nat.mul_le_mul_right b (show t + 1 ≤ hh by omega); rwa [add_one_mul] at this
      have hst : s * t + s ≤ s * hh := by
        have := Nat.mul_le_mul_left s (show t + 1 ≤ hh by omega); rwa [Nat.mul_add, Nat.mul_one] at this
      have hsot : s * (o + t) + s ≤ s * (o + hh) := by
        have := Nat.mul_le_mul_left s (show o + t + 1 ≤ o + hh by omega); rwa [Nat.mul_add s (o + t) 1, Nat.mul_one] at this
      have x1 := blkPos_spec hS hQ cap s W σv h0C h0Y h0A h0A' h0V hQ0 hQ1 recs x wx u wu t b (2 * (s * (o + t)))
        (okB x.testBit b s o N t).toNat (wvAt recs wv0 (t * b)) init fl hX hU hT hb (by omega) (by omega)
        (by omega) (hfl t ht) (fun P hP => hR P (by omega)) hQ9 hQ15 hcap hcapW
        (le_trans (Nat.mul_le_mul_right _ htb) hcapT) (by omega) hcapb
      have hsy := synC_lt x.testBit (t * b) s b hb
      have x2 := blkEnd_spec hS hQ cap s W σv h0C h0Y h0A h0A' h0V hQ0 hQ1 N wn o t (2 * (t * b + b))
        ((t * b + b) * (2 * W + 2)) b (synC x.testBit (t * b) b) (accC init (zAt recs) x.testBit (t * b + b)).toNat
        (accC init (zAt recs) c' (t * b + b)).toNat (okB x.testBit b s o N t).toNat
        (if b = 0 then wvAt recs wv0 (t * b) else (recAt recs (t * b + b - 1)).2) hN (by omega) hsy
        (by cases okB x.testBit b s o N t <;> simp) hQ11 hQ15 hcap (by omega) (by omega)
      refine WExec.cast cap (WExec.seq x1 x2) ?_ le_rfl
      simp only [M]
      have e1 : (t + 1) * b = t * b + b := add_one_mul t b
      have eok : (if synC x.testBit (t * b) b = N / 2 ^ (s * (o + t)) % 2 ^ s then (okB x.testBit b s o N t).toNat
          else 0) = (okB x.testBit b s o N (t + 1)).toNat := by
        simp only [okB]
        cases okB x.testBit b s o N t <;> by_cases h : synC x.testBit (t * b) b = N / 2 ^ (s * (o + t)) % 2 ^ s <;>
          simp [h]
      have ewv : (if b = 0 then wvAt recs wv0 (t * b) else (recAt recs (t * b + b - 1)).2) =
          wvAt recs wv0 (t * b + b) := by
        by_cases hb0 : b = 0
        · subst hb0; simp
        · unfold wvAt
          rw [if_neg hb0, if_neg (by omega)]
      rw [e1, eok, ewv])
  simp only [M] at hl
  have e0 : mkP S Q s W σ0 (2 * (0 * b)) (0 * b * (2 * W + 2)) (2 * (s * 0)) (2 * (s * (o + 0))) 0 0
      (accC init (zAt recs) x.testBit (0 * b)).toNat (accC init (zAt recs) c' (0 * b)).toNat
      (okB x.testBit b s o N 0).toNat 0 0 (wvAt recs wv0 (0 * b)) =
      mkP S Q s W σ0 0 0 0 (2 * (s * o)) 0 0 (accC init (zAt recs) x.testBit 0).toNat
        (accC init (zAt recs) c' 0).toNat 1 0 0 wv0 := by
    simp [okB, wvAt]
  rw [e0] at hl
  exact hl

/-- **The free positions of a half**: after `f` free positions (no flip), both sums are complete. -/
theorem frees_spec (recs : List (Bool × ℕ)) (x wx hb f pU pN ok wv0 : ℕ) (init : ℤ) (fl : ℕ → Bool)
    (hX : σ0.st (S 0) = frame (binary wx x)) (hT : σ0.st (S 3) = tbl W recs)
    (hL : hb + f ≤ recs.length) (hLx : hb + f ≤ wx) (hfl0 : ∀ p, hb ≤ p → fl p = false)
    (hR : ∀ P ≤ hb + f, (0 ≤ accC init (zAt recs) x.testBit P ∧ accC init (zAt recs) x.testBit P < 2 ^ W) ∧
      (0 ≤ accC init (zAt recs) (fun p => xor (x.testBit p) (fl p)) P ∧
        accC init (zAt recs) (fun p => xor (x.testBit p) (fl p)) P < 2 ^ W))
    (hK12 : σ0.val (Q 12) = f) (hT14 : σ0.val (Q 14) = 0)
    (hcapW : 2 * W + 1 ≤ cap) (hcapT : (hb + f) * (2 * W + 2) ≤ cap) (hcapX : 2 * (hb + f) ≤ cap) (hcapf : f ≤ cap) :
    WExec cap (cloop (Q 12) (Q 14) (posF S Q))
      (mkP S Q s W σ0 (2 * hb) (hb * (2 * W + 2)) pU pN 0 0 (accC init (zAt recs) x.testBit hb).toNat
        (accC init (zAt recs) (fun p => xor (x.testBit p) (fl p)) hb).toNat ok 0 0 (wvAt recs wv0 hb))
      (mkP S Q s W σ0 (2 * (hb + f)) ((hb + f) * (2 * W + 2)) pU pN 0 0
        (accC init (zAt recs) x.testBit (hb + f)).toNat
        (accC init (zAt recs) (fun p => xor (x.testBit p) (fl p)) (hb + f)).toNat ok 0 0 (wvAt recs wv0 (hb + f)))
      (f * (140 * W + 70 + 8) + 1 + 1 + (7 * f + 1)) := by
  set c' : ℕ → Bool := fun p => xor (x.testBit p) (fl p) with hc'
  let M : WState ns nr → ℕ → WState ns nr := fun σ j =>
    mkP S Q s W σ (2 * (hb + j)) ((hb + j) * (2 * W + 2)) pU pN 0 0 (accC init (zAt recs) x.testBit (hb + j)).toNat
      (accC init (zAt recs) c' (hb + j)).toNat ok 0 0 (wvAt recs wv0 (hb + j))
  have hl := cloopM cap (Q 12) (Q 14) (hQ.ne (by decide)) (posF S Q) M
    (fun σ j v w => mkP_setv2 hS hQ s W σ 12 14 (by decide) (by decide) v w _ _ _ _ _ _ _ _ _ _ _ _) σ0 f
    (140 * W + 70) hK12 hT14 hcapf (by
      intro j hj v w
      set σv := (σ0.setv (Q 12) v).setv (Q 14) w with hσv
      have hQ0 : σv.val (Q 0) = 0 := by simp [hσv, Function.update_apply, hQ.eq_iff, h0F]
      have hQ1 : σv.val (Q 1) = 0 := by simp [hσv, Function.update_apply, hQ.eq_iff, h0R]
      have hp : hb + j < recs.length := by omega
      have hsplit := tbl_split W recs (hb + j) hp
      have hlen : (tbl W (recs.take (hb + j))).length = (hb + j) * (2 * W + 2) := by
        rw [tbl_length, List.length_take, Nat.min_eq_left (by omega)]
      have hbit : readTapeBit (σv.st (S 0)) (2 * (hb + j) + 1) = x.testBit (hb + j) := by
        simp only [hσv, WState.setv_st, hX]
        exact rd_frame_bit wx x (hb + j) (by omega)
      have hRj := hR (hb + j) (by omega)
      have hfj : fl (hb + j) = false := hfl0 (hb + j) (by omega)
      have h := posF_spec hS hQ cap s W σv h0C h0Y h0A h0A' h0V hQ0 hQ1 (2 * (hb + j)) pU pN 0 0
        (accC init (zAt recs) x.testBit (hb + j)).toNat (accC init (zAt recs) c' (hb + j)).toNat ok
        (wvAt recs wv0 (hb + j)) (tbl W (recs.take (hb + j))) (tbl W (recs.drop (hb + j + 1)))
        (recAt recs (hb + j)).1 (recAt recs (hb + j)).2 (x.testBit (hb + j))
        (by simp only [hσv, WState.setv_st, hT, hsplit, List.append_assoc]) hbit
        (by
          intro hbt
          rw [Int.toNat_of_nonneg hRj.1.1]
          have h2 : 0 ≤ accC init (zAt recs) x.testBit (hb + j + 1) ∧
              accC init (zAt recs) x.testBit (hb + j + 1) < 2 ^ W := (hR (hb + j + 1) (by omega)).1
          rw [accC_succ, if_pos hbt] at h2
          exact h2)
        (by
          intro hbt
          rw [Int.toNat_of_nonneg hRj.2.1]
          have hb' : c' (hb + j) = true := by
            show (x.testBit (hb + j) ^^ fl (hb + j)) = true
            rw [hfj, Bool.xor_false]; exact hbt
          have h2 : 0 ≤ accC init (zAt recs) c' (hb + j + 1) ∧ accC init (zAt recs) c' (hb + j + 1) < 2 ^ W :=
            (hR (hb + j + 1) (by omega)).2
          rw [accC_succ, if_pos hb'] at h2
          exact h2)
        (toNat_lt_pow _ W hRj.1.1 hRj.1.2) (toNat_lt_pow _ W hRj.2.1 hRj.2.2) hcapW
        (by rw [hlen]; nlinarith) (by omega)
      rw [hlen] at h
      refine WExec.cast cap h ?_ (by omega)
      simp only [M]
      have e1 : 2 * (hb + j) + 2 = 2 * (hb + (j + 1)) := by ring
      have e2 : (hb + j) * (2 * W + 2) + 2 * W + 2 = (hb + (j + 1)) * (2 * W + 2) := by ring
      have hcj : c' (hb + j) = x.testBit (hb + j) := by
        show (x.testBit (hb + j) ^^ fl (hb + j)) = x.testBit (hb + j)
        rw [hfj, Bool.xor_false]
      have e4 : (accC init (zAt recs) x.testBit (hb + (j + 1))).toNat =
          if x.testBit (hb + j) then (((accC init (zAt recs) x.testBit (hb + j)).toNat : ℤ) +
            sv (recAt recs (hb + j)).1 (recAt recs (hb + j)).2).toNat
          else (accC init (zAt recs) x.testBit (hb + j)).toNat := by
        rw [acc_step _ hRj.1.1, ← Nat.add_assoc, accC_succ]; rfl
      have e5 : (accC init (zAt recs) c' (hb + (j + 1))).toNat =
          if x.testBit (hb + j) then (((accC init (zAt recs) c' (hb + j)).toNat : ℤ) +
            sv (recAt recs (hb + j)).1 (recAt recs (hb + j)).2).toNat
          else (accC init (zAt recs) c' (hb + j)).toNat := by
        rw [acc_step _ hRj.2.1, ← Nat.add_assoc, accC_succ, hcj]; rfl
      have e6 : wvAt recs wv0 (hb + (j + 1)) = (recAt recs (hb + j)).2 := by
        unfold wvAt; rw [if_neg (by omega)]; congr 2
      rw [e1, e2, e4, e5, e6])
  simp only [M, Nat.add_zero] at hl
  exact WExec.cast cap hl rfl le_rfl

end Blocks

/-- **The point routine.** -/
def pointR (S : Fin 12 → Fin (ns + 1)) (Q : Fin 20 → Fin nr) : WM ns nr :=
  .seq (copyB (S 6) (S 9) (Q 0) (Q 1)) (.seq (copyB (S 7) (S 9) (Q 0) (Q 1)) (.seq (.inc (Q 2))
    (.seq (cloop (Q 13) (Q 14) (segN S Q)) (.seq (cloop (Q 10) (Q 14) (blk S Q)) (.seq (cloop (Q 12) (Q 14) (posF S Q))
    (.seq (.ifr (Q 2) (.dec (Q 2)) (.seq (copyB (S 6) (S 9) (Q 0) (Q 1)) (copyB (S 7) (S 9) (Q 0) (Q 1))))
    (rewP S Q)))))))

/-- The routine's cost bound. -/
def pointCost (hh b f o s W : ℕ) : ℕ := (hh * b + f + hh + o + 1) * (400 * W + 400 * s + 400)

section Routine
variable {S : Fin 12 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 20 → Fin nr} (hQ : Function.Injective Q)
variable (cap s W : ℕ) (σ0 : WState ns nr)
variable (h0C : σ0.sh (S 4) = 0) (h0Y : σ0.sh (S 5) = 0) (h0A : σ0.sh (S 6) = 0) (h0A' : σ0.sh (S 7) = 0)
  (h0V : σ0.sh (S 8) = 0) (h0F : σ0.val (Q 0) = 0) (h0R : σ0.val (Q 1) = 0)
include hS hQ h0C h0Y h0A h0A' h0V h0F h0R

/-- **The point routine**: from the zero words, `AC` and `AC'` end holding the half's two running sums over all
`h·b + f` positions (offset by `init`) if every block passes the coset test, else `init` (the null point); `OK` and
every head come back. -/
theorem pointR_spec (recs : List (Bool × ℕ)) (x wx u wu N wn hh b f o ini a0 a0' wv0 : ℕ) (fl : ℕ → Bool)
    (hX : σ0.st (S 0) = frame (binary wx x)) (hU : σ0.st (S 1) = frame (binary wu u))
    (hN : σ0.st (S 2) = frame (binary wn N)) (hT : σ0.st (S 3) = tbl W recs) (hI : NumOn σ0 (S 9) W ini)
    (hb : b < 2 ^ s) (hL : hh * b + f ≤ recs.length) (hLx : hh * b + f ≤ wx) (hLu : s * hh ≤ wu)
    (hLn : s * (o + hh) ≤ wn)
    (hfl : ∀ t < hh, ∀ j < b, decide (binary s (j + 1) = binary s (u / 2 ^ (s * t))) = fl (t * b + j))
    (hfl0 : ∀ p, hh * b ≤ p → fl p = false)
    (hR : ∀ P ≤ hh * b + f, (0 ≤ accC ini (zAt recs) x.testBit P ∧ accC ini (zAt recs) x.testBit P < 2 ^ W) ∧
      (0 ≤ accC ini (zAt recs) (fun p => xor (x.testBit p) (fl p)) P ∧
        accC ini (zAt recs) (fun p => xor (x.testBit p) (fl p)) P < 2 ^ W))
    (hK9 : σ0.val (Q 9) = b) (hK10 : σ0.val (Q 10) = hh) (hK11 : σ0.val (Q 11) = s) (hK12 : σ0.val (Q 12) = f)
    (hK13 : σ0.val (Q 13) = o) (hT14 : σ0.val (Q 14) = 0) (hT15 : σ0.val (Q 15) = 0)
    (hcap : 2 * s + 1 ≤ cap) (hcapW : 2 * W + 1 ≤ cap) (hcapT : (hh * b + f) * (2 * W + 2) ≤ cap)
    (hcapX : 2 * (hh * b + f) ≤ cap) (hcapb : b ≤ cap) (hcaph : hh ≤ cap) (hcapf : f ≤ cap) (hcapo : o ≤ cap)
    (hcapU : 2 * (s * hh) ≤ cap) (hcapN : 2 * (s * (o + hh)) ≤ cap) :
    WExec cap (pointR S Q) (mkP S Q s W σ0 0 0 0 0 0 0 a0 a0' 0 0 0 wv0)
      (mkP S Q s W σ0 0 0 0 0 0 0
        (if okB x.testBit b s o N hh then (accC ini (zAt recs) x.testBit (hh * b + f)).toNat else ini)
        (if okB x.testBit b s o N hh then
          (accC ini (zAt recs) (fun p => xor (x.testBit p) (fl p)) (hh * b + f)).toNat else ini)
        0 0 0 (wvAt recs wv0 (hh * b + f))) (pointCost hh b f o s W) := by
  set c' : ℕ → Bool := fun p => xor (x.testBit p) (fl p) with hc'
  have x1 := mkP_initA hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R ini hI 0 0 0 0 0 0 a0 a0' 0 0 0 wv0 hcapW
  have x2 := mkP_initA' hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R ini hI 0 0 0 0 0 0 ini a0' 0 0 0 wv0 hcapW
  have x3 := mkP_incOK hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R 0 0 0 0 0 0 ini ini 0 0 0 wv0 (by omega)
  -- the coset word's head to segment `o`
  let M : WState ns nr → ℕ → WState ns nr := fun σ j => mkP S Q s W σ 0 0 0 (2 * (s * j)) 0 0 ini ini 1 0 0 wv0
  have x4 := cloopM cap (Q 13) (Q 14) (hQ.ne (by decide)) (segN S Q) M
    (fun σ j v w => mkP_setv2 hS hQ s W σ 13 14 (by decide) (by decide) v w _ _ _ _ _ _ _ _ _ _ _ _) σ0 o
    (s * 19 + 3 + 7 * s) hK13 hT14 hcapo (by
      intro j hj v w
      have hQ11 : ((σ0.setv (Q 13) v).setv (Q 14) w).val (Q 11) = s := by
        simp [Function.update_apply, hQ.eq_iff, hK11]
      have hQ15 : ((σ0.setv (Q 13) v).setv (Q 14) w).val (Q 15) = 0 := by
        simp [Function.update_apply, hQ.eq_iff, hT15]
      have hsj : 2 * (s * j) + 2 * s ≤ cap := by
        have := Nat.mul_le_mul_left s (show j + 1 ≤ o + hh by omega); rw [Nat.mul_add, Nat.mul_one] at this; omega
      have h := segN_spec hS hQ cap s W ((σ0.setv (Q 13) v).setv (Q 14) w) 0 0 0 (2 * (s * j)) 0 0 ini ini 1 0 0 wv0
        hQ11 hQ15 hsj
      refine WExec.cast cap h ?_ le_rfl
      simp only [M]; congr 1; ring)
  simp only [M, Nat.mul_zero] at x4
  -- the blocks
  have x5 := blocks_spec hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R recs x wx u wu N wn hh b o wv0 (ini : ℤ) fl
    hX hU hN hT hb (by omega) (by omega) hLu hLn hfl (fun P hP => hR P (by omega)) hK9 hK10 hK11 hT14 hT15 hcap hcapW
    (le_trans (Nat.mul_le_mul_right _ (by omega)) hcapT) (by omega) hcapb hcaph hcapU hcapN
  simp only [accC_zero, Int.toNat_natCast] at x5
  -- the free positions
  have x6 := frees_spec hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R recs x wx (hh * b) f (2 * (s * hh))
    (2 * (s * (o + hh))) (okB x.testBit b s o N hh).toNat wv0 (ini : ℤ) fl hX hT hL hLx hfl0 hR hK12 hT14 hcapW hcapT
    hcapX hcapf
  -- the null point
  set aF := (accC ini (zAt recs) x.testBit (hh * b + f)).toNat with haF
  set aF' := (accC ini (zAt recs) c' (hh * b + f)).toNat with haF'
  set okF := okB x.testBit b s o N hh with hokF
  have x7 := mkP_null hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R ini hI (2 * (hh * b + f))
    ((hh * b + f) * (2 * W + 2)) (2 * (s * hh)) (2 * (s * (o + hh))) 0 0 aF aF' (wvAt recs wv0 (hh * b + f)) okF hcapW
  have x8 := mkP_rew hS hQ cap s W σ0 (2 * (hh * b + f)) ((hh * b + f) * (2 * W + 2)) (2 * (s * hh))
    (2 * (s * (o + hh))) 0 0 (if okF then aF else ini) (if okF then aF' else ini) 0 0 0 (wvAt recs wv0 (hh * b + f))
    (by omega) (by omega) (by omega) (by omega)
  have hall := WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5 (WExec.seq x6
    (WExec.seq x7 x8))))))
  unfold pointR
  refine WExec.cast cap hall rfl ?_
  unfold pointCost
  ring_nf
  omega

end Routine

end NearCubicWires.WireExponent3_5.SelectionMachine.Point
