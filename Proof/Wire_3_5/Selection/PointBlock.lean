import Proof.Wire_3_5.Selection.PointMath
import Proof.Wire_3_5.UnionMachine.FrontTWKit

/-! # C1.4: one block of the point routine (P3:1339-1344, 1195-1197)

Paper: "For each gate and row, the four threshold predicates have integer scores of the form `a_j(z_L) + b_j(z_R)`"
(P3:1341-1342). A block of the half is `b` machine positions; the routine walks them with C6's counted loop
(`FrontTWKit.cloop`), then checks the block's syndrome against the coset counter's segment and steps the errors word
and the coset word to their next segments. Main declarations: `cloopM` (a counted loop over a family of states that
commute with the loop's registers), **`blkPos_spec`** (the `b` positions of a block: the running sums and the running
syndrome), **`blkEnd_spec`**. Paper quantity: a half's integer score over one block, and the block's syndrome test. -/

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

/-! ## A counted loop over a family of states -/

/-- **The counted loop over a family** `M σ j` whose states commute with setting the loop's registers `K`, `T`. -/
theorem cloopM (cap : ℕ) (K T : Fin nr) (hKT : K ≠ T) (body : WM ns nr) (M : WState ns nr → ℕ → WState ns nr)
    (hM : ∀ σ j v w, ((M σ j).setv K v).setv T w = M ((σ.setv K v).setv T w) j) (σ0 : WState ns nr) (n c : ℕ)
    (hK : σ0.val K = n) (hT : σ0.val T = 0) (hcap : n ≤ cap)
    (hbody : ∀ j < n, ∀ v w, WExec cap body (M ((σ0.setv K v).setv T w) j) (M ((σ0.setv K v).setv T w) (j + 1)) c) :
    WExec cap (cloop K T body) (M σ0 0) (M σ0 n) (n * (c + 8) + 1 + 1 + (7 * n + 1)) := by
  have h := cloop_spec cap K T hKT body n c (fun j => M σ0 j) hcap (fun j hj => by
    rw [hM, hM]; exact hbody j hj _ _)
  have e : (σ0.setv K n).setv T 0 = σ0 := by
    rw [← hK, wsetv_same, ← hT, wsetv_same]
  simp only [hM, e] at h
  exact h

theorem toNat_lt_pow (v : ℤ) (W : ℕ) (h0 : 0 ≤ v) (h : v < 2 ^ W) : v.toNat < 2 ^ W := by
  have : (v.toNat : ℤ) < ((2 ^ W : ℕ) : ℤ) := by rw [Int.toNat_of_nonneg h0]; exact_mod_cast h
  exact_mod_cast this

/-! ## The routine's layout -/

section Layout
variable {S : Fin 12 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 20 → Fin nr} (hQ : Function.Injective Q)
include hS hQ

theorem mkP_setv2 (s W : ℕ) (σ0 : WState ns nr) (i k : Fin 20) (hi : 9 ≤ i.val) (hk : 9 ≤ k.val) (v w : ℕ)
    (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    ((mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv).setv (Q i) v).setv (Q k) w =
      mkP S Q s W ((σ0.setv (Q i) v).setv (Q k) w) pX pW pU pN ci sy a a' ok fl sg wv := by
  rw [mkP_setv hS hQ s W σ0 (Q i) v (fun j hj => hQ.ne (by intro h; rw [h] at hi; omega)),
    mkP_setv hS hQ s W (σ0.setv (Q i) v) (Q k) w (fun j hj => hQ.ne (by intro h; rw [h] at hk; omega))]

end Layout

/-! ## The positions of one block -/

section Block
variable {S : Fin 12 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 20 → Fin nr} (hQ : Function.Injective Q)
variable (cap s W : ℕ) (σ0 : WState ns nr)
variable (h0C : σ0.sh (S 4) = 0) (h0Y : σ0.sh (S 5) = 0) (h0A : σ0.sh (S 6) = 0) (h0A' : σ0.sh (S 7) = 0)
  (h0V : σ0.sh (S 8) = 0) (h0F : σ0.val (Q 0) = 0) (h0R : σ0.val (Q 1) = 0)
include hS hQ h0C h0Y h0A h0A' h0V h0F h0R

/-- **The positions of one block** (machine block `t`, positions `p0 = t·b` to `p0 + b`): `CI` counts to `b`, `SY`
is the running syndrome, `AC` and `AC'` the running sums of the bits `c` and `c'` (the bits xor the flips `fl`). -/
theorem blkPos_spec (recs : List (Bool × ℕ)) (x wx u wu t b pN ok wv0 : ℕ) (init : ℤ) (fl : ℕ → Bool)
    (hX : σ0.st (S 0) = frame (binary wx x)) (hU : σ0.st (S 1) = frame (binary wu u)) (hT : σ0.st (S 3) = tbl W recs)
    (hb : b < 2 ^ s) (hL : t * b + b ≤ recs.length) (hLx : t * b + b ≤ wx) (hLu : s * t + s ≤ wu)
    (hfl : ∀ j < b, decide (binary s (j + 1) = binary s (u / 2 ^ (s * t))) = fl (t * b + j))
    (hR : ∀ P ≤ t * b + b, (0 ≤ accC init (zAt recs) x.testBit P ∧ accC init (zAt recs) x.testBit P < 2 ^ W) ∧
      (0 ≤ accC init (zAt recs) (fun p => xor (x.testBit p) (fl p)) P ∧
        accC init (zAt recs) (fun p => xor (x.testBit p) (fl p)) P < 2 ^ W))
    (hK : σ0.val (Q 9) = b) (hT2 : σ0.val (Q 15) = 0)
    (hcap : 2 * s + 1 ≤ cap) (hcapW : 2 * W + 1 ≤ cap) (hcapT : (t * b + b) * (2 * W + 2) ≤ cap)
    (hcapX : 2 * (t * b + b) ≤ cap) (hcapb : b ≤ cap) :
    WExec cap (cloop (Q 9) (Q 15) (posB S Q))
      (mkP S Q s W σ0 (2 * (t * b)) (t * b * (2 * W + 2)) (2 * (s * t)) pN 0 0
        (accC init (zAt recs) x.testBit (t * b)).toNat
        (accC init (zAt recs) (fun p => xor (x.testBit p) (fl p)) (t * b)).toNat ok 0 0 wv0)
      (mkP S Q s W σ0 (2 * (t * b + b)) ((t * b + b) * (2 * W + 2)) (2 * (s * t)) pN b
        (synC x.testBit (t * b) b)
        (accC init (zAt recs) x.testBit (t * b + b)).toNat
        (accC init (zAt recs) (fun p => xor (x.testBit p) (fl p)) (t * b + b)).toNat ok 0 0
        (if b = 0 then wv0 else (recAt recs (t * b + b - 1)).2))
      (b * (180 * W + 125 * s + 118) + 3 + 7 * b) := by
  set p0 := t * b with hp0
  set c : ℕ → Bool := x.testBit with hc
  set c' : ℕ → Bool := fun p => xor (x.testBit p) (fl p) with hc'
  let M : WState ns nr → ℕ → WState ns nr := fun σ j =>
    mkP S Q s W σ (2 * (p0 + j)) ((p0 + j) * (2 * W + 2)) (2 * (s * t)) pN j (synC c p0 j)
      (accC init (zAt recs) c (p0 + j)).toNat (accC init (zAt recs) c' (p0 + j)).toNat ok 0 0
      (if j = 0 then wv0 else (recAt recs (p0 + j - 1)).2)
  have hM : ∀ σ j v w, ((M σ j).setv (Q 9) v).setv (Q 15) w = M ((σ.setv (Q 9) v).setv (Q 15) w) j := by
    intro σ j v w
    exact mkP_setv2 hS hQ s W σ 9 15 (by decide) (by decide) v w _ _ _ _ _ _ _ _ _ _ _ _
  have hl := cloopM cap (Q 9) (Q 15) (hQ.ne (by decide)) (posB S Q) M hM σ0 b (180 * W + 125 * s + 110) hK hT2 hcapb
    (by
      intro j hj v w
      set σv := (σ0.setv (Q 9) v).setv (Q 15) w with hσv
      have hQ0 : σv.val (Q 0) = 0 := by simp [hσv, Function.update_apply, hQ.eq_iff, h0F]
      have hQ1 : σv.val (Q 1) = 0 := by simp [hσv, Function.update_apply, hQ.eq_iff, h0R]
      have hp : p0 + j < recs.length := by omega
      have hsplit := tbl_split W recs (p0 + j) hp
      have hlen : (tbl W (recs.take (p0 + j))).length = (p0 + j) * (2 * W + 2) := by
        rw [tbl_length, List.length_take, Nat.min_eq_left (by omega)]
      have hseg := frame_seg wu (s * t) s u hLu
      have hbit : readTapeBit (σv.st (S 0)) (2 * (p0 + j) + 1) = c (p0 + j) := by
        simp only [hσv, WState.setv_st, hX]
        exact rd_frame_bit wx x (p0 + j) (by omega)
      have hRj := hR (p0 + j) (by omega)
      have hfj := hfl j hj
      have h := posB_spec hS hQ cap s W σv h0C h0Y h0A h0A' h0V hQ0 hQ1 (2 * (p0 + j)) pN j (synC c p0 j)
        (accC init (zAt recs) c (p0 + j)).toNat (accC init (zAt recs) c' (p0 + j)).toNat ok
        (if j = 0 then wv0 else (recAt recs (p0 + j - 1)).2)
        (frameP (binary (s * t) u)) (binary s (u / 2 ^ (s * t)))
        (frameP (binary (wu - s * t - s) (u / 2 ^ (s * t) / 2 ^ s)) ++ [false])
        (tbl W (recs.take (p0 + j))) (tbl W (recs.drop (p0 + j + 1)))
        (recAt recs (p0 + j)).1 (recAt recs (p0 + j)).2 (c (p0 + j)) (by simp)
        (by simp only [hσv, WState.setv_st, hU, hseg, List.append_assoc])
        (by simp only [hσv, WState.setv_st, hT, hsplit, List.append_assoc])
        hbit (by omega)
        (by
          intro hbt
          rw [Int.toNat_of_nonneg hRj.1.1]
          have h2 : 0 ≤ accC init (zAt recs) c (p0 + j + 1) ∧ accC init (zAt recs) c (p0 + j + 1) < 2 ^ W :=
            (hR (p0 + j + 1) (by omega)).1
          rw [accC_succ, if_pos hbt] at h2
          exact h2)
        (by
          intro hbt
          rw [Int.toNat_of_nonneg hRj.2.1]
          have hb' : c' (p0 + j) = true := by
            show (x.testBit (p0 + j) ^^ fl (p0 + j)) = true
            rw [hfj] at hbt; exact hbt
          have h2 : 0 ≤ accC init (zAt recs) c' (p0 + j + 1) ∧ accC init (zAt recs) c' (p0 + j + 1) < 2 ^ W :=
            (hR (p0 + j + 1) (by omega)).2
          rw [accC_succ, if_pos hb'] at h2
          exact h2)
        (toNat_lt_pow _ W hRj.1.1 hRj.1.2) (toNat_lt_pow _ W hRj.2.1 hRj.2.2) hcap hcapW
        (by rw [hlen]; nlinarith) (by omega)
      rw [hlen, hfj] at h
      simp only [frameP_length, binary_length] at h
      refine WExec.cast cap h ?_ (by omega)
      simp only [M]
      have e1 : 2 * (p0 + j) + 2 = 2 * (p0 + (j + 1)) := by ring
      have e2 : (p0 + j) * (2 * W + 2) + 2 * W + 2 = (p0 + (j + 1)) * (2 * W + 2) := by ring
      have e3 : synC c p0 (j + 1) = if c (p0 + j) then synC c p0 j ^^^ (j + 1) else synC c p0 j := synC_succ c p0 j
      have e4 : (accC init (zAt recs) c (p0 + (j + 1))).toNat =
          if c (p0 + j) then (((accC init (zAt recs) c (p0 + j)).toNat : ℤ) + sv (recAt recs (p0 + j)).1
            (recAt recs (p0 + j)).2).toNat else (accC init (zAt recs) c (p0 + j)).toNat := by
        rw [acc_step _ hRj.1.1, ← Nat.add_assoc, accC_succ]; rfl
      have e5 : (accC init (zAt recs) c' (p0 + (j + 1))).toNat =
          if xor (c (p0 + j)) (fl (p0 + j)) then (((accC init (zAt recs) c' (p0 + j)).toNat : ℤ) +
            sv (recAt recs (p0 + j)).1 (recAt recs (p0 + j)).2).toNat
          else (accC init (zAt recs) c' (p0 + j)).toNat := by
        rw [acc_step _ hRj.2.1, ← Nat.add_assoc, accC_succ]; rfl
      have e6 : (if j + 1 = 0 then wv0 else (recAt recs (p0 + (j + 1) - 1)).2) = (recAt recs (p0 + j)).2 := by
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
        congr 2
      rw [e1, e2, e3, e4, e5, e6])
  simp only [M, Nat.add_zero] at hl
  refine WExec.cast cap hl ?_ (le_of_eq (by ring))
  rfl

end Block

/-! ## Segment steps and the block's end -/

/-- Step a word's head by one `s`-bit segment (`2s` cells), counted. -/
def segU (S : Fin 12 → Fin (ns + 1)) (Q : Fin 20 → Fin nr) : WM ns nr :=
  cloop (Q 11) (Q 15) (.seq (WM.fwdC (S 1) (Q 7)) (WM.fwdC (S 1) (Q 7)))

def segN (S : Fin 12 → Fin (ns + 1)) (Q : Fin 20 → Fin nr) : WM ns nr :=
  cloop (Q 11) (Q 15) (.seq (WM.fwdC (S 2) (Q 8)) (WM.fwdC (S 2) (Q 8)))

/-- **The end of a block**: `OK &&= [SY = the coset segment at NS]`; `SY, CI := 0`; `U`, `NS` step one segment. -/
def blkEnd (S : Fin 12 → Fin (ns + 1)) (Q : Fin 20 → Fin nr) : WM ns nr :=
  .seq (eqAtF (S 5) (S 2) (Q 0) (Q 1) (Q 3)) (.seq (.ifr (Q 3) (.dec (Q 3)) (clrF (Q 2)))
    (.seq (zeroB (S 5) (S 4) (Q 0) (Q 1)) (.seq (zeroB (S 4) (S 5) (Q 0) (Q 1)) (.seq (segU S Q) (segN S Q)))))

/-- **One block**: its positions, then its end. -/
def blk (S : Fin 12 → Fin (ns + 1)) (Q : Fin 20 → Fin nr) : WM ns nr := .seq (cloop (Q 9) (Q 15) (posB S Q)) (blkEnd S Q)

section End
variable {S : Fin 12 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 20 → Fin nr} (hQ : Function.Injective Q)
variable (cap s W : ℕ) (σ0 : WState ns nr)
include hS hQ

theorem segU_spec (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) (hK : σ0.val (Q 11) = s) (hT : σ0.val (Q 15) = 0)
    (hcap : pU + 2 * s ≤ cap) :
    WExec cap (segU S Q) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W σ0 pX pW (pU + 2 * s) pN ci sy a a' ok fl sg wv) (s * 19 + 3 + 7 * s) := by
  let M : WState ns nr → ℕ → WState ns nr := fun σ j => mkP S Q s W σ pX pW (pU + 2 * j) pN ci sy a a' ok fl sg wv
  have hl := cloopM cap (Q 11) (Q 15) (hQ.ne (by decide)) _ M
    (fun σ j v w => mkP_setv2 hS hQ s W σ 11 15 (by decide) (by decide) v w _ _ _ _ _ _ _ _ _ _ _ _) σ0 s 11 hK hT
    (by omega) (by
      intro j hj v w
      have h1 := mkP_fwdU hS hQ cap s W ((σ0.setv (Q 11) v).setv (Q 15) w) pX pW (pU + 2 * j) pN ci sy a a' ok fl sg wv
        (by omega)
      have h2 := mkP_fwdU hS hQ cap s W ((σ0.setv (Q 11) v).setv (Q 15) w) pX pW (pU + 2 * j + 1) pN ci sy a a' ok fl
        sg wv (by omega)
      refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
      simp only [M]; congr 1)
  simp only [M, Nat.mul_zero, Nat.add_zero] at hl
  exact WExec.cast cap hl rfl (le_of_eq (by ring))

theorem segN_spec (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) (hK : σ0.val (Q 11) = s) (hT : σ0.val (Q 15) = 0)
    (hcap : pN + 2 * s ≤ cap) :
    WExec cap (segN S Q) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W σ0 pX pW pU (pN + 2 * s) ci sy a a' ok fl sg wv) (s * 19 + 3 + 7 * s) := by
  let M : WState ns nr → ℕ → WState ns nr := fun σ j => mkP S Q s W σ pX pW pU (pN + 2 * j) ci sy a a' ok fl sg wv
  have hl := cloopM cap (Q 11) (Q 15) (hQ.ne (by decide)) _ M
    (fun σ j v w => mkP_setv2 hS hQ s W σ 11 15 (by decide) (by decide) v w _ _ _ _ _ _ _ _ _ _ _ _) σ0 s 11 hK hT
    (by omega) (by
      intro j hj v w
      have h1 := mkP_fwdN hS hQ cap s W ((σ0.setv (Q 11) v).setv (Q 15) w) pX pW pU (pN + 2 * j) ci sy a a' ok fl sg wv
        (by omega)
      have h2 := mkP_fwdN hS hQ cap s W ((σ0.setv (Q 11) v).setv (Q 15) w) pX pW pU (pN + 2 * j + 1) ci sy a a' ok fl
        sg wv (by omega)
      refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
      simp only [M]; congr 1)
  simp only [M, Nat.mul_zero, Nat.add_zero] at hl
  exact WExec.cast cap hl rfl (le_of_eq (by ring))

variable (h0C : σ0.sh (S 4) = 0) (h0Y : σ0.sh (S 5) = 0) (h0A : σ0.sh (S 6) = 0) (h0A' : σ0.sh (S 7) = 0)
  (h0V : σ0.sh (S 8) = 0) (h0F : σ0.val (Q 0) = 0) (h0R : σ0.val (Q 1) = 0)
include h0C h0Y h0A h0A' h0V h0F h0R

/-- **The end of block `t`**: the syndrome test against the coset word's segment `o + t`. -/
theorem blkEnd_spec (N wn o t pX pW ci sy a a' ok wv : ℕ) (hN : σ0.st (S 2) = frame (binary wn N))
    (hNw : s * (o + t) + s ≤ wn) (hsy : sy < 2 ^ s) (hok : ok ≤ 1)
    (hK : σ0.val (Q 11) = s) (hT : σ0.val (Q 15) = 0) (hcap : 2 * s + 1 ≤ cap)
    (hcapU : 2 * (s * t) + 2 * s ≤ cap) (hcapN : 2 * (s * (o + t)) + 2 * s ≤ cap) :
    WExec cap (blkEnd S Q) (mkP S Q s W σ0 pX pW (2 * (s * t)) (2 * (s * (o + t))) ci sy a a' ok 0 0 wv)
      (mkP S Q s W σ0 pX pW (2 * (s * (t + 1))) (2 * (s * (o + (t + 1)))) 0 0 a a'
        (if sy = N / 2 ^ (s * (o + t)) % 2 ^ s then ok else 0) 0 0 wv) (180 * s + 40) := by
  have hseg := frame_seg wn (s * (o + t)) s N hNw
  have x1 := mkP_eqSyn hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW (2 * (s * t)) ci sy a a' ok 0 wv
    (frameP (binary (s * (o + t)) N)) (binary s (N / 2 ^ (s * (o + t))))
    (frameP (binary (wn - s * (o + t) - s) (N / 2 ^ (s * (o + t)) / 2 ^ s)) ++ [false]) (by simp)
    (by rw [hN, hseg]) hcap
  simp only [frameP_length, binary_length] at x1
  have x2 := mkP_okAnd hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW (2 * (s * t)) (2 * (s * (o + t))) ci sy a a' ok
    0 wv (decide (binary s sy = binary s (N / 2 ^ (s * (o + t))))) hok (by omega)
  have ee : (if decide (binary s sy = binary s (N / 2 ^ (s * (o + t)))) = true then ok else 0) =
      (if sy = N / 2 ^ (s * (o + t)) % 2 ^ s then ok else 0) := by
    simp only [decide_eq_true_eq, binary_seg_eq s sy _ hsy]
  rw [ee] at x2
  have x3 := mkP_zeroY hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW (2 * (s * t)) (2 * (s * (o + t))) ci sy a a'
    (if sy = N / 2 ^ (s * (o + t)) % 2 ^ s then ok else 0) 0 0 wv hcap
  have x4 := mkP_zeroC hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW (2 * (s * t)) (2 * (s * (o + t))) ci 0 a a'
    (if sy = N / 2 ^ (s * (o + t)) % 2 ^ s then ok else 0) 0 0 wv hcap
  have x5 := segU_spec hS hQ cap s W σ0 pX pW (2 * (s * t)) (2 * (s * (o + t))) 0 0 a a'
    (if sy = N / 2 ^ (s * (o + t)) % 2 ^ s then ok else 0) 0 0 wv hK hT hcapU
  have x6 := segN_spec hS hQ cap s W σ0 pX pW (2 * (s * t) + 2 * s) (2 * (s * (o + t))) 0 0 a a'
    (if sy = N / 2 ^ (s * (o + t)) % 2 ^ s then ok else 0) 0 0 wv hK hT hcapN
  have e1 : 2 * (s * t) + 2 * s = 2 * (s * (t + 1)) := by ring
  have e2 : 2 * (s * (o + t)) + 2 * s = 2 * (s * (o + (t + 1))) := by ring
  rw [e1] at x5 x6
  rw [e2] at x6
  unfold blkEnd
  exact WExec.mono (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5 x6))))) (by omega)

end End

end NearCubicWires.WireExponent3_5.SelectionMachine.Point
