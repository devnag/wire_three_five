import Proof.Wire_3_5.Selection.PointRoutine
import Proof.Wire_3_5.Selection.EmitKeys

/-! # C1.4: one point's keys (P3:1339-1346)

Paper: "Enumerate each half's score vectors. For each of the sixteen corner patterns, count pairs" (P3:1344-1346).
One point of a half: the point routine leaves its two key words in `AC`, `AC'`; the body orders them
(`F := [AC' < AC]`, C6's `ltB`), hands `(min, max)` to the join's emitter `EM lo hi`, and zeroes the words `AC`, `AC'`,
`WV` for the next point. The emitter writes to the key stream `K`, whose state rides in the routine's base (`kst`).
Main declarations: `ptBody`, **`ptBody_spec`** (the key stream gains `f (min a a') (max a a')` for the point's words
`a`, `a'`). Paper quantity: one point's contribution to a join's key stream. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit (cloop cloop_spec)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

variable {ns nr : ℕ}

/-- **One point's body**: the routine, the order of its words, the emitter, the words back to `0`. -/
def ptBody (S : Fin 12 → Fin (ns + 1)) (Q : Fin 20 → Fin nr)
    (EM : Fin (ns + 1) → Fin (ns + 1) → Fin nr → Fin nr → WM ns nr) (CA CA' : Fin nr) : WM ns nr :=
  .seq (pointR S Q) (.seq (ltB (S 7) (S 6) (Q 0) (Q 1))
    (.seq (.ifr (Q 0) (.seq (.dec (Q 0)) (EM (S 7) (S 6) CA' CA)) (EM (S 6) (S 7) CA CA'))
    (.seq (zeroB (S 6) (S 7) (Q 0) (Q 1)) (.seq (zeroB (S 7) (S 6) (Q 0) (Q 1)) (zeroB (S 8) (S 6) (Q 0) (Q 1))))))

section Frame
variable {S : Fin 12 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 20 → Fin nr} (hQ : Function.Injective Q)
include hS hQ

theorem mkP_kst (s W : ℕ) (σb : WState ns nr) (K : Fin (ns + 1)) (CK : Fin nr) (L out : List Bool)
    (hK : ∀ k : Fin 12, k.val < 9 → K ≠ S k) (hCK : ∀ i : Fin 20, 2 ≤ i.val → i.val < 9 → CK ≠ Q i)
    (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    mkP S Q s W (kst σb K CK L out) pX pW pU pN ci sy a a' ok fl sg wv =
      kst (mkP S Q s W σb pX pW pU pN ci sy a a' ok fl sg wv) K CK L out := by
  have k0 := hK 0 (by decide); have k1 := hK 1 (by decide); have k2 := hK 2 (by decide); have k3 := hK 3 (by decide)
  have k4 := hK 4 (by decide); have k5 := hK 5 (by decide); have k6 := hK 6 (by decide); have k7 := hK 7 (by decide)
  have k8 := hK 8 (by decide)
  have q2 := hCK 2 (by decide) (by decide); have q3 := hCK 3 (by decide) (by decide)
  have q4 := hCK 4 (by decide) (by decide); have q5 := hCK 5 (by decide) (by decide)
  have q6 := hCK 6 (by decide) (by decide); have q7 := hCK 7 (by decide) (by decide)
  have q8 := hCK 8 (by decide) (by decide)
  apply WState.eq
  · funext j; simp only [mkP, kst, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    by_cases hj : j = K
    · subst hj; simp [k0, k1, k2, k3]
    · simp only [hj, if_false]
  · funext j; simp only [mkP, kst, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
    by_cases hj : j = K
    · subst hj; simp [k4, k5, k6, k7, k8]
    · simp only [hj, if_false]
  · funext j; simp only [mkP, kst, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    by_cases hj : j = CK
    · subst hj; simp [q2, q3, q4, q5, q6, q7, q8]
    · simp only [hj, if_false]
  · rfl

theorem mkP_setvF (s W : ℕ) (σ0 : WState ns nr) (v : ℕ) (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv).setv (Q 0) v =
      mkP S Q s W (σ0.setv (Q 0) v) pX pW pU pN ci sy a a' ok fl sg wv := by
  apply WState.eq
  · rfl
  · rfl
  · funext j; simp only [mkP, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hQ.eq_iff]
  · rfl

end Frame

section Zero
variable {S : Fin 12 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 20 → Fin nr} (hQ : Function.Injective Q)
variable (cap s W : ℕ) (σ0 : WState ns nr)
variable (h0C : σ0.sh (S 4) = 0) (h0Y : σ0.sh (S 5) = 0) (h0A : σ0.sh (S 6) = 0) (h0A' : σ0.sh (S 7) = 0)
  (h0V : σ0.sh (S 8) = 0) (h0F : σ0.val (Q 0) = 0) (h0R : σ0.val (Q 1) = 0)
include hS hQ h0C h0Y h0A h0A' h0V h0F h0R

/-- **The words back to `0`.** -/
theorem mkP_zero3 (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (.seq (zeroB (S 6) (S 7) (Q 0) (Q 1)) (.seq (zeroB (S 7) (S 6) (Q 0) (Q 1)) (zeroB (S 8) (S 6) (Q 0) (Q 1))))
      (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv) (mkP S Q s W σ0 pX pW pU pN ci sy 0 0 ok fl sg 0)
      (123 * W + 11) := by
  have z1 := zeroB_spec cap W (A := S 6) (B := S 7) (F := Q 0) (R := Q 1) (hS.ne (by decide)) (hQ.ne (by decide)) _ a a'
    (mkP_numA hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_numA' hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _) hcap
  have e1 : (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv).sets (S 6) (frame (binary W 0)) =
      mkP S Q s W σ0 pX pW pU pN ci sy 0 a' ok fl sg wv := by
    apply WState.eq
    · rfl
    · funext j; simp only [mkP, WState.sets_st, Function.update_apply]
      split_ifs <;> simp_all [hS.eq_iff]
    · rfl
    · rfl
  rw [e1] at z1
  have z2 := zeroB_spec cap W (A := S 7) (B := S 6) (F := Q 0) (R := Q 1) (hS.ne (by decide)) (hQ.ne (by decide)) _ a' 0
    (mkP_numA' hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy 0 a' ok fl sg wv)
    (mkP_numA hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy 0 a' ok fl sg wv)
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _) hcap
  have e2 : (mkP S Q s W σ0 pX pW pU pN ci sy 0 a' ok fl sg wv).sets (S 7) (frame (binary W 0)) =
      mkP S Q s W σ0 pX pW pU pN ci sy 0 0 ok fl sg wv := by
    apply WState.eq
    · rfl
    · funext j; simp only [mkP, WState.sets_st, Function.update_apply]
      split_ifs <;> simp_all [hS.eq_iff]
    · rfl
    · rfl
  rw [e2] at z2
  have z3 := zeroB_spec cap W (A := S 8) (B := S 6) (F := Q 0) (R := Q 1) (hS.ne (by decide)) (hQ.ne (by decide)) _ wv 0
    (mkP_numV hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy 0 0 ok fl sg wv)
    (mkP_numA hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy 0 0 ok fl sg wv)
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _) hcap
  have e3 : (mkP S Q s W σ0 pX pW pU pN ci sy 0 0 ok fl sg wv).sets (S 8) (frame (binary W 0)) =
      mkP S Q s W σ0 pX pW pU pN ci sy 0 0 ok fl sg 0 := by
    apply WState.eq
    · rfl
    · funext j; simp only [mkP, WState.sets_st, Function.update_apply]
      split_ifs <;> simp_all [hS.eq_iff]
    · rfl
    · rfl
  rw [e3] at z3
  exact WExec.mono (WExec.seq z1 (WExec.seq z2 z3)) (by omega)

/-- **The order of the two words**: `F := [a' < a]`. -/
theorem mkP_ltF (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) (ha : a < 2 ^ W) (ha' : a' < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (ltB (S 7) (S 6) (Q 0) (Q 1)) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W (σ0.setv (Q 0) (decide (a' < a)).toNat) pX pW pU pN ci sy a a' ok fl sg wv) (41 * W + 3) := by
  have h := ltB_spec cap W (A := S 7) (B := S 6) (F := Q 0) (R := Q 1) (hS.ne (by decide)) (hQ.ne (by decide)) _ a' a
    (mkP_numA' hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_numA hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _) ha' ha hcap
  rw [mkP_setvF hS hQ] at h
  exact h

end Zero

section Body
variable {S : Fin 12 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 20 → Fin nr} (hQ : Function.Injective Q)
variable (cap s W : ℕ) (σb : WState ns nr) {K : Fin (ns + 1)} {CK : Fin nr} (L : List Bool)
variable (hK : ∀ k : Fin 12, k.val < 10 → K ≠ S k) (hCK : ∀ i : Fin 20, i.val < 16 → CK ≠ Q i)
variable (h0C : σb.sh (S 4) = 0) (h0Y : σb.sh (S 5) = 0) (h0A : σb.sh (S 6) = 0) (h0A' : σb.sh (S 7) = 0)
  (h0V : σb.sh (S 8) = 0) (h0F : σb.val (Q 0) = 0) (h0R : σb.val (Q 1) = 0)
include hS hQ hK hCK h0C h0Y h0A h0A' h0V h0F h0R

/-- **One point's keys**: the key stream gains `f (min a a') (max a a')` for the point's two words (the routine's
result: the running sums over the half, or `init` for a point outside the coset), every word back at `0`. -/
theorem ptBody_spec (EM : Fin (ns + 1) → Fin (ns + 1) → Fin nr → Fin nr → WM ns nr) (CA CA' : Fin nr)
    (f : ℕ → ℕ → List Bool) (cE : ℕ) (out : List Bool)
    (recs : List (Bool × ℕ)) (x wx u wu N wn hh b fr o ini : ℕ) (fl : ℕ → Bool)
    (hX : σb.st (S 0) = frame (binary wx x)) (hU : σb.st (S 1) = frame (binary wu u))
    (hN : σb.st (S 2) = frame (binary wn N)) (hT : σb.st (S 3) = tbl W recs) (hI : NumOn σb (S 9) W ini)
    (hb : b < 2 ^ s) (hL : hh * b + fr ≤ recs.length) (hLx : hh * b + fr ≤ wx) (hLu : s * hh ≤ wu)
    (hLn : s * (o + hh) ≤ wn)
    (hfl : ∀ t < hh, ∀ j < b, decide (binary s (j + 1) = binary s (u / 2 ^ (s * t))) = fl (t * b + j))
    (hfl0 : ∀ p, hh * b ≤ p → fl p = false)
    (hR : ∀ P ≤ hh * b + fr, (0 ≤ accC ini (zAt recs) x.testBit P ∧ accC ini (zAt recs) x.testBit P < 2 ^ W) ∧
      (0 ≤ accC ini (zAt recs) (fun p => xor (x.testBit p) (fl p)) P ∧
        accC ini (zAt recs) (fun p => xor (x.testBit p) (fl p)) P < 2 ^ W))
    (hini : ini < 2 ^ W)
    (hK9 : σb.val (Q 9) = b) (hK10 : σb.val (Q 10) = hh) (hK11 : σb.val (Q 11) = s) (hK12 : σb.val (Q 12) = fr)
    (hK13 : σb.val (Q 13) = o) (hT14 : σb.val (Q 14) = 0) (hT15 : σb.val (Q 15) = 0)
    (hcap : 2 * s + 1 ≤ cap) (hcapW : 2 * W + 1 ≤ cap) (hcapT : (hh * b + fr) * (2 * W + 2) ≤ cap)
    (hcapX : 2 * (hh * b + fr) ≤ cap) (hcapb : b ≤ cap) (hcaph : hh ≤ cap) (hcapf : fr ≤ cap) (hcapo : o ≤ cap)
    (hcapU : 2 * (s * hh) ≤ cap) (hcapN : 2 * (s * (o + hh)) ≤ cap)
    (hEmA : let aF := (if okB x.testBit b s o N hh then (accC ini (zAt recs) x.testBit (hh * b + fr)).toNat else ini)
      let aF' := (if okB x.testBit b s o N hh then
          (accC ini (zAt recs) (fun p => xor (x.testBit p) (fl p)) (hh * b + fr)).toNat else ini)
      aF' < aF → WExec cap (EM (S 7) (S 6) CA' CA)
        (kst (mkP S Q s W σb 0 0 0 0 0 0 aF aF' 0 0 0 (wvAt recs 0 (hh * b + fr))) K CK L out)
        (kst (mkP S Q s W σb 0 0 0 0 0 0 aF aF' 0 0 0 (wvAt recs 0 (hh * b + fr))) K CK L (out ++ f aF' aF)) cE)
    (hEmB : let aF := (if okB x.testBit b s o N hh then (accC ini (zAt recs) x.testBit (hh * b + fr)).toNat else ini)
      let aF' := (if okB x.testBit b s o N hh then
          (accC ini (zAt recs) (fun p => xor (x.testBit p) (fl p)) (hh * b + fr)).toNat else ini)
      aF ≤ aF' → WExec cap (EM (S 6) (S 7) CA CA')
        (kst (mkP S Q s W σb 0 0 0 0 0 0 aF aF' 0 0 0 (wvAt recs 0 (hh * b + fr))) K CK L out)
        (kst (mkP S Q s W σb 0 0 0 0 0 0 aF aF' 0 0 0 (wvAt recs 0 (hh * b + fr))) K CK L (out ++ f aF aF')) cE) :
    let aF := (if okB x.testBit b s o N hh then (accC ini (zAt recs) x.testBit (hh * b + fr)).toNat else ini)
    let aF' := (if okB x.testBit b s o N hh then
        (accC ini (zAt recs) (fun p => xor (x.testBit p) (fl p)) (hh * b + fr)).toNat else ini)
    WExec cap (ptBody S Q EM CA CA') (mkP S Q s W (kst σb K CK L out) 0 0 0 0 0 0 0 0 0 0 0 0)
      (mkP S Q s W (kst σb K CK L (out ++ f (min aF aF') (max aF aF'))) 0 0 0 0 0 0 0 0 0 0 0 0)
      (pointCost hh b fr o s W + cE + 200 * W + 30) := by
  intro aF aF'
  have hK' : ∀ k : Fin 12, k.val < 9 → K ≠ S k := fun k hk => hK k (by omega)
  have hCK' : ∀ i : Fin 20, 2 ≤ i.val → i.val < 9 → CK ≠ Q i := fun i _ hi => hCK i (by omega)
  have hq : ∀ i : Fin 20, i.val < 16 → (kst σb K CK L out).val (Q i) = σb.val (Q i) := fun i hi =>
    kst_val σb K CK (Q i) L out (Ne.symm (hCK i hi))
  have hs : ∀ k : Fin 12, k.val < 10 → (kst σb K CK L out).st (S k) = σb.st (S k) := fun k hk =>
    kst_st σb K (S k) CK L out (Ne.symm (hK k hk))
  have hh' : ∀ k : Fin 12, k.val < 10 → (kst σb K CK L out).sh (S k) = σb.sh (S k) := fun k hk =>
    kst_sh σb K (S k) CK L out (Ne.symm (hK k hk))
  have hs9 := hs 9 (by decide)
  have hh9 := hh' 9 (by decide)
  -- the routine
  have x1 := pointR_spec hS hQ cap s W (kst σb K CK L out)
    (by rw [hh' 4 (by decide)]; exact h0C) (by rw [hh' 5 (by decide)]; exact h0Y) (by rw [hh' 6 (by decide)]; exact h0A)
    (by rw [hh' 7 (by decide)]; exact h0A') (by rw [hh' 8 (by decide)]; exact h0V)
    (by rw [hq 0 (by decide)]; exact h0F) (by rw [hq 1 (by decide)]; exact h0R)
    recs x wx u wu N wn hh b fr o ini 0 0 0 fl
    (by rw [hs 0 (by decide)]; exact hX) (by rw [hs 1 (by decide)]; exact hU) (by rw [hs 2 (by decide)]; exact hN)
    (by rw [hs 3 (by decide)]; exact hT) ⟨by rw [hs9]; exact hI.1, by rw [hh9]; exact hI.2⟩ hb hL hLx hLu hLn hfl
    hfl0 hR (by rw [hq 9 (by decide)]; exact hK9) (by rw [hq 10 (by decide)]; exact hK10)
    (by rw [hq 11 (by decide)]; exact hK11) (by rw [hq 12 (by decide)]; exact hK12)
    (by rw [hq 13 (by decide)]; exact hK13) (by rw [hq 14 (by decide)]; exact hT14)
    (by rw [hq 15 (by decide)]; exact hT15) hcap hcapW hcapT hcapX hcapb hcaph hcapf hcapo hcapU hcapN
  have haF : aF < 2 ^ W := by
    show (if okB x.testBit b s o N hh then _ else ini) < 2 ^ W
    split_ifs
    · exact toNat_lt_pow _ W (hR _ le_rfl).1.1 (hR _ le_rfl).1.2
    · exact hini
  have haF' : aF' < 2 ^ W := by
    show (if okB x.testBit b s o N hh then _ else ini) < 2 ^ W
    split_ifs
    · exact toNat_lt_pow _ W (hR _ le_rfl).2.1 (hR _ le_rfl).2.2
    · exact hini
  -- the order
  have x2 := mkP_ltF hS hQ cap s W (kst σb K CK L out)
    (by rw [hh' 4 (by decide)]; exact h0C) (by rw [hh' 5 (by decide)]; exact h0Y) (by rw [hh' 6 (by decide)]; exact h0A)
    (by rw [hh' 7 (by decide)]; exact h0A') (by rw [hh' 8 (by decide)]; exact h0V)
    (by rw [hq 0 (by decide)]; exact h0F) (by rw [hq 1 (by decide)]; exact h0R)
    0 0 0 0 0 0 aF aF' 0 0 0 (wvAt recs 0 (hh * b + fr)) haF haF' hcapW
  -- the emitter, then the words back to `0`
  have hzero := fun (o' : List Bool) => mkP_zero3 hS hQ cap s W (kst σb K CK L o')
    (by rw [kst_sh σb K _ CK L o' (Ne.symm (hK 4 (by decide)))]; exact h0C)
    (by rw [kst_sh σb K _ CK L o' (Ne.symm (hK 5 (by decide)))]; exact h0Y)
    (by rw [kst_sh σb K _ CK L o' (Ne.symm (hK 6 (by decide)))]; exact h0A)
    (by rw [kst_sh σb K _ CK L o' (Ne.symm (hK 7 (by decide)))]; exact h0A')
    (by rw [kst_sh σb K _ CK L o' (Ne.symm (hK 8 (by decide)))]; exact h0V)
    (by rw [kst_val σb K CK _ L o' (Ne.symm (hCK 0 (by decide)))]; exact h0F)
    (by rw [kst_val σb K CK _ L o' (Ne.symm (hCK 1 (by decide)))]; exact h0R)
    0 0 0 0 0 0 aF aF' 0 0 0 (wvAt recs 0 (hh * b + fr)) hcapW
  have hF0 : (kst σb K CK L out).val (Q 0) = 0 := by rw [hq 0 (by decide)]; exact h0F
  by_cases hlt : aF' < aF
  · have em := hEmA hlt
    rw [← mkP_kst hS hQ s W σb K CK L out hK' hCK', ← mkP_kst hS hQ s W σb K CK L (out ++ f aF' aF) hK' hCK'] at em
    have hd : WExec cap (.seq (.dec (Q 0)) (EM (S 7) (S 6) CA' CA))
        (mkP S Q s W ((kst σb K CK L out).setv (Q 0) (decide (aF' < aF)).toNat) 0 0 0 0 0 0 aF aF' 0 0 0
          (wvAt recs 0 (hh * b + fr)))
        (mkP S Q s W (kst σb K CK L (out ++ f aF' aF)) 0 0 0 0 0 0 aF aF' 0 0 0 (wvAt recs 0 (hh * b + fr)))
        (1 + 1 + cE) := by
      have y := WExec.dec (cap := cap) (Q 0) (mkP S Q s W ((kst σb K CK L out).setv (Q 0) (decide (aF' < aF)).toNat)
        0 0 0 0 0 0 aF aF' 0 0 0 (wvAt recs 0 (hh * b + fr))) (by simp [mkP, hQ.eq_iff, hlt]; omega)
      have ey : (mkP S Q s W ((kst σb K CK L out).setv (Q 0) (decide (aF' < aF)).toNat) 0 0 0 0 0 0 aF aF' 0 0 0
          (wvAt recs 0 (hh * b + fr))).setv (Q 0) ((mkP S Q s W ((kst σb K CK L out).setv (Q 0)
          (decide (aF' < aF)).toNat) 0 0 0 0 0 0 aF aF' 0 0 0 (wvAt recs 0 (hh * b + fr))).val (Q 0) - 1) =
          mkP S Q s W (kst σb K CK L out) 0 0 0 0 0 0 aF aF' 0 0 0 (wvAt recs 0 (hh * b + fr)) := by
        rw [mkP_setvF hS hQ]
        congr 1
        apply WState.eq
        · rfl
        · rfl
        · funext j; simp only [WState.setv_val, Function.update_apply]
          split_ifs with h1
          · subst h1; simp [mkP, hQ.eq_iff, hlt, hF0]
          · rfl
        · rfl
      rw [ey] at y
      exact WExec.seq y em
    have hbr := WExec.ifrT (r := Q 0) (Q := EM (S 6) (S 7) CA CA') (by simp [mkP, hQ.eq_iff, hlt]) hd
    have x5 := hzero (out ++ f aF' aF)
    have hall := WExec.seq x1 (WExec.seq x2 (WExec.seq hbr x5))
    have e1 : min aF aF' = aF' := min_eq_right (le_of_lt hlt)
    have e2 : max aF aF' = aF := max_eq_left (le_of_lt hlt)
    rw [e1, e2]
    unfold ptBody
    exact WExec.mono hall (by omega)
  · have hle : aF ≤ aF' := by omega
    have em := hEmB hle
    rw [← mkP_kst hS hQ s W σb K CK L out hK' hCK', ← mkP_kst hS hQ s W σb K CK L (out ++ f aF aF') hK' hCK'] at em
    have e0 : (kst σb K CK L out).setv (Q 0) (decide (aF' < aF)).toNat = kst σb K CK L out := by
      rw [show (decide (aF' < aF)).toNat = 0 by simp [hlt], ← hF0, wsetv_same]
    rw [e0] at x2
    have hbr := WExec.ifrF (r := Q 0) (P := .seq (.dec (Q 0)) (EM (S 7) (S 6) CA' CA))
      (by simp [mkP, hQ.eq_iff]; exact hF0) em
    have x5 := hzero (out ++ f aF aF')
    have hall := WExec.seq x1 (WExec.seq x2 (WExec.seq hbr x5))
    have e1 : min aF aF' = aF := min_eq_left hle
    have e2 : max aF aF' = aF' := max_eq_right hle
    rw [e1, e2]
    unfold ptBody
    exact WExec.mono hall (by omega)

end Body

end NearCubicWires.WireExponent3_5.SelectionMachine.Point
