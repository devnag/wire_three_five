import Proof.Wire_3_5.Primitive.SeedFix.W6T

/-! # W6, part 21: the numbers' arithmetic as one word run

P3:2552-2557, 2596-2597, 2551-2553, 2618-2620, 2121-2157, 2220-2231 (the THR numbers `|𝒢|, K, cut, τ₀, |primes|, Σp, A,
B_*, J, t, ℓ₀`): the counts read (`midA_exec`), the prime rows (`primes_exec`), the fixed hash's parameters (`midC_rr`):
* `fA_other`, `f6_other` (registers off the written ones), **`midAP_exec`**, **`mid_exec`**: from the word phase's exit
  (the counts on block C/E's tape `1`, `rN … rCap`, every other register `0`, `sPr` blank) to `sPr = Data.unaryList
  (primesList cut)` and the registers `53 … 65`.

Paper quantities of the main type: the THR numbers above. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

variable (cap : ℕ)

theorem fA_other (f : Fin 80 → ℕ) (g E K cut d : ℕ) (r : Fin 80) (h53 : r ≠ 53) (h54 : r ≠ 54) (h55 : r ≠ 55)
    (h56 : r ≠ 56) (h57 : r ≠ 57) :
    Function.update (Function.update (Function.update (Function.update (Function.update f 53 g) 54 E) 55 K) 56 cut) 57 d r
      = f r := by
  simp only [Function.update_apply, h53, h54, h55, h56, h57, if_false]

theorem f6_other (f : Fin 80 → ℕ) (pr ps : ℕ) (r : Fin 80) (h58 : r ≠ 58) (h59 : r ≠ 59) :
    Function.update (Function.update f 58 pr) 59 ps r = f r := by
  simp only [Function.update_apply, h58, h59, if_false]

def midW (D : ℕ) : WP := .seq (.seq (midAW D) primesW) midCW

theorem midAP_exec (σ : WL) (n g E D K cut d : ℕ) (h48 : σ.val 48 = n) (hz0 : ∀ r : Fin 80, r.val < 48 → σ.val r = 0)
    (hzH : ∀ r : Fin 80, 53 ≤ r.val → σ.val r = 0)
    (hC : σ.st (sBC 1) = List.replicate g true) (hCh : σ.sh (sBC 1) = 0)
    (hE : σ.st (sBE 1) = List.replicate E true) (hEh : σ.sh (sBE 1) = 0) (hPr : σ.st sPr = []) (hPrh : σ.sh sPr = 0)
    (hK : K = 8 * (g + 1) * n ^ D) (hcut : cut = SupplierPrime.canonicalPrimeCutoff E K) (hd : d = Nat.clog 2 cut)
    (hbA : MidBoundsA cap n g E D cut) :
    WExec cap (.seq (midAW D) primesW) σ (pSt (⟨Function.update (Function.update σ.sh (sBC 1) g) (sBE 1) E, σ.st, Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d, σ.cell⟩ : WL) (Data.unaryList (PrimThrW.Joins.primesList cut))
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 (SupplierPrime.primesUpTo cut).card) 59 (ThrQ.primeSum cut)))
      (7 * g + 7 * E + (D + 1) * opU cap + 40 * (opU cap + 1) + 1 +
        (cut * (cut * (8 * (opU cap + 1) + 4) + 14 * (opU cap + 1) + 4) + 8 * (opU cap + 1))) := by
  have h1c : 1 ≤ cut := by rw [hcut]; have := SupplierPrime.canonicalPrimeCutoff_ge_563 E K; omega
  have eA := midA_exec cap σ n g E D K cut d h48 hz0 (hzH _ (by decide)) (hzH _ (by decide)) (hzH _ (by decide))
    (hzH _ (by decide)) (hzH _ (by decide)) hC hCh hE hEh hK hcut hd hbA
  have eP := primes_exec cap (⟨Function.update (Function.update σ.sh (sBC 1) g) (sBE 1) E, σ.st, Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d, σ.cell⟩ : WL) cut (by show (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 56 = cut; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add])
    h1c ((fA_other σ.val g E K cut d 20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide))) ((fA_other σ.val g E K cut d 21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide))) ((fA_other σ.val g E K cut d 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide))) ((fA_other σ.val g E K cut d 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide))) ((fA_other σ.val g E K cut d 24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide))) ((fA_other σ.val g E K cut d 25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide))) ((fA_other σ.val g E K cut d 26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide))) ((fA_other σ.val g E K cut d 27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide))) ((fA_other σ.val g E K cut d 28 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide))) ((fA_other σ.val g E K cut d 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide))) ((fA_other σ.val g E K cut d 30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide))) ((fA_other σ.val g E K cut d 31 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide))) ((fA_other σ.val g E K cut d 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide))) ((fA_other σ.val g E K cut d 34 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))
    ((fA_other σ.val g E K cut d 58 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hzH _ (by decide))) ((fA_other σ.val g E K cut d 59 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hzH _ (by decide))) ((fA_other σ.val g E K cut d 74 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hzH _ (by decide)))
    hPr (by show Function.update (Function.update σ.sh (sBC 1) g) (sBE 1) E sPr = 0; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hPrh)
    hbA.p1 hbA.p2
  exact WExec.seq eA eP

theorem mid_exec (σ : WL) (n a M nc ct g E D K cut d pr ps A B J t : ℕ) (h48 : σ.val 48 = n) (h49 : σ.val 49 = a)
    (h50 : σ.val 50 = M) (h51 : σ.val 51 = nc) (h52 : σ.val 52 = ct) (hz0 : ∀ r : Fin 80, r.val < 48 → σ.val r = 0)
    (hzH : ∀ r : Fin 80, 53 ≤ r.val → σ.val r = 0)
    (hC : σ.st (sBC 1) = List.replicate g true) (hCh : σ.sh (sBC 1) = 0)
    (hE : σ.st (sBE 1) = List.replicate E true) (hEh : σ.sh (sBE 1) = 0) (hPr : σ.st sPr = []) (hPrh : σ.sh sPr = 0)
    (hK : K = 8 * (g + 1) * n ^ D) (hcut : cut = SupplierPrime.canonicalPrimeCutoff E K) (hd : d = Nat.clog 2 cut)
    (hpr : pr = (SupplierPrime.primesUpTo cut).card) (hps : ps = ThrQ.primeSum cut)
    (hA : A = g * (pr * (d * 2))) (hB : B = a * (4096 * ((nc + 1) * (4096 * ct))))
    (hJ : J = Nat.clog 2 (8 * K * A * B + 1)) (ht : t = Nat.clog 2 (8 * K * A * J + 1) + 1)
    (hbA : MidBoundsA cap n g E D cut) (hbC : MidBounds cap g pr d a nc ct K A B J M) :
    WExec cap (midW D) σ (pSt (⟨Function.update (Function.update σ.sh (sBC 1) g) (sBE 1) E, σ.st, Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d, σ.cell⟩ : WL) (Data.unaryList (PrimThrW.Joins.primesList cut)) (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 60 A) 61 B) 62 J) 63 t) 65 (J + 1 + (Nat.clog 2 M - (J + 1)))))
      (7 * g + 7 * E + (D + 1) * opU cap + 40 * (opU cap + 1) + 1 +
        (cut * (cut * (8 * (opU cap + 1) + 4) + 14 * (opU cap + 1) + 4) + 8 * (opU cap + 1)) + 1 +
        100 * (opU cap + 1)) := by
  have eAP := midAP_exec cap σ n g E D K cut d h48 hz0 hzH hC hCh hE hEh hPr hPrh hK hcut hd hbA
  rw [← hpr, ← hps] at eAP
  have eC := RegRun.onP cap (midC_rr cap (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) g pr d a nc ct K A B J t M
    ((f6_other _ pr ps 0 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 1 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 2 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 3 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 4 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 4 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 5 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 6 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 7 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 8 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 9 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 10 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 11 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 12 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 13 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 14 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 15 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 16 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide)))) ((f6_other _ pr ps 17 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hz0 _ (by decide))))
    ((f6_other _ pr ps 60 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 60 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hzH _ (by decide)))) ((f6_other _ pr ps 61 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 61 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hzH _ (by decide)))) ((f6_other _ pr ps 62 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 62 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hzH _ (by decide)))) ((f6_other _ pr ps 63 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 63 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hzH _ (by decide)))) ((f6_other _ pr ps 65 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 65 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hzH _ (by decide))))
    (by show (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 53 = g; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by show (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 58 = pr; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by show (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 57 = d; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add])
    ((f6_other _ pr ps 49 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 49 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h49))
    ((f6_other _ pr ps 51 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 51 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h51))
    ((f6_other _ pr ps 52 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 52 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h52))
    (by show (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 55 = K; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add])
    ((f6_other _ pr ps 50 (by decide) (by decide)).trans ((fA_other σ.val g E K cut d 50 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h50))
    hA hB hJ ht hbC) (⟨Function.update (Function.update σ.sh (sBC 1) g) (sBE 1) E, σ.st, Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d, σ.cell⟩ : WL) (Data.unaryList (PrimThrW.Joins.primesList cut))
  exact WExec.seq eAP eC

end NearCubicWires.WireExponent3_5.PrimT.W6
