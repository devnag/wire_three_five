import Proof.Wire_3_5.Primitive.SeedFix.W6X

/-! # W6, part 25: the arithmetic, then the EW stage

P3:2121-2157, 2150-2157, 2220-2231 (the THR numbers, then the aux filter's `e` and the level windows `W_j`): the word run of
the arithmetic (`mid_exec`) and the docked EW stage (`ew_phase`), chained as steps:
* `tail1M`, **`tail1_run`**: `sPr` the prime rows, `sWin` the level records, the registers `53 … 65` and `rEe = e`, every
  stream off the EW streams, the cell stream `160`, `sPr` and block C/E's tape `1` as found.

Paper quantities of the main type: the THR numbers up to `e`, the prime rows, the level records. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

variable (cap : ℕ)

noncomputable def tail1M (D : ℕ) := Composition.machine (midW D).toProg.compile ewM

theorem ewL_sm_ne (i : Fin 9) : ewL.sm i ≠ sPr ∧ ewL.sm i ≠ sBC 1 ∧ ewL.sm i ≠ sBE 1 ∧ ewL.sm i ≠ 160 := by
  fin_cases i <;> decide

theorem tail1_run (σ : WL) (n a M nc ct g E D K cut d pr ps A B J t : ℕ) (h48 : σ.val 48 = n) (h49 : σ.val 49 = a)
    (h50 : σ.val 50 = M) (h51 : σ.val 51 = nc) (h52 : σ.val 52 = ct) (hz0 : ∀ r : Fin 80, r.val < 48 → σ.val r = 0)
    (hzH : ∀ r : Fin 80, 53 ≤ r.val → σ.val r = 0)
    (hC : σ.st (sBC 1) = List.replicate g true) (hCh : σ.sh (sBC 1) = 0)
    (hE : σ.st (sBE 1) = List.replicate E true) (hEh : σ.sh (sBE 1) = 0) (hPr : σ.st sPr = []) (hPrh : σ.sh sPr = 0)
    (hWs : ∀ i : Fin 9, σ.st (ewL.sm i) = [] ∧ σ.sh (ewL.sm i) = 0) (hcs : σ.st 160 = [] ∧ σ.sh 160 = 0)
    (hK : K = 8 * (g + 1) * n ^ D) (hcut : cut = SupplierPrime.canonicalPrimeCutoff E K) (hd : d = Nat.clog 2 cut)
    (hpr : pr = (SupplierPrime.primesUpTo cut).card) (hps : ps = ThrQ.primeSum cut)
    (hA : A = g * (pr * (d * 2))) (hB : B = a * (4096 * ((nc + 1) * (4096 * ct))))
    (hJ : J = Primitive.listJ A B K) (ht : t = Primitive.listT A B K)
    (hbA : MidBoundsA cap n g E D cut) (hbC : MidBounds cap g pr d a nc ct K A B J M)
    (bE : Primitive.listE A B M K ≤ cap) (hneed : UnionMachine.EwSize.ewNeed (M + A + B + K) ≤ cap) :
    ∃ (τ : WL) (m : ℕ), Step (tail1M D) m (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      m ≤ 7 * g + 7 * E + (D + 1) * opU cap + 40 * (opU cap + 1) + 1 +
        (cut * (cut * (8 * (opU cap + 1) + 4) + 14 * (opU cap + 1) + 4) + 8 * (opU cap + 1)) + 1 +
        100 * (opU cap + 1) + 1 + (20 * (opU cap + 1) + UnionMachine.EwSize.ewBound (M + A + B + K)) ∧
      τ.val = Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 60 A) 61 B) 62 J) 63 t) 65 (J + 1 + (Nat.clog 2 M - (J + 1)))) 64 (Primitive.listE A B M K) ∧
      τ.st sPr = Data.unaryList (PrimThrW.Joins.primesList cut) ∧ τ.st 20 = PrimThrW.Joins.winRecs (PrimThrW.Joins.thrMP M A B K) ∧
      (∀ s, (∀ i, ewL.sm i ≠ s) → s ≠ 160 → s ≠ sPr → τ.st s = σ.st s) ∧
      (∀ s, (∀ i, ewL.sm i ≠ s) → s ≠ 160 → s ≠ sPr → s ≠ sBC 1 → s ≠ sBE 1 → τ.sh s = σ.sh s) ∧
      (∀ i : Fin 9, i ≠ 0 → (τ.st (ewL.sm i)).length ≤ UnionMachine.EwSize.ewBound (M + A + B + K)) ∧
      τ.st 160 = [false] ∧ τ.cell = σ.cell := by
  have e4 := mid_exec cap σ n a M nc ct g E D K cut d pr ps A B J t h48 h49 h50 h51 h52 hz0 hzH hC hCh hE hEh hPr hPrh
    hK hcut hd hpr hps hA hB hJ (by rw [ht, hJ]; rfl) hbA hbC
  have s4 := (WExec.exec cap e4).step
  have hq : ∀ r : Fin 80, r.val < 48 → (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 60 A) 61 B) 62 J) 63 t) 65 (J + 1 + (Nat.clog 2 M - (J + 1)))) r = 0 := fun r hr => by
      have n53 : r ≠ 53 := fun e => by rw [e] at hr; exact absurd hr (by decide)
      have n54 : r ≠ 54 := fun e => by rw [e] at hr; exact absurd hr (by decide)
      have n55 : r ≠ 55 := fun e => by rw [e] at hr; exact absurd hr (by decide)
      have n56 : r ≠ 56 := fun e => by rw [e] at hr; exact absurd hr (by decide)
      have n57 : r ≠ 57 := fun e => by rw [e] at hr; exact absurd hr (by decide)
      have n58 : r ≠ 58 := fun e => by rw [e] at hr; exact absurd hr (by decide)
      have n59 : r ≠ 59 := fun e => by rw [e] at hr; exact absurd hr (by decide)
      have n60 : r ≠ 60 := fun e => by rw [e] at hr; exact absurd hr (by decide)
      have n61 : r ≠ 61 := fun e => by rw [e] at hr; exact absurd hr (by decide)
      have n62 : r ≠ 62 := fun e => by rw [e] at hr; exact absurd hr (by decide)
      have n63 : r ≠ 63 := fun e => by rw [e] at hr; exact absurd hr (by decide)
      have n65 : r ≠ 65 := fun e => by rw [e] at hr; exact absurd hr (by decide)
      simp only [Function.update_apply, n53, n54, n55, n56, n57, n58, n59, n60, n61, n62, n63, n65, if_false]
      exact hz0 r hr
  refine (ew_phase cap (pSt (⟨Function.update (Function.update σ.sh (sBC 1) g) (sBE 1) E, σ.st, Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d, σ.cell⟩ : WL) (Data.unaryList (PrimThrW.Joins.primesList cut)) (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 60 A) 61 B) 62 J) 63 t) 65 (J + 1 + (Nat.clog 2 M - (J + 1))))) M A B K (by show (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 60 A) 61 B) 62 J) 63 t) 65 (J + 1 + (Nat.clog 2 M - (J + 1)))) 50 = M; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, h50])
    (by show (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 60 A) 61 B) 62 J) 63 t) 65 (J + 1 + (Nat.clog 2 M - (J + 1)))) 60 = A; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by show (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 60 A) 61 B) 62 J) 63 t) 65 (J + 1 + (Nat.clog 2 M - (J + 1)))) 61 = B; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by show (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 60 A) 61 B) 62 J) 63 t) 65 (J + 1 + (Nat.clog 2 M - (J + 1)))) 55 = K; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add])
    (by show (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 60 A) 61 B) 62 J) 63 t) 65 (J + 1 + (Nat.clog 2 M - (J + 1)))) 62 = _; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact hJ) (by show (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 60 A) 61 B) 62 J) 63 t) 65 (J + 1 + (Nat.clog 2 M - (J + 1)))) 63 = _; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact ht)
    hq (by show (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 60 A) 61 B) 62 J) 63 t) 65 (J + 1 + (Nat.clog 2 M - (J + 1)))) 64 = 0; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact hzH 64 (by decide))
    (by show (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d) 58 pr) 59 ps) 60 A) 61 B) 62 J) 63 t) 65 (J + 1 + (Nat.clog 2 M - (J + 1)))) 76 = 0; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact hzH 76 (by decide))
    (fun i => by
      have hi := ewL_sm_ne i
      constructor
      · show Function.update σ.st sPr (Data.unaryList (PrimThrW.Joins.primesList cut)) (ewL.sm i) = []
        rw [Function.update_of_ne hi.1]; exact (hWs i).1
      · show Function.update (Function.update (Function.update σ.sh (sBC 1) g) (sBE 1) E) sPr (Data.unaryList (PrimThrW.Joins.primesList cut)).length (ewL.sm i) = 0
        rw [Function.update_of_ne hi.1, Function.update_of_ne hi.2.2.1, Function.update_of_ne hi.2.1]; exact (hWs i).2)
    ⟨by show Function.update σ.st sPr (Data.unaryList (PrimThrW.Joins.primesList cut)) 160 = []; rw [Function.update_of_ne (by decide)]; exact hcs.1,
     by show Function.update (Function.update (Function.update σ.sh (sBC 1) g) (sBE 1) E) sPr (Data.unaryList (PrimThrW.Joins.primesList cut)).length 160 = 0
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        exact hcs.2⟩
    (by have := hbC.aL2; omega) (by have := hbC.aJ3; omega) (by have := hbC.aJ6; omega) (by have := hbC.aJ0; omega)
    (by rw [← hJ]; have := hbC.aL0; omega) (by have h := hbC.aT11; rw [hJ] at h; exact h) bE hneed).elim
    fun τ5 h5 => h5.elim fun m5 h5' => ?_
  refine ⟨τ5, _, s4.seq h5'.1, by have := h5'.2.1; omega, h5'.2.2.1, ?_, h5'.2.2.2.1, fun s h1 h2 h3 => ?_,
    fun s h1 h2 h3 h4 h5 => ?_, fun i hi => (h5'.2.2.2.2.2.1 i hi).1, h5'.2.2.2.2.2.2.1, ?_⟩
  · rw [(h5'.2.2.2.2.2.2.2.2.1 sPr (fun i => (ewL_sm_ne i).1) (by decide)).1]
    show Function.update σ.st sPr (Data.unaryList (PrimThrW.Joins.primesList cut)) sPr = _
    rw [Function.update_self]
  · rw [(h5'.2.2.2.2.2.2.2.2.1 s h1 h2).1]
    show Function.update σ.st sPr (Data.unaryList (PrimThrW.Joins.primesList cut)) s = σ.st s
    rw [Function.update_of_ne h3]
  · rw [(h5'.2.2.2.2.2.2.2.2.1 s h1 h2).2]
    show Function.update (Function.update (Function.update σ.sh (sBC 1) g) (sBE 1) E) sPr (Data.unaryList (PrimThrW.Joins.primesList cut)).length s = σ.sh s
    rw [Function.update_of_ne h3, Function.update_of_ne h5, Function.update_of_ne h4]
  · rw [h5'.2.2.2.2.2.2.2.2.2]; rfl

end NearCubicWires.WireExponent3_5.PrimT.W6
