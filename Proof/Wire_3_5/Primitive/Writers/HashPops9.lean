import Proof.Wire_3_5.Primitive.Writers.HashPops8

/-! # HASH setup (C), P2a part 9: the HASH call's populations program, run

* `cRow`; **`row_ok`**: at a THR call, the row `rowW digsWImpl` (C1's verified digit program) meets the generic loop's
  row contract `RowOK` at every selection index and prime of the call;
* **`hash_pops_run`**: from the loop's entry (the call's payloads, the primes `≤ cut` in unary on `PR`, `a'`, `τ₀`,
  `oOff` in `R 0`, `R 3`, `R 4`, zero scratch registers, `|𝒢|` in `GR`), the populations program writes the populations stream `popsWord (hashPopsOf …)` (the KW writer's input `1`) on the output.

Paper quantity of the main type: the HASH call's populations stream `popsWord (hashPopsOf …)` (P3:2253-2293). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashPops
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.HbM (elemW popRec popsWord)

/-- A row's uniform step bound (digit program `Bm`, digit word `≤ Sm`, `τ₀` digits). -/
def cRow (tau Bm Sm : ℕ) : ℕ := Bm + 1 + (18 * tau + 3 + 1 + (tau * (46 * Sm + 69 + 4) + 1)) + 1 + (7 * Sm + 1)

theorem primes_pos (c : ℕ) : ∀ q ∈ PrimThrW.Joins.primesList c, 1 ≤ q := by
  intro q hq
  unfold PrimThrW.Joins.primesList at hq
  rw [List.mem_filter] at hq
  exact (of_decide_eq_true hq.2 : Nat.Prime q).one_lt.le

section Call
variable {kclk : ℕ} {E : Cost.Envelope} {B : Cost.TimeBudget kclk E}
  (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a' : ℕ}
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
variable {ns nr : ℕ} (cap : ℕ) (L : PL ns nr) (h : L.Ok) (σB : WState ns nr)
include h

/-- **The call's rows meet the loop's row contract.** -/
theorem row_ok (ha' : a' ≤ 4)
    (hpay : ∀ i : Fin 4, σB.st (L.Pay i) = if hi : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, hi⟩) else [])
    (hpayH : ∀ i : Fin 4, σB.sh (L.Pay i) = 0) (h0 : σB.val (L.R 0) = a')
    (h3 : σB.val (L.R 3) = Primitive.thrDigits (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs))
    (h4 : σB.val (L.R 4) = Records.thrOff (I.starParams n hs) Cs carriers)
    (hz : ∀ j : Fin FinalPass.Digs.digsK, 5 ≤ j.val → σB.val (L.R j) = 0) (hT : σB.val L.T = 0) (U Bm Sm : ℕ)
    (hneed : ∀ pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff (I.starParams n hs) Cs alg
      (Primitive.thrCallDen alg I hs Cs)), FinalPass.DigsBody.digsWImpl.need
        (FinalPass.Digs.digsN (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) pr.val) ≤ cap)
    (hB : ∀ pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff (I.starParams n hs) Cs alg
      (Primitive.thrCallDen alg I hs Cs)), FinalPass.DigsBody.digsWImpl.bound
        (FinalPass.Digs.digsN (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) pr.val) ≤ Bm)
    (hS : ∀ (g : Primitive.ThrEq (I.starParams n hs) Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff
      (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs))),
      ((digL (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) g pr).flatMap segW).length ≤ Sm)
    (hn : Primitive.thrDigits (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs) ≤ cap)
    (hc : U + 2 * Sm + 4 ≤ cap) :
    RowOK cap L σB (rowW L FinalPass.DigsBody.digsWImpl) (hNG alg Cs) (hPrimes alg I hs Cs) (hF alg I hs Cs carriers) U
      (cRow (Primitive.thrDigits (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs)) Bm Sm) := by
  intro gi hgi pi hpi t kD hdg hdh hk hdl hdc hgt hp hU
  have hpi' : pi < (SupplierPrime.primesUpTo (Primitive.thrCutoff (I.starParams n hs) Cs alg
      (Primitive.thrCallDen alg I hs Cs))).card := by rw [← hPrimes_length alg I hs Cs]; exact hpi
  set g := (PrimAsm.Enum.thrEqEquiv (I.starParams n hs) Cs alg).symm ⟨gi, hgi⟩ with hg
  set pr := PrimAsm.Enum.primeEquiv (Primitive.thrCutoff (I.starParams n hs) Cs alg
    (Primitive.thrCallDen alg I hs Cs)) ⟨pi, hpi'⟩ with hpr
  have hfe : hF alg I hs Cs carriers gi pi =
      digL (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) g pr := by
    unfold hF; rw [dif_pos hgi, dif_pos hpi']
  have hSg := hS g pr
  have hBg := hB pr
  rw [hfe] at hU ⊢
  have e := row_spec cap L h σB FinalPass.DigsBody.digsWImpl (I.starParams n hs) ha' Cs carriers alg
    (Primitive.thrCallDen alg I hs Cs) g pr t kD hdg hdh hk hdl hdc
    (by rw [hgt, hg, Equiv.apply_symm_apply])
    (by rw [hp, hpr, PrimThrW.Joins.primesList_get])
    hpay hpayH h0 h3 h4 hz hT (hneed pr) hn (by omega) (by omega)
  refine ⟨_, WExec.cast cap e rfl ?_⟩
  have m1 := Nat.mul_le_mul_left (Primitive.thrDigits (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs))
    (show 46 * ((digL (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) g pr).flatMap segW).length
      + 69 + 4 ≤ 46 * Sm + 69 + 4 by omega)
  unfold cRow
  omega

/-- The loop's entry: empty output and digit stream, the selections count in `GR`. -/
def entryLS (G : ℕ) : LS := ⟨[], [], 0, 0, 0, 0, G, 0, 0, 0⟩

/-- **The HASH call's populations, written**: from the loop's entry, `popsWord (hashPopsOf …)` on the output. -/
theorem hash_pops_run (ha' : a' ≤ 4)
    (hpay : ∀ i : Fin 4, σB.st (L.Pay i) = if hi : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, hi⟩) else [])
    (hpayH : ∀ i : Fin 4, σB.sh (L.Pay i) = 0) (h0 : σB.val (L.R 0) = a')
    (h3 : σB.val (L.R 3) = Primitive.thrDigits (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs))
    (h4 : σB.val (L.R 4) = Records.thrOff (I.starParams n hs) Cs carriers)
    (hz : ∀ j : Fin FinalPass.Digs.digsK, 5 ≤ j.val → σB.val (L.R j) = 0) (hT : σB.val L.T = 0)
    (hPR : σB.st L.PR = PrimAsm.Data.unaryList (hPrimes alg I hs Cs)) (Bm Sm : ℕ)
    (hneed : ∀ pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff (I.starParams n hs) Cs alg
      (Primitive.thrCallDen alg I hs Cs)), FinalPass.DigsBody.digsWImpl.need
        (FinalPass.Digs.digsN (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) pr.val) ≤ cap)
    (hB : ∀ pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff (I.starParams n hs) Cs alg
      (Primitive.thrCallDen alg I hs Cs)), FinalPass.DigsBody.digsWImpl.bound
        (FinalPass.Digs.digsN (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) pr.val) ≤ Bm)
    (hS : ∀ (g : Primitive.ThrEq (I.starParams n hs) Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff
      (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs))),
      ((digL (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) g pr).flatMap segW).length ≤ Sm)
    (hn : Primitive.thrDigits (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs) ≤ cap)
    (hc : (popsWord (PrimT.C4H.hashPopsOf alg I hs Cs carriers)).length + 2 * Sm + 4 ≤ cap)
    (hcP : (PrimAsm.Data.unaryList (hPrimes alg I hs Cs)).length + 1 ≤ cap) (hG : hNG alg Cs + 1 ≤ cap) :
    ∃ kD', WExec cap (popsW L (rowW L FinalPass.DigsBody.digsWImpl)) ((entryLS (hNG alg Cs)).w L σB)
      (({ gSt (entryLS (hNG alg Cs)) (hF alg I hs Cs carriers) (hPrimes alg I hs Cs).length (hNG alg Cs) (hNG alg Cs)
          kD' with out := popsWord (PrimT.C4H.hashPopsOf alg I hs Cs carriers) } : LS).w L σB)
      (hNG alg Cs * (pCost (hPrimes alg I hs Cs).length (PrimAsm.Data.unaryList (hPrimes alg I hs Cs)).length
        (cRow (Primitive.thrDigits (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs)) Bm Sm) + 1 +
        (5 * (PrimAsm.Data.unaryList (hPrimes alg I hs Cs)).length + 1 + 1 + 3) + 4) + 1 + 1 + 7) := by
  have hrow := row_ok alg I hs Cs carriers cap L h σB ha' hpay hpayH h0 h3 h4 hz hT
    (popsWord (PrimT.C4H.hashPopsOf alg I hs Cs carriers)).length Bm Sm hneed hB hS hn hc
  have hlen := congrArg List.length (popsWord_eq alg I hs Cs carriers)
  rw [List.length_append, List.length_singleton] at hlen
  obtain ⟨kD', e⟩ := pops_spec cap L h σB (rowW L FinalPass.DigsBody.digsWImpl) (hNG alg Cs) (hPrimes alg I hs Cs)
    (hF alg I hs Cs carriers) _ _ hrow (primes_pos _) hPR hcP hG (entryLS (hNG alg Cs)) 0 rfl rfl rfl rfl rfl rfl
    rfl rfl rfl (by simp [entryLS]; omega) (by omega)
  refine ⟨kD', WExec.cast cap e ?_ le_rfl⟩
  congr 1
  apply LS.ext <;> simp [gSt, entryLS, popsWord_eq]

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.HashPops
