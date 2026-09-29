import Proof.Wire_3_5.Primitive.Writers.HashCellB

/-! # HASH setup (C), P2b part 4: the HASH call's populations written on the cell

P3:2253-2293: the HASH call's populations stream `popsWord (hashPopsOf …)` (the kept words writer's input `1`, C4KW
`kwIns`). After part B the cell is exactly the populations loop's entry `(entryLS |𝒢|).w (hPL x) σ` (output, digit
stream and the loop's counters empty, `GR = |𝒢|`); the verified loop (`HashPops.hash_pops_run`) writes the stream on
the output `138` and leaves every other stream but the digit stream `137` as it found it.

* **`cP_run`**.

Paper quantity of the main type: the HASH call's populations stream `popsWord (hashPopsOf …)` on stream `138`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimT.HbM (popsWord)

section Call
variable {kclk : ℕ} {E : Cost.Envelope} {B : Cost.TimeBudget kclk E}
  (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a' : ℕ}
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (cap x : ℕ)

/-- The populations program's steps (`hash_pops_run`'s bound). -/
noncomputable def popsCost (Bm Sm : ℕ) : ℕ :=
  HashPops.hNG alg Cs * (HashPops.pCost (HashPops.hPrimes alg I hs Cs).length
    (PrimAsm.Data.unaryList (HashPops.hPrimes alg I hs Cs)).length
    (HashPops.cRow (Primitive.thrDigits (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs)) Bm Sm) + 1 +
    (5 * (PrimAsm.Data.unaryList (HashPops.hPrimes alg I hs Cs)).length + 1 + 1 + 3) + 4) + 1 + 1 + 7

/-- **The HASH call's populations, written on the cell.** -/
theorem cP_run (σ : WState (LNS x) LNR) (ha' : a' ≤ 4)
    (hpay : ∀ i : Fin 4, σ.st (sk x ⟨133 + i.val, by omega⟩) =
      if hi : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, hi⟩) else [])
    (hpayH : ∀ i : Fin 4, σ.sh (sk x ⟨133 + i.val, by omega⟩) = 0)
    (h0 : σ.val ⟨0, by decide⟩ = a')
    (h3 : σ.val ⟨3, by decide⟩ = Primitive.thrDigits (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs))
    (h4 : σ.val ⟨4, by decide⟩ = Records.thrOff (I.starParams n hs) Cs carriers)
    (hG : σ.val ⟨53, by decide⟩ = HashPops.hNG alg Cs)
    (hz : ∀ r : Fin LNR, r.val < 60 → r.val ≠ 0 → r.val ≠ 3 → r.val ≠ 4 → r.val ≠ 53 → σ.val r = 0)
    (hPR : σ.st (sk x 130) = PrimAsm.Data.unaryList (HashPops.hPrimes alg I hs Cs)) (hPRh : σ.sh (sk x 130) = 0)
    (hO : σ.st (sk x 138) = []) (hOh : σ.sh (sk x 138) = 0) (hD : σ.st (sk x 137) = []) (hDh : σ.sh (sk x 137) = 0)
    (Bm Sm : ℕ)
    (hneed : ∀ pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff (I.starParams n hs) Cs alg
      (Primitive.thrCallDen alg I hs Cs)), FinalPass.DigsBody.digsWImpl.need
        (FinalPass.Digs.digsN (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) pr.val) ≤ cap)
    (hB : ∀ pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff (I.starParams n hs) Cs alg
      (Primitive.thrCallDen alg I hs Cs)), FinalPass.DigsBody.digsWImpl.bound
        (FinalPass.Digs.digsN (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) pr.val) ≤ Bm)
    (hS : ∀ (g : Primitive.ThrEq (I.starParams n hs) Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff
      (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs))),
      ((HashPops.digL (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) g pr).flatMap
        HashPops.segW).length ≤ Sm)
    (hn : Primitive.thrDigits (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs) ≤ cap)
    (hc : (popsWord (PrimT.C4H.hashPopsOf alg I hs Cs carriers)).length + 2 * Sm + 4 ≤ cap)
    (hcP : (PrimAsm.Data.unaryList (HashPops.hPrimes alg I hs Cs)).length + 1 ≤ cap)
    (hGc : HashPops.hNG alg Cs + 1 ≤ cap) :
    ∃ τ : WState (LNS x) LNR, WExec cap (HashPops.popsW (hPL x) (HashPops.rowW (hPL x) FinalPass.DigsBody.digsWImpl))
        σ τ (popsCost alg I hs Cs Bm Sm) ∧
      τ.st (sk x 138) = popsWord (PrimT.C4H.hashPopsOf alg I hs Cs carriers) ∧
      (∀ s, s ≠ sk x 138 → s ≠ sk x 137 → τ.st s = σ.st s) ∧ τ.cell = σ.cell := by
  have hL := hPL_ok x
  have eσ : (HashPops.entryLS (HashPops.hNG alg Cs)).w (hPL x) σ = σ := by
    apply WState.eq
    · funext s
      simp only [HashPops.LS.w, HashPops.entryLS, List.length_nil]
      by_cases h1 : s = sk x 138
      · rw [if_pos (show s = (hPL x).O from h1), h1, hOh]
      · rw [if_neg (show ¬ s = (hPL x).O from h1)]
        by_cases h2 : s = sk x 137
        · rw [if_pos (show s = (hPL x).Dg from h2), h2, hDh]
        · rw [if_neg (show ¬ s = (hPL x).Dg from h2)]
          by_cases h3 : s = sk x 130
          · rw [if_pos (show s = (hPL x).PR from h3), h3, hPRh]
          · rw [if_neg (show ¬ s = (hPL x).PR from h3)]
    · funext s
      simp only [HashPops.LS.w, HashPops.entryLS]
      by_cases h1 : s = sk x 138
      · rw [if_pos (show s = (hPL x).O from h1), h1, hO]
      · rw [if_neg (show ¬ s = (hPL x).O from h1)]
        by_cases h2 : s = sk x 137
        · rw [if_pos (show s = (hPL x).Dg from h2), h2, hD]
        · rw [if_neg (show ¬ s = (hPL x).Dg from h2)]
    · funext r
      simp only [HashPops.LS.w, HashPops.entryLS, List.length_nil]
      split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
      · rw [h1]; exact (hz ⟨48, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)).symm
      · rw [h2]; exact (hz ⟨49, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)).symm
      · rw [h3]; exact (hz ⟨50, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)).symm
      · rw [h4]; exact (hz ⟨51, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)).symm
      · rw [h5]; exact hG.symm
      · rw [h6]; exact (hz (hR 1) (by decide) (by decide) (by decide) (by decide) (by decide)).symm
      · rw [h7]; exact (hz (hR 2) (by decide) (by decide) (by decide) (by decide) (by decide)).symm
      · rw [h8]; exact (hz ⟨54, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)).symm
      · rfl
    · rfl
  obtain ⟨kD', e⟩ := HashPops.hash_pops_run alg I hs Cs carriers cap (hPL x) hL σ ha' hpay hpayH h0 h3 h4
    (fun j hj => hz _ (by have := j.isLt; simp only [FinalPass.Digs.digsK] at this; show (j : ℕ) < 60; omega)
      (by show (j : ℕ) ≠ 0; omega) (by show (j : ℕ) ≠ 3; omega) (by show (j : ℕ) ≠ 4; omega)
      (by have := j.isLt; simp only [FinalPass.Digs.digsK] at this; show (j : ℕ) ≠ 53; omega))
    (hz ⟨52, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)) hPR Bm Sm hneed hB hS hn hc hcP
    hGc
  rw [eσ] at e
  refine ⟨_, e, ?_, ?_, ?_⟩
  · exact HashPops.w_st_O (hPL x) hL σ _
  · intro s h1 h2
    exact HashPops.w_st_other (hPL x) hL σ _ s h1 h2
  · rfl

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.HashCell
