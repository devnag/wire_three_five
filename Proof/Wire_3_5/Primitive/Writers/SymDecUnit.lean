import Proof.Wire_3_5.Primitive.Writers.SymDecCall

/-! # PA (d)-SYM decode, part 16: the SYM call's unit decode

At a SYM call `(I, hs, Cs, carriers)` (request word `w`, counts `Data.symCounts`), the unit decode `decW` reaches
`CellUnit.DecOK` at unit `j` with the loop's emission: the SYM tape's unit `j` (`SymFlat.symEmit` over
`SymFlat.symCallUnit`) below the tape's unit count `symNT·N²·EU` (the range of `SymFlat.symTape_flat`), empty past
it; the request and the counter kept.

* **`sym_dec`**: the unit decode at the call, given the ledger's numbers (`r`, the SYM cap, `carrierDeg = 26`,
  `D = 1`), the capacity needs, the FILTER setup's need and pipeline bound at the FILTER units, and the POP bank's run
  from the `Decoded` state on the POP units.

Paper quantities of the main type: the SYM tape's unit `j` (P3:3011-3016) and the loop's decode contract. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.CellUnit NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.Records
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.PrimAsm.Enum
open NearCubicWires.WireExponent3_5.PrimAsm.SymDecEnum
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces

section Unit
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable (cap : ℕ) (W : WalkBankProducer)
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

theorem symCodes_length {n a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) :
    (Data.symCodes a Cs).length = a := by simp [Data.symCodes]

/-- **The SYM call's unit decode.** -/
theorem sym_dec (F : FiltSetupSpec5 W) (pb : WM (LNS W.x) LNR) (cr : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)
    (Cδ : ℕ) (C : Ledger.CapParams) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (tl w out : List Bool)
    (j Kb Cmax Bb BP : ℕ) (ha : a ≤ 4) (hnc : carriers.length ≤ 2) (hrB : B.rOf n = Ledger.rowBr cr n)
    (hcapOf : B.capOf .sym n = Ledger.rowBCap C .sym (B.rOf n) (Ledger.rowBSparse h0 h1 2 Cδ n) n)
    (hcd : I.carrierDeg = 26) (hD : I.D = 1)
    (hw : w = Data.reqW n false (Data.symCodes a Cs) (carriers.map Stars.Carrier.code) tl)
    (hKb : ∀ c ∈ Data.symCodes a Cs, natBitLength c ≤ Kb)
    (hC : ∀ c ∈ carriers.map (·.length) ++ cyOf Cs, c ≤ Cmax)
    (hN1 : P1Need cap w n (Data.symCodes a Cs) (carriers.map Stars.Carrier.code) (carriers.map (·.length)) (cyOf Cs)
      Kb Cmax)
    (hcS : (I.filterErrDeg + 4) * (n + 3) + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq n) (Ledger.rowBt h0 h1 n - 1) ≤ cap)
    (hcC : CapNeed C .sym n (B.rOf n) (Ledger.rowBSparse h0 h1 2 Cδ n) cap)
    (hN2 : NumsNeed cap n (B.capOf .sym n) (I.filterErrDeg * Ledger.Lq n) (cyOf Cs).sum carriers.length
      (Ledger.Lq n) (SeedFix.callKh (I.starParams n hs)) a ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0)
      ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0))
    (hI : j + totV n (B.capOf .sym n) (I.filterErrDeg * Ledger.Lq n) (cyOf Cs).sum carriers.length (Ledger.Lq n)
      (SeedFix.callKh (I.starParams n hs)) a ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
      ((cyOf Cs).getD 3 0) + euV (cyOf Cs).sum carriers.length a + 2 * (cyOf Cs).sum +
      2 ^ (2 * SeedFix.callKh (I.starParams n hs)) +
      stV ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) +
      2 ^ FlatNums.fbv (cyOf Cs).sum (bV carriers.length (B.capOf .sym n)) (Ledger.Lq n + 5) + carriers.length + 20 ≤ cap)
    (hU : 1 ≤ B.capOf .sym n)
    (hcF : 4 * 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) +
      2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + (cyOf Cs).sum ≤ cap)
    (hFc : fbCost cap + F.bound cap ≤ Bb)
    (hFN : ∀ (eg : GapSeed (I.filterParams .sym n)) (r row : ℕ), r < carriers.length →
      row < 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) →
      F.need (I.filterParams .sym n).len (I.filterParams .sym n).cap (I.filterParams .sym n).errExp
          (fbL r ((carriers.map (·.length)).getD 0 0) ((carriers.map (·.length)).getD 1 0)) (2 * (2 * row))
          (2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + (cyOf Cs).sum)
          (fbOff r ((carriers.map (·.length)).getD 0 0)) (Fintype.card (GapSeed (I.filterParams .sym n))) ≤ cap ∧
      filtPipeBound (I.filterParams .sym n) eg
          (fbL r ((carriers.map (·.length)).getD 0 0) ((carriers.map (·.length)).getD 1 0)) (2 * (2 * row))
          (2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + (cyOf Cs).sum)
          (fbOff r ((carriers.map (·.length)).getD 0 0)) (rulerW (I.filterParams .sym n))
          (rulerW (I.filterParams .sym n)) ≤ BP)
    (hP : ∀ σ : WState (LNS W.x) LNR, Decoded W.x cap σ w out j (Data.unaryList (Data.symCounts a Cs carriers)) n a
        carriers.length (cyOf Cs).sum ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
        ((cyOf Cs).getD 3 0) ((carriers.map (·.length)).getD 0 0) ((carriers.map (·.length)).getD 1 0)
        (B.capOf .sym n) (I.filterErrDeg * Ledger.Lq n) (Ledger.Lq n) (SeedFix.callKh (I.starParams n hs)) →
      IsPopU (totV n (B.capOf .sym n) (I.filterErrDeg * Ledger.Lq n) (cyOf Cs).sum carriers.length (Ledger.Lq n)
        (SeedFix.callKh (I.starParams n hs)) a ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
        ((cyOf Cs).getD 3 0)) (carriers.length + 2 * a) (cyOf Cs).sum carriers.length j →
      ∃ τ c, WExec cap pb σ τ c ∧
        DecOK cap W τ out (SymFlat.symCallUnit I hs Cs carriers (j / ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2))
          ((j % ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2) - 1) / ((cyOf Cs).sum + 3))
          ((j % ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2) - 1) % ((cyOf Cs).sum + 3) - 1)) BP ∧
        τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 ∧ c ≤ Bb) :
    ∃ σD m, WExec cap (decW W F pb cr I.filterErrDeg ζ Cδ C)
        (CellLoopD.blankCellD W.x w out j (Data.unaryList (Data.symCounts a Cs carriers))) σD m ∧
      DecOK cap W σD out (unitE (symNT I hs Cs carriers * (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2 *
          ((carriers.length + 2 * a) * ((symListParams I n a Cs carriers).M + 3) + 2)) (carriers.length + 2 * a)
          (symListParams I n a Cs carriers).M (SymFlat.symCallUnit I hs Cs carriers) j) BP ∧
      σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧ σD.sh (sk W.x 2) = 0 ∧
      m ≤ 4 * UnaryPow.sq cap + 1 + (reqParseCost n a carriers.length Kb + 1 + (5 * UnaryPow.sq cap + 1 +
        (30 * UnaryPow.sq cap + 1 + countsCost carriers.length Cmax (cyOf Cs).sum))) + 1 +
        (starCapCost n cr I.filterErrDeg (Ledger.rowBt h0 h1 n) (Ledger.rowBSparse h0 h1 2 Cδ n) (Ledger.Lq n) cap +
        1 + (500 * UnaryPow.sq cap + 1 + (30 * UnaryPow.sq cap + 1 + 26 * UnaryPow.sq cap))) + 1 + (Bb + 12) := by
  have hcl := symCodes_length Cs
  have hn : (I.starParams n hs).n = n := rfl
  have hpow : (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2 = 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) := by
    rw [← pow_mul, mul_comm]
  have hpos : 0 < 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) := by positivity
  have htot := tot_eq_symNT I hs Cs carriers (B.capOf .sym n) ha hcd hD rfl
  have hsum := cy_sum I Cs carriers
  obtain ⟨σD, m, e, d, k0, k2, k2h, hm⟩ := dec_run cap W F pb cr I.filterErrDeg h0 h1 Cδ C (I.starParams n hs) hrB w
    out j (Data.symCodes a Cs) (carriers.map Stars.Carrier.code) tl (carriers.map (·.length)) (cyOf Cs) Kb Cmax
    (B.capOf .sym n) (I.filterErrDeg * Ledger.Lq n) (Ledger.Lq n) (SeedFix.callKh (I.starParams n hs)) Bb BP hw
    (by simp) (by simpa using hnc) (by rw [cyOf_length]; exact ha) hKb hC hN1 hcapOf rfl rfl rfl hcS hcP hcC
    (by rw [List.length_map, hcl]; exact hN2) (by rw [List.length_map, hcl]; exact hI) (I.filterParams .sym n) rfl
    (by show 2 * (n + 1) ^ I.carrierDeg = _; rw [hcd]; rfl) rfl hU hcF hFc (SymFlat.symCallUnit I hs Cs carriers)
    (fun e r s hr hs0 => by
      unfold SymFlat.symCallUnit SymFlat.symReqUnit
      rw [if_pos (by simpa using hr), if_neg hs0])
    (fun hf => by
      rw [List.length_map, hcl] at hf ⊢
      have hr : (j % ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2) - 1) / ((cyOf Cs).sum + 3) <
          carriers.length := hf.2.2.2.2.2.1
      have hr1 : (j % ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2) - 1) / ((cyOf Cs).sum + 3) ≤ 1 := by
        omega
      have hT := hf.1
      rw [hn, htot, ← hsum] at hT
      have ht : j / ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2) / 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) <
          symNT I hs Cs carriers := by
        rw [Nat.div_lt_iff_lt_mul hpos, Nat.div_lt_iff_lt_mul (by omega), ← hpow]
        calc j < symNT I hs Cs carriers * (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2 *
              ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2) := hT
          _ = _ := by ring
      have hrow : j / ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2) %
          2 ^ (2 * SeedFix.callKh (I.starParams n hs)) < 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) :=
        Nat.mod_lt _ hpos
      obtain ⟨hFn, hFp⟩ := hFN (symEnum I hs Cs carriers (j / ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2) /
        2 ^ (2 * SeedFix.callKh (I.starParams n hs)))).1.1 _ _ hr hrow
      refine ⟨_, ?_, ?_, hFn, hFp⟩
      · rw [(symEnum_vals I hs Cs carriers _ ht).1, ← stV_eq_nSt I hs Cs ha,
          ← fbv_eq_nFlat I Cs carriers (B.capOf .sym n) hD rfl]
      · rw [filt_unit I hs Cs carriers _ _ hr hr1 hnc, hpow])
    (fun σ hDd hp => by
      rw [List.length_map, hcl] at hDd hp ⊢
      exact hP σ hDd hp)
  refine ⟨σD, m, e, ?_, k0, k2, k2h, ?_⟩
  · rw [List.length_map, hcl, hn, htot, hsum] at d; exact d
  · rw [List.length_map, List.length_map, hcl, hn] at hm; exact hm

end Unit

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
