import Proof.Wire_3_5.Primitive.Writers.HashNum

/-! # (HASH (a)): the HASH unit decode, part 4: the unit's `DecOK`

**`hdecW F cr`**: the numbers and the index split (`hNW`), then SymDec's branch (`brW`) with the aux FILTER bank
(`hbW`) on the request units and no POP bank (a HASH entry has one row, `R = 1`, one target, `M = 0`, and that row is a
FILTER row). **`hash_dec`**: from the unit's entry, `DecOK` with the loop's emission `unitE TOT 1 0 (hrq Pa pool) j` —
the entry markers, and at the request unit the aux FILTER row's body at the aux seed `(j/5) mod nE` and cell
`(j/5)/nE` (`hbody`) — the request and the counter kept.

Paper quantity of the main type: the HASH tape's unit `j` (`HashFlat.hashTape_flat`, the aux FILTER rows of
P3:2220-2226). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.CellUnit NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.FinalPass.Filt

/-- The aux seed of entry `q`: index `q mod |GapSeed|`. -/
def hseed (Pa : GapParams) (q : ℕ) : GapSeed Pa :=
  (Enum.gapSeedEquiv Pa).symm ⟨q % Fintype.card (GapSeed Pa), Nat.mod_lt _ (Enum.card_gapSeed_pos Pa)⟩

/-- **The aux FILTER row's body** of entry `q` (seed `q mod nE`, cell `q / nE`, slice `0 … len`). -/
def hbody (Pa : GapParams) (pool q : ℕ) : List Bool :=
  (filtRefC (filterTable Pa (hseed Pa q) Pa.len) (SupplierWalk.majorityThreshold Pa.walkLen) Pa.len true
    (sliceLabs (2 * (2 * (q / Fintype.card (GapSeed Pa)))) pool 0 Pa.len)).flatMap
    (fun t => true :: ListMachine.Rec.termWord t)

/-- The HASH request units: entry `q`'s body at the only target. -/
def hrq (Pa : GapParams) (pool : ℕ) : ℕ → ℕ → ℕ → List Bool := fun q _ s => if s = 0 then hbody Pa pool q else []

section Unit
variable (cap : ℕ) (W : WalkBankProducer)

/-- **The HASH unit decode.** -/
def hdecW (F : FiltSetupSpec5 W) (cr : ℕ) : WM (LNS W.x) LNR := .seq (hNW W.x cr) (brW W (hbW W F) .skip)

theorem hash_dec (F : FiltSetupSpec5 W) (cr : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n)
    (w out : List Bool) (j : ℕ) (codes cc : List ℕ) (tl : List Bool) (hw : w = Data.reqW P.n true codes cc tl)
    (hs xs : List ℕ) (tg : ℕ) (hhs : hs.length = 16) (hxs : xs.length ≤ 2) (h0v : hs.getD 0 0 = xs.length)
    (Pa : GapParams) (hPl : Pa.len = 2 * xs.sum) (hPc : Pa.cap = (xs.length + 1) * 4096 * hs.getD 1 0)
    (hPe : Pa.errExp = hs.getD 13 0) (hPc1 : 1 ≤ Pa.cap)
    (hc1 : 2 * w.length + 2 ≤ cap) (hc2 : 2 ^ (natBitLength P.n + 1) ≤ cap) (hc3 : (0 + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcl : ∀ k, (hs ++ (xs ++ [tg])).getD k 0 ≤ cap) (hcs : xs.sum + tg + 4 ≤ cap)
    (hcD1 : hs.getD 13 0 + 2 * xs.sum + (xs.length + 1) * 4096 * hs.getD 1 0 + (xs.length + 1) * 4096 +
      hs.getD 1 0 + 10 ≤ cap)
    (hcG1 : Pa.cap * 32 + 2 ≤ cap) (hcG2 : Pa.len + 8 ≤ cap) (hcG3 : Pa.errExp + 4 ≤ cap)
    (hcG4 : 2 ^ (Pa.seedBits + 1) ≤ cap) (hcG5 : Pa.labelBits + Pa.fieldBits + Pa.walkLen + 512 ≤ cap)
    (hcD3 : 2 * xs.sum + hs.getD 8 0 + 2 ^ Pa.seedBits + 2 ^ (2 * (P.s * (P.r / 2)) + 1) +
      2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5 + 10 ≤ cap)
    (hcI : j + 2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5 + 2 ^ Pa.seedBits + 30 ≤ cap)
    (hc4 : 4 * (j / 5 / 2 ^ Pa.seedBits) ≤ cap)
    (Bf BP : ℕ) (hFc : hbCost cap + F.bound cap ≤ Bf)
    (hFN : F.need Pa.len Pa.cap Pa.errExp Pa.len (2 * (2 * (j / 5 / Fintype.card (GapSeed Pa)))) (2 * xs.sum + hs.getD 8 0) 0
        (Fintype.card (GapSeed Pa)) ≤ cap ∧
      filtPipeBound Pa (hseed Pa (j / 5)) Pa.len (2 * (2 * (j / 5 / Fintype.card (GapSeed Pa)))) (2 * xs.sum + hs.getD 8 0) 0
        (rulerW Pa) (rulerW Pa) ≤ BP) :
    ∃ σD m, WExec cap (hdecW W F cr) (CellLoopD.blankCellD W.x w out j (Data.unaryList (hs ++ (xs ++ [tg])))) σD m ∧
      DecOK cap W σD out (unitE (2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5) 1 0 (hrq Pa (2 * xs.sum + hs.getD 8 0)) j) BP ∧
      σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧ σD.sh (sk W.x 2) = 0 ∧
      m ≤ hNCost P.n w.length cr cap + 1 + (Bf + 12) := by
  obtain ⟨τ, c, e, cle, hV, g0, g1, g2, g7, st, sh, cl, zl, zfs, zT, bd⟩ :=
    hN_run cap W.x cr P hrP w out j codes cc tl hw hs xs tg hhs hxs h0v Pa hPl hPc hPe hPc1 hc1 hc2 hc3 hcl hcs
      hcD1 hcG1 hcG2 hcG3 hcG4 hcG5 hcD3 hcI
  have hcard : Fintype.card (GapSeed Pa) = 2 ^ Pa.seedBits := card_gapSeed Pa
  have hV' : HVals W.x τ j (2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5) (1 * (0 + 3) + 2) 0 (2 ^ Pa.seedBits)
      1 1 1 := hV
  set u := Data.unaryList (hs ++ (xs ++ [tg])) with hu
  have n1B : sk W.x 1 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
  have n01 : sk W.x 0 ≠ sk W.x 1 := fun e => absurd (sk_inj W.x e) (by decide)
  have n0B : sk W.x 0 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
  have n2B : sk W.x 2 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
  have n20 : sk W.x 2 ≠ sk W.x 0 := fun e => absurd (sk_inj W.x e) (by decide)
  have n21 : sk W.x 2 ≠ sk W.x 1 := fun e => absurd (sk_inj W.x e) (by decide)
  have a150 : sk W.x 150 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
  have a151 : sk W.x 151 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
  have b0 : sk W.x 150 ≠ sk W.x 0 := fun e => absurd (sk_inj W.x e) (by decide)
  have b1 : sk W.x 150 ≠ sk W.x 1 := fun e => absurd (sk_inj W.x e) (by decide)
  have b2 : sk W.x 150 ≠ sk W.x 2 := fun e => absurd (sk_inj W.x e) (by decide)
  have c0 : sk W.x 151 ≠ sk W.x 0 := fun e => absurd (sk_inj W.x e) (by decide)
  have c1 : sk W.x 151 ≠ sk W.x 1 := fun e => absurd (sk_inj W.x e) (by decide)
  have c2 : sk W.x 151 ≠ sk W.x 2 := fun e => absurd (sk_inj W.x e) (by decide)
  obtain ⟨σD, m, eB, dok, d0, d2, d2h, mle⟩ := br_spec cap W (hbW W F) .skip τ out w j
    (2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5) 1 0 (2 ^ Pa.seedBits) 1 1 1 Bf BP (hrq Pa (2 * xs.sum + hs.getD 8 0))
    hV' (by rw [st]; simp [CellLoopD.blankCellD, blankCell, n1B, n01.symm])
    (by rw [sh _ n1B]; simp [CellLoopD.blankCellD, blankCell])
    (by rw [st]; simp [CellLoopD.blankCellD, blankCell, a150, b0, b1, b2])
    (by rw [sh _ a150]; simp [CellLoopD.blankCellD, blankCell, b1])
    (by rw [st]; simp [CellLoopD.blankCellD, blankCell, a151, c0, c1, c2])
    (by rw [sh _ a151]; simp [CellLoopD.blankCellD, blankCell, c1])
    (by rw [st]; simp [CellLoopD.blankCellD, blankCell, n0B])
    (by rw [st]; simp [CellLoopD.blankCellD, blankCell, n2B, n20, n21])
    (by rw [sh _ n2B]; simp [CellLoopD.blankCellD, blankCell, n21])
    (fun e r s _ hs => by simp [hrq, hs])
    (fun hf => by
      obtain ⟨τ', m', eF, hm', hdec, k0, k2, k2h⟩ := hb_spec cap W F τ w out u j Pa (hseed Pa (j / 5))
        (j / 5 / 2 ^ Pa.seedBits) (2 * xs.sum + hs.getD 8 0) st sh cl zl zfs zT bd g0 g1 g2
        (by
          rw [hV.h13]
          unfold hseed
          rw [Equiv.apply_symm_apply]
          simp only
          rw [hcard])
        hV.h14 g7 hc4 hPc1 (by rw [← hcard]; exact hFN.1)
      refine ⟨τ', m', eF, ?_, k0, k2, k2h, by omega⟩
      have hr0 : (1 * (0 + 3) + 2) = 5 := by norm_num
      simp only [hrq, if_pos rfl]
      unfold hbody
      rw [hcard] at hFN ⊢
      exact decOK_mono cap W hdec hFN.2)
    (fun hp => by
      exfalso
      obtain ⟨-, -, hlt, -, -, hge⟩ := hp
      have : (j % (1 * (0 + 3) + 2) - 1) / (0 + 3) < 1 := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]; omega
      omega)
  exact ⟨σD, _, WExec.seq e eB, dok, d0, d2, d2h, by omega⟩

end Unit

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
