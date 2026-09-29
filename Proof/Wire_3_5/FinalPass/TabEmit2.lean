import Proof.Wire_3_5.FinalPass.TabDec3
import Proof.Wire_3_5.FinalPass.TabPre

/-! # S4 (f1), the tables writer, part 6: a unit's emission after its table (P3:2036-2101)

After the table stages the unit's registers are known only where C6's FILTER-ready state fixes them (the FILTER
numbers `FR`, kept by the table stages), so the seed's test is recomputed from the kept request and counter with the
known-zero registers `FR 0, FR 5 … FR 12` (`Rg2`), `FR 18`, `FR 19`: the request's numbers (`parseW` at `Rg2`), the
counter counted, halved, compared with the seed count. **`emitT`**: when `j / 2 < nE`, `frame tw` appended to the
output (`copyE`, `tw` the table on stream `80`, its length `FR 17`); then the counter advanced (`incE`).
**`emitT_spec`**: the output `out ++ (if j / 2 < nE then frame tw else []) ++ [false]`, its head at the end of the
emission, the counter `1^(j+1)`, the request kept.

Paper quantity of the main type: the tables word's piece of unit `j` (the table of seed `j / 2` at mask length
`L_{j % 2}`, nothing past the seeds). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.TabW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe

/-- The emission's parse registers: `FR 0, FR 5 … FR 12`. -/
def Rg2 : Fin 9 ↪ Fin LNR :=
  ⟨fun k => ⟨if k.val = 0 then 230 else 234 + k.val, by have := k.isLt; unfold LNR; split <;> omega⟩,
    fun a b h => Fin.ext (by
      have h1 := congrArg Fin.val h
      have := a.isLt
      have := b.isLt
      try dsimp only at h1
      split_ifs at h1 <;> omega)⟩

theorem notRg2 (q : Fin LNR) (hq : q.val < 230 ∨ 243 ≤ q.val) : ∀ k, q ≠ Rg2 k := fun k e => by
  have h := congrArg Fin.val e
  have := k.isLt
  simp only [Rg2, Function.Embedding.coeFn_mk] at h
  split_ifs at h <;> omega

variable (cap x : ℕ)

/-- **A unit's emission**, the seed's test recomputed. -/
def emitT : WM (LNS x) LNR :=
  .seq (parseW x Rg2) (.seq (cntK (sk x 2) (FR 18) (FR 19)) (.seq (WM.rewind (sk x 2) (FR 19))
    (.seq (div2 (FR 18) (Rg2 0) (Rg2 1)) (.seq (cmpD (Rg2 1) (Rg2 8) (FR 19))
    (.seq (.ifr (Rg2 8) (copyE (sk x 80) (sk x 1) (FR 17)) .skip) (incE (sk x 2) (FR 18)))))))

/-- The emission's cost bound. -/
def emitBound (lw j lt : ℕ) : ℕ := 30 * lw + 50 * j + 15 * lt + 400

theorem emitT_spec (n len cp err L0 L1 nE j : ℕ) (w out tw : List Bool) (hw : w = reqT n len cp err L0 L1 nE)
    (σ : WState (LNS x) LNR) (h0 : σ.st (sk x 0) = frame w) (h0h : σ.sh (sk x 0) = 0)
    (h1 : σ.st (sk x 1) = out ++ [false]) (h1h : σ.sh (sk x 1) = out.length)
    (h2 : σ.st (sk x 2) = List.replicate j true) (h2h : σ.sh (sk x 2) = 0)
    (h80 : σ.st (sk x 80) = tw) (h80h : σ.sh (sk x 80) = 0) (hz : ∀ k, σ.val (Rg2 k) = 0)
    (hF18 : σ.val (FR 18) = 0) (hF19 : σ.val (FR 19) = 0) (hF17 : σ.val (FR 17) = tw.length)
    (hc : 2 * w.length + 2 ≤ cap) (hj : j + 1 ≤ cap) (ht : tw.length ≤ cap) (hc2 : 2 ≤ cap) :
    ∃ (σE : WState (LNS x) LNR) (m : ℕ), WExec cap (emitT x) σ σE m ∧ m ≤ emitBound w.length j tw.length ∧
      σE.st (sk x 0) = frame w ∧ σE.st (sk x 1) = out ++ (if j / 2 < nE then frame tw else []) ++ [false] ∧
      σE.sh (sk x 1) = (out ++ (if j / 2 < nE then frame tw else [])).length ∧
      σE.st (sk x 2) = List.replicate (j + 1) true := by
  have n01 := skn x 0 1 (by decide)
  have n02 := skn x 0 2 (by decide)
  have n12 := skn x 1 2 (by decide)
  have n801 := skn x 80 1 (by decide)
  have n802 := skn x 80 2 (by decide)
  have hlw : nE ≤ w.length := by
    have := congrArg List.length (reqT_eq n len cp err L0 L1 nE)
    rw [← hw] at this
    rw [this]
    simp [Data.unaryList]
    omega
  have r18 : ∀ k, FR 18 ≠ Rg2 k := notRg2 (FR 18) (by decide)
  have r19 : ∀ k, FR 19 ≠ Rg2 k := notRg2 (FR 19) (by decide)
  have r17 : ∀ k, FR 17 ≠ Rg2 k := notRg2 (FR 17) (by decide)
  -- the request's numbers
  obtain ⟨σA, mA, eA, cA, sA, hA, lA, -, -, -, -, -, aNE, aO, aP0, aP1⟩ := parse_spec cap x Rg2 n len cp err L0 L1 nE σ
    (by rw [h0, hw]) h0h hz (by rw [← hw]; exact hc)
  -- the counter
  have eB1 := cntK_spec cap (sk x 2) (FR 18) (FR 19) (by decide) j (by omega) j 0 σA (by omega)
    (by rw [sA, h2]) (by rw [hA, h2h]) (by rw [aO _ r18, hF18]; omega) (by rw [aO _ r19, hF19]; omega)
  obtain ⟨σB1, hB1⟩ : ∃ y : WState (LNS x) LNR, y = ((σA.seth (sk x 2) j).setv (FR 18) (σA.val (FR 18) + j)).setv
      (FR 19) (σA.val (FR 19) + j) := ⟨_, rfl⟩
  rw [← hB1] at eB1
  have eB2 := wrewind_spec cap (sk x 2) (FR 19) j σB1 (by rw [hB1]; simp [aO _ r19, hF19])
    (by rw [hB1]; simp [aO _ r19, hF19]; omega)
  obtain ⟨σB2, hB2⟩ : ∃ y : WState (LNS x) LNR, y = (σB1.setv (FR 19) 0).seth (sk x 2) (σB1.sh (sk x 2) - j) :=
    ⟨_, rfl⟩
  rw [← hB2] at eB2
  have b2st : σB2.st = σ.st := by rw [hB2, hB1, ← sA]; rfl
  have b2sh : ∀ s, σB2.sh s = σ.sh s := fun s => by
    rw [hB2, hB1]
    by_cases hs : s = sk x 2
    · rw [hs]; simp [hA, h2h]
    · simp [Function.update_of_ne hs, hA]
  have b2v : ∀ q, q ≠ FR 18 → q ≠ FR 19 → σB2.val q = σA.val q := fun q a b => by
    rw [hB2, hB1]; simp [Function.update_of_ne a, Function.update_of_ne b]
  have b2a : σB2.val (FR 18) = j := by
    rw [hB2, hB1]; simp [Function.update_of_ne (by decide : FR 18 ≠ FR 19), aO _ r18, hF18]
  have b2b : σB2.val (FR 19) = 0 := by rw [hB2]; simp
  -- halving
  have eB3 := div2_spec cap (FR 18) (Rg2 0) (Rg2 1) (r18 0) (r18 1) (Rg2.injective.ne (by decide)) hc2 j 0 σB2 b2a
    (by omega) (by rw [b2v _ (r18 0).symm (r19 0).symm, aP0]) (by rw [b2v _ (r18 1).symm (r19 1).symm, aP1])
    (by omega)
  obtain ⟨σB3, hB3⟩ : ∃ y : WState (LNS x) LNR, y = ((σB2.setv (FR 18) 0).setv (Rg2 0) ((0 + j) % 2)).setv (Rg2 1)
      ((0 + j) / 2) := ⟨_, rfl⟩
  rw [← hB3] at eB3
  have b3h : σB3.val (Rg2 1) = j / 2 := by rw [hB3, wsetv_val_self, Nat.zero_add]
  have b3ne : σB3.val (Rg2 8) = nE := by
    rw [hB3, wsetv_val_ne _ _ (Rg2.injective.ne (by decide)), wsetv_val_ne _ _ (Rg2.injective.ne (by decide)),
      wsetv_val_ne _ _ (r18 8).symm, b2v _ (r18 8).symm (r19 8).symm, aNE]
  have b3g : σB3.val (FR 19) = 0 := by
    rw [hB3, wsetv_val_ne _ _ (r19 1), wsetv_val_ne _ _ (r19 0), wsetv_val_ne _ _ (by decide : FR 19 ≠ FR 18), b2b]
  have b3a : σB3.val (FR 18) = 0 := by
    rw [hB3, wsetv_val_ne _ _ (r18 1), wsetv_val_ne _ _ (r18 0), wsetv_val_self]
  -- the seed's test
  have eB4 := cmpD_spec cap (Rg2 1) (Rg2 8) (FR 19) (Rg2.injective.ne (by decide)) (r19 1).symm (r19 8).symm (j / 2)
    σB3 b3h (by omega) (by rw [b3ne]; omega) (by rw [b3g]; omega)
  obtain ⟨σB4, hB4⟩ : ∃ y : WState (LNS x) LNR, y = ((σB3.setv (Rg2 1) 0).setv (Rg2 8) (σB3.val (Rg2 8) - j / 2)).setv
      (FR 19) (σB3.val (FR 19) + j / 2) := ⟨_, rfl⟩
  rw [← hB4] at eB4
  have b4st : σB4.st = σ.st := by rw [hB4, hB3, ← b2st]; rfl
  have b4sh : ∀ s, σB4.sh s = σ.sh s := fun s => by rw [hB4, hB3]; exact b2sh s
  have b4ne : σB4.val (Rg2 8) = nE - j / 2 := by
    rw [hB4, wsetv_val_ne _ _ (r19 8).symm, wsetv_val_self, b3ne]
  have b4a : σB4.val (FR 18) = 0 := by
    rw [hB4, wsetv_val_ne _ _ (by decide : FR 18 ≠ FR 19), wsetv_val_ne _ _ (r18 8), wsetv_val_ne _ _ (r18 1), b3a]
  have b4c : σB4.val (FR 17) = tw.length := by
    rw [hB4, wsetv_val_ne _ _ (by decide : FR 17 ≠ FR 19), wsetv_val_ne _ _ (r17 8), wsetv_val_ne _ _ (r17 1), hB3,
      wsetv_val_ne _ _ (r17 1), wsetv_val_ne _ _ (r17 0), wsetv_val_ne _ _ (by decide : FR 17 ≠ FR 18),
      b2v _ (by decide) (by decide), aO _ r17, hF17]
  -- the table's frame, when the seed is below the count
  obtain ⟨σC, mC, eC, cC, oC, ohC, sC, hC, vC⟩ : ∃ (σC : WState (LNS x) LNR) (mC : ℕ),
      WExec cap (.ifr (Rg2 8) (copyE (sk x 80) (sk x 1) (FR 17)) .skip) σB4 σC mC ∧ mC ≤ copyCost tw.length + 1 ∧
      σC.st (sk x 1) = out ++ (if j / 2 < nE then frame tw else []) ++ [false] ∧
      σC.sh (sk x 1) = (out ++ (if j / 2 < nE then frame tw else [])).length ∧
      (∀ s, s ≠ sk x 1 → σC.st s = σB4.st s) ∧ (∀ s, s ≠ sk x 1 → s ≠ sk x 80 → σC.sh s = σB4.sh s) ∧
      (∀ r, r ≠ FR 17 → σC.val r = σB4.val r) := by
    by_cases hlt : j / 2 < nE
    · obtain ⟨σ', e', o', oh', s', h'', v', -⟩ := copyE_spec cap (sk x 80) (sk x 1) (FR 17) n801 tw out σB4 b4c ht
        (by rw [b4st, h80]) (by rw [b4sh, h80h]) (by rw [b4st, h1]) (by rw [b4sh, h1h])
      refine ⟨σ', _, WExec.ifrT (by rw [b4ne]; omega) e', by omega, by rw [if_pos hlt]; exact o', by
        rw [if_pos hlt]; exact oh', s', h'', v'⟩
    · refine ⟨σB4, _, WExec.ifrF (by rw [b4ne]; omega) (WExec.skip σB4), by omega, ?_, ?_, fun _ _ => rfl,
        fun _ _ _ => rfl, fun _ _ => rfl⟩
      · rw [if_neg hlt, b4st, h1]; simp
      · rw [if_neg hlt, b4sh, h1h]; simp
  -- the counter advanced
  obtain ⟨σE, eE, kE, khE, sE, hE, -, -⟩ := incE_spec cap (sk x 2) (FR 18) j hj σC
    (by rw [sC _ n12.symm, b4st, h2]) (by rw [hC _ n12.symm n802.symm, b4sh, h2h])
    (by rw [vC _ (by decide), b4a])
  refine ⟨σE, _, WExec.seq eA (WExec.seq eB1 (WExec.seq eB2 (WExec.seq eB3 (WExec.seq eB4 (WExec.seq eC eE))))), ?_,
    ?_, ?_, ?_, kE⟩
  · unfold emitBound incCostE
    have hj2 : j / 2 ≤ j := Nat.div_le_self j 2
    rw [← hw] at cA
    unfold copyCost at cC
    omega
  · rw [sE _ n02, sC _ n01, b4st, h0]
  · rw [sE _ n12, oC]
  · rw [hE _ n12, ohC]

end NearCubicWires.WireExponent3_5.FinalPass.TabW
