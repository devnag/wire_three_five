import Proof.Wire_3_5.FinalPass.TabEmit2
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellIface

/-! # S4 (f1), the tables writer, part 7: the unit machine (P3:2036-2101)

**`tabU W F5`**: the decode (`decW`), C6's FILTER setup (`F5.prog`, any `FiltSetupSpec5`), the table stages
(`tabPreM`), the emission (`emitT`). **`tabEmit FP L₀ L₁ j`**: unit `j`'s piece of the tables word, the framed table of
seed `j / 2` at mask length `L_{j % 2}` while `j / 2 < |seeds|`, nothing after. **`unit_ok`**: at every unit `j` the
unit machine meets the shell unit interface `PrimThrW.Shell.UnitOK` (from the loop's blank cell with the data `u`:
the request kept, `out ++ tabEmit j ++ [false]` on the output, the counter `1^(j+1)`, within `nU`).

Paper quantity of the main type: the tables word's piece of unit `j` (the regular filter's table of seed `j / 2` at
the mask length of carrier `j % 2`, P3:2036-2101). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.TabW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.PrimAsm.UnitReady
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.Filters

variable (cap : ℕ) (W : WalkBankProducer) (F5 : FiltSetupSpec5 W)

/-- **The tables writer's unit machine.** -/
noncomputable def tabU := Composition.machine (Composition.machine (Composition.machine
  (decW W.x).toProg.compile F5.prog.toProg.compile) (tabPreM W)) (emitT W.x).toProg.compile

/-- **Unit `j`'s piece of the tables word.** -/
def tabEmit (FP : GapParams) (L0 L1 j : ℕ) : List Bool :=
  if h : j / 2 < Fintype.card (GapSeed FP) then
    frame (tableWord (filterTable FP ((Enum.gapSeedEquiv FP).symm ⟨j / 2, h⟩) (if j % 2 = 0 then L0 else L1)))
  else []

theorem Rg2_FR (k : Fin 9) : Rg2 k = FR ⟨if k.val = 0 then 0 else 4 + k.val, by have := k.isLt; split <;> omega⟩ := by
  apply Fin.ext
  simp only [Rg2, FR, Function.Embedding.coeFn_mk]
  split <;> omega

/-- **Every unit meets the shell's unit interface.** -/
theorem unit_ok (FP : GapParams) (n L0 L1 j : ℕ) (w out u : List Bool) (nU : ℕ)
    (hw : w = reqT n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))) (hU1 : 1 ≤ FP.cap)
    (hneed : ∀ L, L = L0 ∨ L = L1 → F5.need FP.len FP.cap FP.errExp L 0 0 0 (Fintype.card (GapSeed FP)) ≤ cap)
    (htab : ∀ (e : GapSeed FP) (L : ℕ), L = L0 ∨ L = L1 → (tableWord (filterTable FP e L)).length ≤ cap)
    (hc : 2 * w.length + 2 ≤ cap) (hj : j + 1 ≤ cap) (hc2 : 2 ≤ cap)
    (hnU : ∀ (e : GapSeed FP) (L : ℕ), L = L0 ∨ L = L1 →
      cpCost u.length + 1 + (decBound w.length j + 1 + F5.bound cap + 1 + tabPreCost FP L (rulerW FP) (rulerW FP) +
        1 + emitBound w.length j (tableWord (filterTable FP e L)).length) ≤ nU) :
    PrimThrW.Shell.UnitOK cap W.x (tabU W F5) nU w u (tabEmit FP L0 L1) j out := by
  set nE := Fintype.card (GapSeed FP) with hnE
  set g := if j / 2 < nE then j / 2 else 0 with hg
  set L := if j % 2 = 0 then L0 else L1 with hL
  have hLc : L = L0 ∨ L = L1 := by rw [hL]; split <;> simp
  have hgc : g < nE := by
    rw [hg]
    split
    · assumption
    · exact Enum.card_gapSeed_pos FP
  -- the decode
  obtain ⟨σD, m1, e1, c1, hIn⟩ := dec_spec cap W.x n FP.len FP.cap FP.errExp L0 L1 nE j w out u hw hc hj hc2
  -- the FILTER setup
  obtain ⟨τ, m2, e2, c2, t0, t0h, t2, t2h, -, -, -, -, Mlab, RW, LW, sample, hRW, hLW, hr⟩ :=
    F5.run cap FP g hgc L 0 0 0 w out u j σD hU1 (Emit.sliceLabs_length 0 0 0 L) (hneed L hLc) hIn
  -- the table
  obtain ⟨σ4, s3, h80, h80h, hFR, hkeep⟩ := tabPre cap W τ out FP _ L 0 0 0 Mlab RW LW sample hr
  have k0 := hkeep 0 (by decide) (by decide) (by decide) (by decide)
  have k1 := hkeep 1 (by decide) (by decide) (by decide) (by decide)
  have k2 := hkeep 2 (by decide) (by decide) (by decide) (by decide)
  have hz : ∀ k, σ4.val (Rg2 k) = 0 := fun k => by
    rw [Rg2_FR, hFR]
    by_cases hk : k.val = 0
    · have e : (⟨if k.val = 0 then 0 else 4 + k.val, by have := k.isLt; split <;> omega⟩ : Fin 20) = 0 :=
        Fin.ext (by simp [hk])
      rw [e]
      exact hr.hF0
    · exact hr.hFz _ (by simp [hk]; omega) (by have := k.isLt; simp [hk]; omega)
  -- the emission
  obtain ⟨σE, m4, e4, c4, o0, o1, o1h, o2⟩ := emitT_spec cap W.x n FP.len FP.cap FP.errExp L0 L1 nE j w out
    (tableWord (filterTable FP ((Enum.gapSeedEquiv FP).symm ⟨g, hgc⟩) L)) hw σ4 (by rw [k0.1, t0]) (by rw [k0.2, t0h])
    (by rw [k1.1, hr.hout]) (by rw [k1.2, hr.houth]) (by rw [k2.1, t2]) (by rw [k2.2, t2h]) h80 h80h hz
    (by rw [hFR, hr.hF18]) (by rw [hFR, hr.hF19]) (by rw [hFR, hr.hF17]) hc hj (htab _ L hLc) hc2
  have hem : (if j / 2 < nE then frame (tableWord (filterTable FP ((Enum.gapSeedEquiv FP).symm ⟨g, hgc⟩) L)) else [])
      = tabEmit FP L0 L1 j := by
    unfold tabEmit
    by_cases h : j / 2 < nE
    · rw [if_pos h, dif_pos h]
      have eg : (⟨g, hgc⟩ : Fin nE) = ⟨j / 2, h⟩ := Fin.ext (by show g = j / 2; rw [hg, if_pos h])
      rw [eg]
    · rw [if_neg h, dif_neg h]
  refine ⟨σE, _, Step.seq (Step.seq (Step.seq (WExec.exec cap e1).step (WExec.exec cap e2).step) s3)
    (WExec.exec cap e4).step, o0, by rw [o1, hem], by rw [o1h, hem], o2, ?_⟩
  have hb := hnU ((Enum.gapSeedEquiv FP).symm ⟨g, hgc⟩) L hLc
  rw [hRW, hLW]
  omega

end NearCubicWires.WireExponent3_5.FinalPass.TabW
