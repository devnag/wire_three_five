import Lean
import Proof.Wire_3_5.FinalPass.Bridge1
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.AssemblyDock3
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsOut2
import Proof.Wire_3_5.FinalPass.SeamsProg
import Proof.Wire_3_5.FinalPass.SeamsProg2
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.FinalPass.SeamsPt
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.S5Seam2
import Proof.Wire_3_5.Primitive.Writers.S5SeamB
import Proof.Wire_3_5.Primitive.Writers.S5SeamB2


noncomputable section
set_option maxRecDepth 4096


/-! # The front phase from the two halves (P3:3105-3115, 3170-3181)

**`frontOfHalves Y E T K : FrontPh3`** at the seeds phase's layout `Y` with the halves' layout `E`: the THR half `T`
(`S5ThrB2`) then the core half `K` (`S5CoreB3`) at `layOf4 Y E`, one bridge step between them. From the entry bank
(the framed input on tape `0`, the rest blank) the THR half's exit is the core half's entry (**`thr_exit`**:
`ThrExit2`), and the core half's exit is the front's `FrontOut` (**`front_run`**). The front's cost is within
`s5Bound (Ct + Cc + 1) (max Dt Dcc)` (**`front_cost_le`**); its width `W` is the core half's.

Paper quantity of the main type: the front's words and the numerator/denominator tapes at the seeds phase's entry,
within the preprocessing class (P3:3105-3115, 3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Bridge
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.Assembly NearCubicWires.WireExponent3_5.FinalPass.Bank

section Front
variable {l : Literals} {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1} {Sw : SymWords}
  (Y : SeedsProg4 l F kclk coef A a ha Sw) (E : LayExt4 l F kclk coef A a ha Sw Y)
  (T : S5ThrB2 l F kclk coef A a ha Sw (layOf4 Y E)) (K : S5CoreB3 l F kclk coef A a ha Sw (layOf4 Y E))

/-- **The THR half's exit is the core half's entry.** -/
theorem thr_exit (r : FReq l F kclk coef A a ha) :
    ∃ Ab' : Fin Y.t → List Bool, Step T.M (T.cost r) (fun _ => 0) (fpEntry l F kclk coef A a ha r) (fun _ => 0) Ab' ∧
      ThrExit2 l F kclk coef A a ha Sw (layOf4 Y E) r Ab' := by
  have hin0 : ∀ k, ((layOf4 Y E).wd k).val ≠ 0 := E.in0
  obtain ⟨Ab', hT, hslot, hsc, hrest⟩ := T.run r (fpEntry l F kclk coef A a ha r) (by simp [fpEntry])
    (fun k _ => by have := hin0 k; simp [fpEntry, this])
    (fun j hj => by have := ((layOf4 Y E).thrOff j hj).1; simp [fpEntry, this])
  have hkeep : ∀ j : Fin Y.t, j.val ≠ 0 → (layOf4 Y E).thrSc j = false →
      (∀ k, thrSlot k → j ≠ (layOf4 Y E).wd k) → Ab' j = [] := fun j h0 hs hw => by
    rw [hrest j hs hw]; simp [fpEntry, h0]
  refine ⟨Ab', hT, ⟨?_, hslot, fun k hk => ?_, ⟨?_, ?_⟩, fun j hj => ?_, fun j h0 hw hN hD hs => ?_⟩⟩
  · rw [hrest ⟨0, (layOf4 Y E).ht⟩ (Bool.eq_false_iff.mpr (fun h => ((layOf4 Y E).thrOff _ h).1 rfl))
      (fun k _ e => hin0 k (by rw [← e]))]
    simp [fpEntry]
  · exact hkeep _ (hin0 k) (Bool.eq_false_iff.mpr (fun h => ((layOf4 Y E).thrOff _ h).2.1 k rfl))
      (fun k' hk' e => hk ((layOf4 Y E).wdInj e ▸ hk'))
  · exact hkeep _ (layOf4 Y E).inN (Bool.eq_false_iff.mpr (fun h => ((layOf4 Y E).thrOff _ h).2.2.1 rfl))
      (fun k _ e => (layOf4 Y E).wdN k e.symm)
  · exact hkeep _ (layOf4 Y E).inD (Bool.eq_false_iff.mpr (fun h => ((layOf4 Y E).thrOff _ h).2.2.2 rfl))
      (fun k _ e => (layOf4 Y E).wdD k e.symm)
  · obtain ⟨ℓ, hℓ, e⟩ := hsc j hj
    exact ⟨ℓ, hℓ.trans (T.len_le r), e⟩
  · exact hkeep j h0 hs (fun k _ => hw k)

/-- **The front phase's run**: the THR half, one bridge step, the core half. -/
theorem front_run (r : FReq l F kclk coef A a ha) :
    Step (Composition.machine T.M K.M) (T.cost r + 1 + K.cost r) (fun _ => 0) (fpEntry l F kclk coef A a ha r)
      (fun _ => 0) (K.exitA r) := by
  obtain ⟨Ab', hT, hex⟩ := thr_exit Y E T r
  exact Step.seq hT (K.run r Ab' hex)

/-- **The front's cost** within `s5Bound (Ct + Cc + 1) (max Dt Dcc)`. -/
theorem front_cost_le (r : FReq l F kclk coef A a ha) :
    T.cost r + 1 + K.cost r ≤ s5Bound l F kclk coef A a ha (T.Ct + K.Cc + 1) (max T.Dt K.Dcc) r := by
  have h1 := le_trans (T.cost_le r) (s5Bound_mono l F kclk coef A a ha T.Ct T.Ct T.Dt (max T.Dt K.Dcc) le_rfl
    (le_max_left _ _) r)
  have h2 := le_trans (K.cost_le r) (s5Bound_mono l F kclk coef A a ha K.Cc K.Cc K.Dcc (max T.Dt K.Dcc) le_rfl
    (le_max_right _ _) r)
  have h3 := one_le_s5Bound l F kclk coef A a ha 1 (max T.Dt K.Dcc) le_rfl r
  have hadd : ∀ C C' : ℕ, s5Bound l F kclk coef A a ha (C + C') (max T.Dt K.Dcc) r =
      s5Bound l F kclk coef A a ha C (max T.Dt K.Dcc) r + s5Bound l F kclk coef A a ha C' (max T.Dt K.Dcc) r := by
    intro C C'; unfold s5Bound; ring
  rw [hadd, hadd]
  omega

/-- **The front phase from the two halves.** -/
noncomputable def frontOfHalves : FrontPh3 l F kclk coef A a ha Sw Y where
  ph := ⟨_, Composition.machine T.M K.M, fun r => T.cost r + 1 + K.cost r, fun _ _ => 0, K.exitA,
    front_run Y E T K⟩
  W := K.W
  hW := K.hW
  out := K.out
  Cf := T.Ct + K.Cc + 1
  Df := max T.Dt K.Dcc
  cost_le := front_cost_le Y E T K
  Cw := K.Cw
  Dw := K.Dw
  W_le := K.W_le


end Front

end NearCubicWires.WireExponent3_5.FinalPass.Bridge

end
