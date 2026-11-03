import Lean
import Proof.Wire_3_5.UnionMachine.NumsA4
import Proof.Wire_3_5.UnionMachine.NumsA5
import Proof.Wire_3_5.FinalPass.LiftR
import Proof.Wire_3_5.FinalPass.S5TUtil
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsPh2
import Proof.Wire_3_5.UnionMachine.NumsA6Base


noncomputable section
set_option maxRecDepth 4096


/-! # NW phase (a), part 6: the SYM numbers program on NW's bank

The SYM numbers program `numsP` is a word program on the `x = 0` bank, reading its request on stream `0` and its counts
on stream `113`; NW's input is on `sIn = 150`. Renamed by the swap `0 ↔ 150` (`fsN`, every other stream `sk x j`,
the registers the identity) it runs on NW's bank at ANY capacity `cap ≥ cap₀` (`WExec.liftW`), from a state carrying
the cell's entry: the framed input on `sIn`, `[false]` on stream `1`, the counts on stream `113`, the other images
blank, every head at `0`, every register `0`, the cell `0`. Its exit: the streams as at entry, every head `0` except
stream `113`'s (at most the step count, `WExec.sh_le`), the registers the program's (each `≤ cap₀`), the three
factors of `V`.

* `swp`, `swp_swp`, `fsN`, `fsN_inj`, `fsN_val`, `NumsIn`, `liftIn`, **`numsBank`**.

Paper quantities of the main type: `|E|`, `|FlatSeed|`, `Q` at the request (`V = |E|·|FlatSeed|·Q`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan

section Gate
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The SYM numbers program on NW's bank**, at a SYM request, at any `cap ≥ cap₀ ≥ K₀·(|fpIn|+1)^{D₀}`. -/
theorem numsBank (x : ℕ) (r : FReq l F kclk coef A a ha) (hm : r.1.mode = .sym) (cap₀ cap : ℕ)
    (hc : K0 l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ D0 l F.filterErrDeg ≤ cap₀) (hcap : cap₀ ≤ cap)
    (ω : WState (LNS x) LNR) (hω : NumsIn x (fpIn l F kclk coef A a ha r) (Data.unaryList (countsOf r.1)) ω) :
    ∃ (ω' : WState (LNS x) LNR) (c h : ℕ), WExec cap ((numsP l F).liftW (fsN x) id) ω ω' c ∧
      ω'.st = ω.st ∧ ω'.sh = Function.update ω.sh (sk x 113) h ∧ h ≤ c ∧ ω'.cell = false ∧
      ω'.val (SymDec.G 21) * ω'.val (SymDec.G 41) * ω'.val (PrimT.C4Set.KB 52) = NumsPh2.vOf l F kclk coef A a ha r ∧
      ω'.val (SymDec.G 21) * ω'.val (SymDec.G 41) ≤ cap₀ ∧
      ω'.val (PrimT.C4Set.KB 52) ≤ (fpIn l F kclk coef A a ha r).length ∧
      (∀ q, ω'.val q ≤ cap₀) ∧ c ≤ 3000000 * ((cap₀ + 2) * (cap₀ + 2) * (cap₀ + 2)) := by
  obtain ⟨τ, c, e, hV, hGF, hQ, hst, hsh, hcell, hcost⟩ := numsAt l F kclk coef A a ha r hm cap₀ hc
  obtain ⟨ω', e', hL, hO⟩ := WExec.liftW cap₀ cap hcap (fsN x) (fsN_inj x) id Function.injective_id e ω
    (liftIn x _ _ ω hω)
  have hv0 : ∀ q, (CellLoopD.blankCellD 0 (fpIn l F kclk coef A a ha r) [] 0 (Data.unaryList (countsOf r.1))).val q
      ≤ cap₀ := fun q => by simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets]
  have hvl := FinalPass.S5T.WExec.val_le cap₀ e hv0
  have hsl := WExec.sh_le cap₀ e (sk 0 113)
  have hsh0 : (CellLoopD.blankCellD 0 (fpIn l F kclk coef A a ha r) [] 0 (Data.unaryList (countsOf r.1))).sh
      (sk 0 113) = 0 := by
    simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets]
  have hval : ∀ q, ω'.val q = τ.val q := fun q => hL.val q
  refine ⟨ω', c, τ.sh (sk 0 113), e', ?_, ?_, by omega, by rw [hL.cell, hcell], ?_, ?_, ?_, fun q => by
    rw [hval]; exact hvl q, hcost⟩
  · funext i
    by_cases hi : ∃ j, fsN x j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [hL.st, hst, (liftIn x _ _ ω hω).st]
    · exact (hO.1 i (fun j e => hi ⟨j, e⟩)).2
  · funext i
    by_cases hi : ∃ j, fsN x j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [hL.sh]
      by_cases hj : j = sk 0 113
      · subst hj
        have e113 : fsN x (sk 0 113) = sk x 113 := rfl
        rw [e113, Function.update_self]
      · have hne : fsN x j ≠ sk x 113 := by
          intro e2
          apply hj
          have e113 : fsN x (sk 0 113) = sk x 113 := rfl
          exact fsN_inj x (e2.trans e113.symm)
        rw [Function.update_of_ne hne, hsh j hj, (liftIn x _ _ ω hω).sh]
    · have hne : i ≠ sk x 113 := fun e2 => hi ⟨sk 0 113, e2.symm ▸ rfl⟩
      rw [Function.update_of_ne hne]
      exact (hO.1 i (fun j e => hi ⟨j, e⟩)).1
  · rw [hval, hval, hval]; exact hV
  · rw [hval, hval]; exact hGF
  · rw [hval]; exact hQ

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA

end
