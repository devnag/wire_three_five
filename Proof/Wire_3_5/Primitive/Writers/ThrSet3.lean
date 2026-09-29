import Proof.Wire_3_5.Primitive.Writers.ThrHB2
import Proof.Wire_3_5.Primitive.Writers.BigBank
import Proof.Wire_3_5.Primitive.SeedFix.C4CapC

/-! # c4 THR block, the hash bits' machine on the big bank

The numbers machine kit (`C4Set.bigM`, `big_step`) runs the hash bits' program `ThrHB.hbXW` on its own region
`off_h` above the layout. It reads the request from `gP0` and the capacity `1^W` from `gUW` (lifted); both are returned
unchanged. The marked hash bits `marks hbF` land on the tape `off_h + 122` (stream `121`), and the bank below `off_h`
is kept (**`hb_dock`**).

Paper quantity of the main type: the framed hash bits `frame hb` of the THR input word (P3:2331-2333). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimAsm.BigBank
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable (L : Lay) {x' : ℕ} (hx : 3 + L.X ≤ 3 + x')

/-- The hash bits' machine's inputs on the big bank: the request, the capacity. -/
def extH (j : Fin (BX + 1)) : Option (Fin (3 + x')) :=
  if j.val = 0 then some (liftE hx L.gP0) else if j.val = 674 then some (liftE hx L.gUW) else none

/-- **The hash bits' machine docked on the big bank.** -/
theorem hb_dock (W : ℕ) (w : List Bool) (τ : WState (LNS 0) LNR) (c : ℕ)
    (hxe : WExec (2 * W + 2) ThrHB.hbXW (CellLoopD.blankCellD 0 w [] 0 []) τ c)
    (hτ0 : τ.st (sk 0 0) = frame w) (hbF : List Bool) (hZ : τ.st ThrHB.sZ = marks hbF)
    (off : ℕ) (hoff : off + (BX + 1) ≤ 3 + x') (hol : 3 + L.X ≤ off)
    (B : Fin (3 + x') → List Bool) (hP0 : B (liftE hx L.gP0) = frame w)
    (hW : B (liftE hx L.gUW) = List.replicate W true) (hbl : ∀ i : Fin (3 + x'), off ≤ i.val → B i = []) :
    ∃ B' : Fin (3 + x') → List Bool,
      Step (RecoveryFocus.machine (slx off hoff (extH L hx)) (bigM ThrHB.hbXW)) (bigCost W c) (fun _ => 0) B
        (fun _ => 0) B' ∧
      B' ⟨off + 122, by have : BX = 676 := rfl; omega⟩ = marks hbF ∧
      (∀ i : Fin (3 + x'), i.val < off → B' i = B i) ∧ (∀ i : Fin (3 + x'), off + (BX + 1) ≤ i.val → B' i = []) := by
  have eBX : BX = 676 := rfl
  have eBT : BT = 674 := rfl
  have hN : L.N = 3 + L.X := rfl
  have hLN : (liftE hx L.gP0).val < off := by rw [liftE_val]; have := L.gP0.isLt; omega
  have hLW : (liftE hx L.gUW).val < off := by rw [liftE_val]; have := L.gUW.isLt; omega
  have nPW : liftE hx L.gP0 ≠ liftE hx L.gUW := fun e => by
    have := congrArg Fin.val e; rw [liftE_val, liftE_val] at this; revert this; lv
  obtain ⟨m8, h8⟩ := big_step ThrHB.hbXW w [] W τ c hxe
  obtain ⟨st, bl, un, pv, ex⟩ := stageP h8 off hoff (extH L hx)
    (fun i j g hi hj => by
      unfold extH at hi hj
      split_ifs at hi hj with a0 a1 b0 b1 <;> simp only [Option.some.injEq] at hi hj <;> subst_vars <;>
        first
        | exact Fin.ext (by omega)
        | exact absurd hj nPW
        | exact absurd hj (Ne.symm nPW))
    (fun i g hi => by
      unfold extH at hi
      split_ifs at hi <;> simp only [Option.some.injEq] at hi <;> subst hi
      · exact hLN
      · exact hLW)
    B
    (fun j g hj => by
      unfold extH at hj
      split_ifs at hj with a0 a1 <;> simp only [Option.some.injEq] at hj <;> subst hj <;>
        rw [ac_lt _ _ j (by omega)]
      · rw [hP0]; simp [rawB, Fin.ext_iff, C4Set.vb0, a0]
      · rw [hW]; simp [rawB, Fin.ext_iff, C4Set.vb0, C4Set.vb113, C4Set.vcnt, a1])
    hbl
    (fun j hj => by
      unfold extH at hj
      split_ifs at hj with a0 a1
      by_cases hlt : j.val < BX
      · rw [ac_lt _ _ j hlt]
        simp [rawB, Fin.ext_iff, C4Set.vb0, C4Set.vb113, C4Set.vcnt, a0, a1]
      · rw [ac_ge _ _ j (by omega)])
  refine ⟨_, st, ?_, ?_, fun i hi => bl i hi⟩
  · have hx122 : extH L hx ⟨122, by omega⟩ = none := by unfold extH; simp
    rw [pv ⟨122, by omega⟩ _ hx122 (by simp), ac_lt _ _ _ (by norm_num), ac_lt _ _ _ (by norm_num)]
    have e : (⟨122, by omega⟩ : Fin BT) = sTape (nr := LNR) ThrHB.sZ := rfl
    rw [e, wenc_A_s, hZ]
  · intro i hi
    by_cases h0 : i = liftE hx L.gP0
    · subst h0
      have e0 : extH L hx ⟨0, by omega⟩ = some (liftE hx L.gP0) := by unfold extH; simp
      rw [ex _ _ e0, ac_lt _ _ _ (by norm_num), ac_lt _ _ _ (by norm_num), hP0]
      have e : (⟨0, by omega⟩ : Fin BT) = sTape (nr := LNR) (sk 0 0) := rfl
      rw [e, wenc_A_s, hτ0]
    · by_cases h1 : i = liftE hx L.gUW
      · subst h1
        have e1 : extH L hx ⟨674, by omega⟩ = some (liftE hx L.gUW) := by unfold extH; simp
        rw [ex _ _ e1, ac_lt _ _ _ (by norm_num), ac_ge _ _ _ (by norm_num), hW]
        rfl
      · apply un i hi
        intro j e
        unfold extH at e
        split_ifs at e <;> simp only [Option.some.injEq] at e
        · exact h0 e.symm
        · exact h1 e.symm

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
