import Proof.Wire_3_5.Primitive.SeedFix.C4SK

/-! # C4 per-call setup (item 3), part 12: the SYM setup's numbers, docked

P3:2987-2988, 3011-3016, 2929-2941: from the request, `1^n` and the unary powers, PA's data stage (the call's counts,
`Data.data_step_blank`), C2's copy-in (the counts `unaryList cs` from the data word) and the numbers machine
(`bigM (bigW …)`, parts 2–8): the thirty-nine words of the enumeration, the generator and the compiler request on
their tapes `gW`.

* `extDA`, `extBG`, `midM`, `midCost`, **`mid_run`**.

Paper quantities of the main type: the thirty-nine words (the enumeration's rulers and constants, the generator's
inputs, the compiler request's numbers). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout

theorem vIN : (sTape (ns := Data.DS) (nr := Data.DR) Data.sIN).val = 0 := rfl
theorem vNT : (sTape (ns := Data.DS) (nr := Data.DR) Data.sNT).val = 2 := rfl
theorem vLT : (sTape (ns := Data.DS) (nr := Data.DR) Data.sLT).val = 3 := rfl
theorem vCT : (sTape (ns := Data.DS) (nr := Data.DR) Data.sCT).val = 4 := rfl
theorem vb0 : (bIn (sTape (nr := LNR) (sk 0 0))).val = 0 := rfl
theorem vb113 : (bIn (sTape (nr := LNR) (sk 0 113))).val = 114 := rfl
theorem vcnt : bCnt.val = 674 := rfl

namespace Lay
variable (L : Lay)

/-- The data stage's inputs: the request, `1^n`, the description bound, the fill count. -/
def extDA (j : Fin (Data.DS + 2 + Data.DR + 1)) : Option (Fin L.N) :=
  if j.val = 0 then some L.gP0 else if j.val = 2 then some L.gN1 else if j.val = 3 then some L.gUL
  else if j.val = 4 then some L.gUD else none

/-- The numbers machine's inputs: the request, the counts, the fill count. -/
def extBG (j : Fin (BX + 1)) : Option (Fin L.N) :=
  if j.val = 0 then some L.gP0 else if j.val = 114 then some L.gU else if j.val = 674 then some L.gUW else none

/-- **The numbers**: the data stage, the copy-in, the numbers machine. -/
noncomputable def midM (F : FreeProg) (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) :=
  Composition.machine (RecoveryFocus.machine (slx L.oDA (by have := L.U_eq; have : Data.DS = 9883 := rfl; have : Data.DR = 16 := rfl; unfold oDA; rw [N_eq]; omega) L.extDA) Data.dataM)
  (Composition.machine (RecoveryFocus.machine (slx L.oCP (by unfold oCP; rw [N_eq]; omega) (ext0 L.gDO)) cpZ)
    (RecoveryFocus.machine (slx L.oBG (by have : BX = 676 := rfl; unfold oBG; rw [N_eq]; omega) L.extBG) (bigM (bigW F cr fe ζ Cδ C))))

/-- The numbers' step bound. -/
def midCost (cD : ℕ) (u : List Bool) (W c : ℕ) : ℕ := cD + 1 + (cpZCost u + 1 + bigCost W c)

theorem extDA_ne (g : Fin L.N) (h0 : g ≠ L.gP0) (h2 : g ≠ L.gN1) (h3 : g ≠ L.gUL) (h4 : g ≠ L.gUD) :
    ∀ j, L.extDA j ≠ some g := by
  intro j hj
  unfold extDA at hj
  split_ifs at hj <;> simp at hj <;> simp_all

theorem extBG_ne (g : Fin L.N) (h0 : g ≠ L.gP0) (h2 : g ≠ L.gU) (h3 : g ≠ L.gUW) : ∀ j, L.extBG j ≠ some g := by
  intro j hj
  unfold extBG at hj
  split_ifs at hj <;> simp at hj <;> simp_all

end Lay

end NearCubicWires.WireExponent3_5.PrimT.C4Set
