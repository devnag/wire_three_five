import Proof.Wire_3_5.Primitive.Writers.SymFamBase
import Proof.Wire_3_5.Primitive.Writers.PopSetupSpecB2

/-! # PA2 (POP setup): the SYM writer at one call of the family over `PopSetupSpecB2`

`SymFamRun` (`symWM`, `sym_fam_run`) with the POP setup `Q : PopSetupSpecB2 W` (the need's measure reads the row
offset `r4`): the POP rows' bound `pn_block2` (`pn_block` with `+ r4` in the need's measure, `r4 ≤ 4·2^k ≤ K_A·Q`),
the machine `symWM2`, the run **`sym_fam_run2`**.

Paper quantity of the main type: the SYM tape `symTape` (C4's `BAT` word of the call, P3:3011-3016). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline

/-! ## The run at one call, within `costS` -/

section Blocks
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.PopSetup
open NearCubicWires.WireExponent3_5.PrimAsm.PopLink NearCubicWires.WireExponent3_5.PrimAsm.Emit

/-- **The POP rows' needs and pipeline bounds over `PopSetupSpecB2`** (`sym_ready`'s `hPN`). -/
theorem pn_block2 {W : PrimT.WalkBank.WalkBankProducer} (Q : PopSetup.PopSetupSpecB2 W) (h : SB)
    (hQ1 : Q.Kn = h.Qn) (hQ2 : Q.Dn = h.Qd)
    (hpp : ∀ (cap : ℕ) (Pl : FlatListParams) (e : Pl.FlatSeed) (L r4 G off : ℕ) (sgn : Bool) (s : Fin (Pl.M + 1))
      (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length),
      PopPipe.popPipeBound cap Pl e L r4 G off (popMlab r4 G off L) (popLw Pl L) (popR Pl r4 G off L)
          (popCp Pl r4 G off L) (popRW Pl) (popRW Pl) sgn s hlabs ≤
        h.Kp * (cap + Pl.M + Pl.B + Pl.errExp + L + r4 + G + off + Fintype.card Pl.FlatSeed +
          (8 * L + 2) ^ (3 * lbP Pl + 1) + 2) ^ h.Dp * 2 ^ (h.Dp * Pl.errExp))
    {n a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (Pl : FlatListParams) {L k kh T BS Qv KQ cap BPf BPp : ℕ}
    (hPe : Pl.errExp = L + 5) (hPM : Pl.M ≤ 4 * (n + 1) ^ 26) (hPB : Pl.B ≤ 8192 * BS)
    (hcP2 : 2 * Fintype.card Pl.FlatSeed ≤ KQ)
    (hx0 : (carriers.map (·.length)).getD 0 0 ≤ (n + 1) ^ 26)
    (hx1 : (carriers.map (·.length)).getD 1 0 ≤ (n + 1) ^ 26)
    (hy : ∀ j, (cyOf Cs).getD j 0 ≤ (n + 1) ^ 26) (hys : (cyOf Cs).sum ≤ 4 * (n + 1) ^ 26) (h2k : 2 * kh = k)
    (hY : ∀ Lp, Lp ≤ (n + 1) ^ 26 → (8 * Lp + 2) ^ (3 * lbP Pl + 1) ≤ 2 ^ T) (aT : 2 ^ T ≤ KQ)
    (a26 : 8 * (n + 1) ^ 26 ≤ KQ) (aBS : 8192 * BS ≤ KQ) (akk : 8 * 2 ^ k ≤ KQ) (aL : L + 5 ≤ KQ)
    (hml : ∀ row, row < 2 ^ k → (2 * (2 * row) + 4) * pbdG Cs carriers ≤ KQ)
    (hcapQ : h.Qn * (30 * KQ) ^ h.Qd ≤ cap) (hDpm : 2 ^ (h.Dp * (L + 5)) ≤ 32 ^ h.Dp * Qv)
    (hBPp : BPp = h.Kp * (cap + 30 * KQ) ^ h.Dp * (32 ^ h.Dp * Qv)) :
    ∀ i : ℕ, i < a → ∀ (e' : Pl.FlatSeed) (row : ℕ) (sgn : Bool) (s : Fin (Pl.M + 1)), row < 2 ^ (2 * kh) →
      Q.need Pl (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) ≤ cap ∧
      ∀ hl : 4 * pbdL Cs i ≤ (sliceLabs (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i)).length,
        PopPipe.popPipeBound cap Pl e' (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i)
          (popMlab (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i)) (popLw Pl (pbdL Cs i))
          (popR Pl (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popCp Pl (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popRW Pl) (popRW Pl) sgn s hl ≤ BPf + BPp := by
  intro i hi e' row sgn s hrow
  rw [h2k] at hrow
  have hL' : pbdL Cs i ≤ (n + 1) ^ 26 := by unfold pbdL SymDec.sel4; split_ifs <;> exact hy _
  have hO' : pbdOff Cs carriers i ≤ 7 * (n + 1) ^ 26 := by
    have := hy 0; have := hy 1; have := hy 2
    unfold pbdOff SymDec.sel4; split_ifs <;> omega
  have hG' : pbdG Cs carriers ≤ 8 * (n + 1) ^ 26 := by unfold pbdG; omega
  have hmlK := hml row hrow
  have hY' := hY _ hL'
  have hmlb : popMlab (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i) ≤ 3 * KQ := by
    unfold popMlab; omega
  refine ⟨?_, fun hl => ?_⟩
  · have hq := Q.need_le Pl (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i)
    rw [hQ1, hQ2] at hq
    refine le_trans hq (le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)) hcapQ)
    rw [hPe]
    omega
  · have hb := hpp cap Pl e' (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) sgn s hl
    refine le_trans hb ?_
    rw [hPe]
    calc _ ≤ h.Kp * (cap + 30 * KQ) ^ h.Dp * (32 ^ h.Dp * Qv) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)) hDpm
      _ = BPp := hBPp.symm
      _ ≤ BPf + BPp := Nat.le_add_left _ _

end Blocks

section Run
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.PopLink
open NearCubicWires.WireExponent3_5.PrimAsm.Emit

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.SymFam
