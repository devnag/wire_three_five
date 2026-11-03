import Proof.Wire_3_5.Primitive.SeedFix.C4BudEBase
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB7Base
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKA
import Proof.Wire_3_5.Primitive.SeedFix.C4PadC
import Proof.Wire_3_5.Primitive.SeedFix.C4KLeafBase

/-! # C4.K SymLeafC4, part 1: the SYM stage at a call with rows

P3:3011-3016 (the SYM tape's entries, the seed of `samp:seed`), 3098-3100 (the budget), 1188-1189 (the star:
`N = 2^{k_h}` live halves, `k_h = s·(r/2) ≥ 1`): at a SYM call with `R = |carriers| + 2a ≥ 1` rows the tape word's second
bit is set (`symTape_plain`), so the branched stage `padStage (symStageU3 …)` runs the SYM stage unchanged
(`padStage_plain`); PA's data stage runs at the unary numbers `C_L(n+1)^D ≥ needW` (`sym_data`); the stage's run from
the numbers machine (`sym_stage_of_big4`), the contract's side conditions at the call (`SymEAt3`) and the C3 writer
(`sym_hc3`) within any budget above its steps (`sym_plain_run`).

* `callKh_pos`, `blockWord_chunk_bit`, **`symTape_plain`**, **`sym_data`**, **`sym_plain_run`**.

Paper quantity of the main type: the SYM stage's output at the call (its seed word) within the budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymLf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapM wrapCost)

/-- `k_h = s·(r/2) ≥ 1` (`r ≥ 2`, `4r ≤ n`, so `s = ⌊log₂(n/r + 1)⌋ ≥ 2`). -/
theorem callKh_pos (P : StarParams) : 1 ≤ SeedFix.callKh P := by
  have h2 := P.two_le_r
  have h4 := P.four_r_le_n
  have hdiv : 4 ≤ P.n / P.r := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hs : 1 ≤ P.s := by
    unfold StarParams.s
    exact Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hr : 1 ≤ P.r / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  unfold SeedFix.callKh
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

/-- **A chunked batch with rows has its tape word's second bit set** (the first entry's first row's marker). -/
theorem blockWord_chunk_bit (N nT R : ℕ) (batch : List SeedFix.SExpr) (hE : 1 ≤ nT * N ^ 2) (hR : 1 ≤ R) :
    (SeedFix.blockWord (SeedFix.JLink.chunk N nT R batch)).getD 1 false = true := by
  obtain ⟨k, hk⟩ : ∃ k, nT * N ^ 2 = k + 1 := ⟨nT * N ^ 2 - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, R = j + 1 := ⟨R - 1, by omega⟩
  unfold SeedFix.blockWord SeedFix.JLink.chunk
  rw [hk, hj, List.range_succ_eq_map, List.range_succ_eq_map]
  simp [SeedFix.entryRec, SeedFix.rowRec]

/-- **The SYM tape at a call with rows has its second bit set.** -/
theorem symTape_plain {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B) {n a : ℕ}
    (hs : I.StarAt n) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (hR : 1 ≤ carriers.length + 2 * a) : (symTape I hs Cs carriers).getD 1 false = true := by
  have h1 := PrimAsm.Enum.symNT_pos I hs Cs carriers
  have h2 : 1 ≤ (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2 := Nat.one_le_pow _ _ (Nat.two_pow_pos _)
  exact blockWord_chunk_bit _ _ _ _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) hR

end NearCubicWires.WireExponent3_5.PrimT.C4SymLf
