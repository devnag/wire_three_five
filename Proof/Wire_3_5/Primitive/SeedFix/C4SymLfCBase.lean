import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfBBase

/-! # C4.K SymLeafC4, part 3: the SYM part of C4Leaf

P3:3105-3115 (the seed-fixing budget `c₄·seedClasses E₄`: `E₄` before `F`, `c₄` after), P3:3011-3016, 3034-3038 (the
SYM stage), #148 (the floors `CD ≥ CD_s`, `cpsi ≥ 1`), #156/#159 (contract v7, `Atable ≥ Dp + 1`): from the builder
of the free numbers (`SymBuild7`), the C3 request writers (`C3ReqLeaf3` at `c_N = K3`, `D_N = D3`) and C1b's
eval-unchanged lemma (`PadEval`): after `fe`, `E₄ = emax E_W (Atable ≥ Dp+1, cpsi ≥ 1)` and `CD₄ = max(CD_s, CD_W, 1)`;
for every admissible `F`, the capacity constant `C_c` (`sym_fits2`, `sym_bigS2`), `c₄` (`sym_steps_gen`), and at every
call family the branched stage `padStage (symStageU3 …)` at the layout `symLay` (the C3 writer of the family), running
at every SYM call: with rows `sym_plain_run`, degenerate `sym_deg_run` (pad `padCost E ≤ K_P·2^{⌊n/8⌋}`).

* `SymBuild7`, `symSB`, `symFloor`, `symLay`, `pad_le_cap`, **`symLeafC4_of`**, **`symLeafC4`**.

Paper quantity of the main type: the SYM part of the C4 leaf (the fixed seeds within `c₄·seedClasses E₄`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymLf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters

/-- The envelope floor of the SYM stage: the pad's table degree `Dp + 1` and `cpsi ≥ 1`. -/
def symFloor (Dp : ℕ) : Envelope := ⟨0, 0, 0, Dp + 1, 0, 0, 0, 1⟩

/-- The SYM stage's layout at a call family: the unary degree `D`, the family's C3 writer, the loop's tapes. -/
noncomputable def symLay (wa : RepairRepresentation.WilliamsAlgorithm) (S3 : C3ReqIface.C3Stage) (D : ℕ) : Lay :=
  ⟨D + 16, S3, (C4SymW.famU wa).T + 3, 31⟩

theorem symLay_T (wa : RepairRepresentation.WilliamsAlgorithm) (S3 : C3ReqIface.C3Stage) (D : ℕ) :
    (C4SymW.famU wa).T + 1 + 1 + 1 ≤ (symLay wa S3 D).T := by
  show _ ≤ (C4SymW.famU wa).T + 3
  omega

/-- The pad writer's steps at `E ≤ 2^{⌊n/8⌋ + C}` entries. -/
theorem pad_le_cap (E Cc n : ℕ) (hE : E ≤ 2 ^ C4Cap.capExp2 Cc n) :
    C4Pad.padCost E ≤ (8 * C4Pad.W1.length + 28) * 2 ^ Cc * 2 ^ (n / 8) := by
  have hM : 2 ^ C4Cap.capExp2 Cc n = 2 ^ Cc * 2 ^ (n / 8) := by unfold C4Cap.capExp2; rw [pow_add, mul_comm]
  obtain ⟨M, hMd⟩ : ∃ x, x = 2 ^ Cc * 2 ^ (n / 8) := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hMd]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [hM, ← hMd] at hE
  have h1 : E * (4 * C4Pad.W1.length + 10) ≤ M * (4 * C4Pad.W1.length + 10) := Nat.mul_le_mul_right _ hE
  have e : (8 * C4Pad.W1.length + 28) * 2 ^ Cc * 2 ^ (n / 8) = 8 * (M * C4Pad.W1.length) + 28 * M := by
    rw [mul_assoc, ← hMd]; ring
  have e2 : M * (4 * C4Pad.W1.length + 10) = 4 * (M * C4Pad.W1.length) + 10 * M := by ring
  rw [e]
  unfold C4Pad.padCost
  omega

end NearCubicWires.WireExponent3_5.PrimT.C4SymLf
