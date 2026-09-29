import Proof.Wire_3_5.Primitive.Writers.NumsXT2

/-! # THRTAIL T-A1: the THR dimension stage `NumsXT2`, part 2: the stage, its cost and `DimOK`

The whole THR dimension program: `n` from the request, phases A–C of `NumsXT2` (the THR load term `T` into `rF`),
then THR's dimension tail at `K_L` (`NumsXS.tailW`: the star numbers, `m = 2·kh + L`, `m += K_L·L²`, `m += T`, the
CapReader source of `2^(m_T)`), `m_T = mOfT K_L P + T` with
`T = K_f·C_D·((k' + L)²·C_D·(⌈√(B_T·L)⌉ + 1 + L²) + k' + L²)`, `k' = r·natBitLength(n/r + 1)`.

* `tT2` (**`T`**), **`mT2`** (the dimension `m_T`), `xNeedT2`, `tNeedT2` (the phases' capacity terms), `phWT2`,
  `phasesT2_run`, `numsWT2`, **`TNeed2`** (the stage's capacity needs at the fill count `W`), `numsCostT2`,
  **`numsWT2_spec`**, `numsMT2` (the stage), `numsStageCostT2`, **`nums_stepT2`**, **`dimOK_numsT2`** (the stage meets
  `ShellT.DimOK` at `mT2` with the step count `2·numsStageCostT2 W P + 2`).

Paper quantity of the main type: the THR writer's dimension `2^(m_T)`, `m_T = Θ(Ψ_T)` (P3:3094-3107). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.NumsXT2
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimAsm.NumsX
open NearCubicWires.WireExponent3_5.PrimAsm.NumsXT
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- **The THR load term** `T = K_f·C_D·((k' + L)²·d + k' + L²)`, `d = C_D·(⌈√(B_T·L)⌉ + 1 + L²)`. -/
def tT2 (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) : ℕ :=
  ((((((((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2))) * (((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2)))) * ((((CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (Nat.clog 2 (P.n + 2)))) + (1)) + ((Nat.clog 2 (P.n + 2)) * (Nat.clog 2 (P.n + 2)))) * (CD))) + ((P.r) * (natBitLength (((P.n) / (P.r)) + (1))))) + ((Nat.clog 2 (P.n + 2)) * (Nat.clog 2 (P.n + 2)))) * (CD)) * (Kf)

/-- **The THR writer's dimension** `m_T = mOfT K_L P + T`. -/
def mT2 (KL : ℕ) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) : ℕ :=
  PrimThrW.Shell2.mOfT KL P + tT2 P h0 h1 Cδ C CD Kf

/-- Phase B's square-root capacity term. -/
def xNeedT2 (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) : ℕ :=
  ((Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (Nat.clog 2 (P.n + 2)) + 2) * ((Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (Nat.clog 2 (P.n + 2)) + 2) + (Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (Nat.clog 2 (P.n + 2)) + 10

/-- The phases' value capacity term. -/
def tNeedT2 (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) : ℕ :=
  (P.n) + (P.r) + ((P.n) % (P.r)) + ((P.n) / (P.r)) + (((P.n) / (P.r)) + (1)) + (natBitLength (((P.n) / (P.r)) + (1))) + ((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) + (Nat.clog 2 (P.n + 2)) + ((Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (Nat.clog 2 (P.n + 2))) + (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (Nat.clog 2 (P.n + 2)))) + ((CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (Nat.clog 2 (P.n + 2)))) + (1)) + ((Nat.clog 2 (P.n + 2)) * (Nat.clog 2 (P.n + 2))) + (((CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (Nat.clog 2 (P.n + 2)))) + (1)) + ((Nat.clog 2 (P.n + 2)) * (Nat.clog 2 (P.n + 2)))) + ((((CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (Nat.clog 2 (P.n + 2)))) + (1)) + ((Nat.clog 2 (P.n + 2)) * (Nat.clog 2 (P.n + 2)))) * (CD)) + (((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2))) + ((((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2))) * (((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2)))) + (((((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2))) * (((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2)))) * ((((CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (Nat.clog 2 (P.n + 2)))) + (1)) + ((Nat.clog 2 (P.n + 2)) * (Nat.clog 2 (P.n + 2)))) * (CD))) + ((((((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2))) * (((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2)))) * ((((CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (Nat.clog 2 (P.n + 2)))) + (1)) + ((Nat.clog 2 (P.n + 2)) * (Nat.clog 2 (P.n + 2)))) * (CD))) + ((P.r) * (natBitLength (((P.n) / (P.r)) + (1))))) + (((((((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2))) * (((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2)))) * ((((CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (Nat.clog 2 (P.n + 2)))) + (1)) + ((Nat.clog 2 (P.n + 2)) * (Nat.clog 2 (P.n + 2)))) * (CD))) + ((P.r) * (natBitLength (((P.n) / (P.r)) + (1))))) + ((Nat.clog 2 (P.n + 2)) * (Nat.clog 2 (P.n + 2)))) + ((((((((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2))) * (((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2)))) * ((((CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (Nat.clog 2 (P.n + 2)))) + (1)) + ((Nat.clog 2 (P.n + 2)) * (Nat.clog 2 (P.n + 2)))) * (CD))) + ((P.r) * (natBitLength (((P.n) / (P.r)) + (1))))) + ((Nat.clog 2 (P.n + 2)) * (Nat.clog 2 (P.n + 2)))) * (CD)) + (((((((((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2))) * (((P.r) * (natBitLength (((P.n) / (P.r)) + (1)))) + (Nat.clog 2 (P.n + 2)))) * ((((CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .thr P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (Nat.clog 2 (P.n + 2)))) + (1)) + ((Nat.clog 2 (P.n + 2)) * (Nat.clog 2 (P.n + 2)))) * (CD))) + ((P.r) * (natBitLength (((P.n) / (P.r)) + (1))))) + ((Nat.clog 2 (P.n + 2)) * (Nat.clog 2 (P.n + 2)))) * (CD)) * (Kf)) + (Ledger.rowBSparse h0 h1 2 Cδ P.n) + (CD) + (Kf) + 10

section Stage

theorem qAOut_st (σ : WState NS NR) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) :
    (qAOut σ P h0 h1 Cδ C).st = σ.st ∧ (qAOut σ P h0 h1 Cδ C).sh = σ.sh ∧ (qAOut σ P h0 h1 Cδ C).cell = σ.cell := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [qAOut, StarNums.starOut]

theorem qB1Out_st (σ : WState NS NR) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) :
    (qB1Out σ P h0 h1 Cδ C).st = σ.st ∧ (qB1Out σ P h0 h1 Cδ C).sh = σ.sh ∧
      (qB1Out σ P h0 h1 Cδ C).cell = σ.cell := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [qB1Out]

theorem qBOut_st (σ : WState NS NR) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) :
    (qBOut σ P h0 h1 Cδ C CD Kf).st = σ.st ∧ (qBOut σ P h0 h1 Cδ C CD Kf).sh = σ.sh ∧
      (qBOut σ P h0 h1 Cδ C CD Kf).cell = σ.cell := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [qBOut]

theorem qCOut_st (σ : WState NS NR) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) :
    (qCOut σ P h0 h1 Cδ C CD Kf).st = σ.st ∧ (qCOut σ P h0 h1 Cδ C CD Kf).sh = σ.sh ∧
      (qCOut σ P h0 h1 Cδ C CD Kf).cell = σ.cell := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [qCOut]

/-- Phases A–C. -/
def phWT2 (cr : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) : WM NS NR :=
  .seq (qAW cr ζ Cδ C) (.seq qB1W (.seq (qBW CD Kf) qCW))

/-- Phases A–C's cost. -/
def phCostT2 (cap : ℕ) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf cr : ℕ) : ℕ :=
  qACost cap P h0 h1 Cδ C cr + 1 + (qB1Cost cap P h0 h1 Cδ C + 1 + (qBCost cap P h0 h1 Cδ C CD Kf + 1 +
    qCCost P h0 h1 Cδ C CD Kf))

/-- Phases A–C's exit state. -/
def phOutT2 (σ : WState NS NR) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) : WState NS NR :=
  qCOut (qBOut (qB1Out (qAOut σ P h0 h1 Cδ C) P h0 h1 Cδ C) P h0 h1 Cδ C CD Kf) P h0 h1 Cδ C CD Kf

/-- **Phases A–C, run**: from `n` in `SN 0` (every other register `0`), phase C's exit state. -/
theorem phasesT2_run (cap cr : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) {ζ : ℚ} (h0 : 0 < ζ)
    (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) (σ : WState NS NR) (v10 : σ.val (SN 0) = P.n)
    (v1 : ∀ r : Fin NR, r ≠ 0 → σ.val r = 0) (hcS : (0 + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ cap)
    (hcC : SymDec.CapNeed C .thr P.n P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) cap)
    (hlam : Ledger.rowBLambda h0 h1 2 P.n ≤ cap) (hX : xNeedT2 P h0 h1 Cδ C ≤ cap)
    (hT : tNeedT2 P h0 h1 Cδ C CD Kf ≤ cap) :
    WExec cap (phWT2 cr ζ Cδ C CD Kf) σ (phOutT2 σ P h0 h1 Cδ C CD Kf) (phCostT2 cap P h0 h1 Cδ C CD Kf cr) := by
  obtain ⟨a0, a1, a2, a3, a12, a20, az⟩ := qA_vals P h0 h1 Cδ C σ v10 v1
  obtain ⟨b0, b1, b3, b5, b12, b13, b20, bz⟩ :=
    qB1_vals P h0 h1 Cδ C (qAOut σ P h0 h1 Cδ C) a0 a1 a2 a3 a12 a20 az
  obtain ⟨c0, c1, c3, c4, c5, c10, c12, c13, c14, c20, cz⟩ :=
    qB_vals P h0 h1 Cδ C CD Kf _ b0 b1 b3 b5 b12 b13 b20 bz
  exact WExec.seq (qA_run cap cr h0 h1 Cδ C P hrP σ v10 v1 hcS hcP hcC hlam)
    (WExec.seq (qB1_run cap P h0 h1 Cδ C CD Kf _ a0 a1 a2 a3 a12 a20 az hX hT)
      (WExec.seq (qB_run cap P h0 h1 Cδ C CD Kf _ b0 b1 b3 b5 b12 b13 b20 bz hX hT)
        (qC_run cap P h0 h1 Cδ C CD Kf _ c0 c1 c3 c4 c5 c10 c12 c13 c14 c20 cz hT)))

/-- Phase C's exit values: `n` in `SN 0`, `T` in `rF`, every other register `0`. -/
theorem phOutT2_vals (σ : WState NS NR) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) (v10 : σ.val (SN 0) = P.n)
    (v1 : ∀ r : Fin NR, r ≠ 0 → σ.val r = 0) :
    (phOutT2 σ P h0 h1 Cδ C CD Kf).val (SN 0) = P.n ∧ (phOutT2 σ P h0 h1 Cδ C CD Kf).val rF = tT2 P h0 h1 Cδ C CD Kf ∧
      (∀ r : Fin NR, r ≠ 0 → r ≠ 20 → (phOutT2 σ P h0 h1 Cδ C CD Kf).val r = 0) := by
  obtain ⟨a0, a1, a2, a3, a12, a20, az⟩ := qA_vals P h0 h1 Cδ C σ v10 v1
  obtain ⟨b0, b1, b3, b5, b12, b13, b20, bz⟩ :=
    qB1_vals P h0 h1 Cδ C (qAOut σ P h0 h1 Cδ C) a0 a1 a2 a3 a12 a20 az
  obtain ⟨c0, c1, c3, c4, c5, c10, c12, c13, c14, c20, cz⟩ :=
    qB_vals P h0 h1 Cδ C CD Kf _ b0 b1 b3 b5 b12 b13 b20 bz
  obtain ⟨d0, d20, dz⟩ := qC_vals P h0 h1 Cδ C CD Kf _ c0 c1 c3 c4 c5 c10 c12 c13 c14 c20 cz
  exact ⟨d0, d20, dz⟩

theorem phOutT2_st (σ : WState NS NR) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) :
    (phOutT2 σ P h0 h1 Cδ C CD Kf).st = σ.st ∧ (phOutT2 σ P h0 h1 Cδ C CD Kf).sh = σ.sh := by
  unfold phOutT2
  rw [(qCOut_st _ P h0 h1 Cδ C CD Kf).1, (qBOut_st _ P h0 h1 Cδ C CD Kf).1, (qB1Out_st _ P h0 h1 Cδ C).1,
    (qAOut_st σ P h0 h1 Cδ C).1, (qCOut_st _ P h0 h1 Cδ C CD Kf).2.1, (qBOut_st _ P h0 h1 Cδ C CD Kf).2.1,
    (qB1Out_st _ P h0 h1 Cδ C).2.1, (qAOut_st σ P h0 h1 Cδ C).2.1]
  exact ⟨rfl, rfl⟩

end Stage

/-! ## The whole program and the stage -/

section Whole

/-- **The THR dimension program**: `n`, phases A–C (`T` into `rF`), THR's tail at `K_L`, `m += T`, the source. -/
def numsWT2 (KL cr : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) : WM NS NR :=
  .seq (readNatM true xIN rF rC (SN 0) rP rT) (.seq (phWT2 cr ζ Cδ C CD Kf) (NumsXS.tailW KL cr))

/-- **The stage's capacity needs** at the fill count `W` (capacity `2W + 2`). -/
structure TNeed2 (W : ℕ) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf KL cr : ℕ) : Prop where
  hW : 2 * P.n + cr + 16 + KL * (P.n + 2) ^ 2 ≤ W
  hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ 2 * W + 2
  hcC : SymDec.CapNeed C .thr P.n P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) (2 * W + 2)
  hlam : Ledger.rowBLambda h0 h1 2 P.n ≤ 2 * W + 2
  hX : xNeedT2 P h0 h1 Cδ C ≤ 2 * W + 2
  hT : tNeedT2 P h0 h1 Cδ C CD Kf ≤ 2 * W + 2
  hM : 2 * mT2 KL P h0 h1 Cδ C CD Kf + 3 ≤ 2 * W + 2

/-- The program's cost bound. -/
def numsCostT2 (cap : ℕ) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf KL cr : ℕ) : ℕ :=
  (natBitLength P.n + 2) * (40 * 2 ^ natBitLength P.n + 40) + 1 + (phCostT2 cap P h0 h1 Cδ C CD Kf cr + 1 +
    NumsXS.tailCost cap P KL cr (tT2 P h0 h1 Cδ C CD Kf))

/-- **The THR dimension program's run**: from the filled state, the output stream holds the source of
`2^(mT2 …)`; the request and the fill count stay. -/
theorem numsWT2_spec (KL cr W : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) {ζ : ℚ} (h0 : 0 < ζ)
    (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hN : TNeed2 W P h0 h1 Cδ C CD Kf KL cr) :
    ∃ σF c, WExec (2 * W + 2) (numsWT2 KL cr ζ Cδ C CD Kf) (σN w W) σF c ∧
      σF.st xOUT = srcWord (mT2 KL P h0 h1 Cδ C CD Kf) ∧ σF.st xIN = RepairOrdinary.frame w ∧
      σF.st xCT = List.replicate W true ∧ c ≤ numsCostT2 (2 * W + 2) P h0 h1 Cδ C CD Kf KL cr := by
  have hW := hN.hW
  have hpow := CopyNat.two_pow_natBitLength_le P.n
  -- 1: `n` into `SN 0`
  have r1 := readNatM_spec (2 * W + 2) true xIN rF rC (SN 0) rP rT (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) P.n [] (marks sfx ++ [false]) (σN w W)
    (by simp only [σN, if_pos rfl]; rw [hw]; exact frame_split _ _) (by rfl) rfl rfl rfl rfl
    (by simp only [σN]; rw [pow_succ]; omega)
  obtain ⟨σ1, hσ1⟩ : ∃ y, y = ((σN w W).seth xIN (([] : List Bool).length +
      stp true * (RepairRepresentation.natWord P.n).length)).setv (SN 0) ((σN w W).val (SN 0) + P.n) := ⟨_, rfl⟩
  rw [← hσ1] at r1
  have v1 : ∀ r : Fin NR, r ≠ 0 → σ1.val r = 0 := by
    intro r hr
    have : r ≠ SN 0 := hr
    rw [hσ1]; simp [Function.update_apply, this, σN]
  have v10 : σ1.val (SN 0) = P.n := by rw [hσ1]; simp [σN]
  have s1 : σ1.st = (σN w W).st := by rw [hσ1]; rfl
  have sh1O : σ1.sh xOUT = 0 := by rw [hσ1]; simp [σN, xOUT, xIN]
  -- 2: phases A–C
  have eP := phasesT2_run (2 * W + 2) cr P hrP h0 h1 Cδ C CD Kf σ1 v10 v1 (by omega) hN.hcP hN.hcC hN.hlam hN.hX hN.hT
  obtain ⟨c0, c20, cz⟩ := phOutT2_vals σ1 P h0 h1 Cδ C CD Kf v10 v1
  obtain ⟨stC, shC⟩ := phOutT2_st σ1 P h0 h1 Cδ C CD Kf
  -- 3: the tail
  obtain ⟨τ, c, eT, tO, tK, tc⟩ := NumsXS.tail_run KL cr W P hrP (tT2 P h0 h1 Cδ C CD Kf)
    (phOutT2 σ1 P h0 h1 Cδ C CD Kf) c0 c20 cz
    (by rw [stC, s1]; simp [σN, xOUT, xIN, xCT, xAUX]) (by rw [shC]; exact sh1O) hW hN.hM
  refine ⟨τ, _, WExec.seq r1 (WExec.seq eP eT), tO, ?_, ?_, ?_⟩
  · rw [tK _ (by decide), stC, s1]; simp [σN]
  · rw [tK _ (by decide), stC, s1]; simp [σN, xCT, xIN]
  · unfold numsCostT2; omega

/-- The stage before its teardown: the fill, then the program. -/
noncomputable def numsPT2 (KL cr : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) :=
  Composition.machine fillX.compile (numsWT2 KL cr ζ Cδ C CD Kf).toProg.compile

/-- **The THR dimension stage** (every head back at `0`). -/
noncomputable def numsMT2 (KL cr : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) :=
  MaskedReset.machine (numsPT2 KL cr ζ Cδ C CD Kf) (fun _ => true)

/-- The stage's cost before the teardown. -/
def numsStageCostT2 (W : ℕ) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf KL cr : ℕ) : ℕ :=
  11 * W + 20 + 1 + 1 + 1 + numsCostT2 (2 * W + 2) P h0 h1 Cδ C CD Kf KL cr

/-- **The THR dimension stage's run**: from `frame w` (`w = natWord n ++ sfx`) and `1^W`, every head back at `0`, the
output stream holds the CapReader source `srcWord (mT2 …)`; the request and the fill count stay. -/
theorem nums_stepT2 (KL cr W : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) {ζ : ℚ} (h0 : 0 < ζ)
    (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hN : TNeed2 W P h0 h1 Cδ C CD Kf KL cr) :
    ∃ (tout : Fin (NS + 2 + NR) → List Bool) (m : ℕ),
      Step (numsMT2 KL cr ζ Cδ C CD Kf) (2 * numsStageCostT2 W P h0 h1 Cδ C CD Kf KL cr + 2) (fun _ => 0)
        (Fin.addCases (rawInX w W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => 0)
        (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape xOUT) = srcWord (mT2 KL P h0 h1 Cδ C CD Kf) ∧ tout (sTape xIN) = RepairOrdinary.frame w ∧
      tout (sTape xCT) = List.replicate W true := by
  have s0 := Exec.step (fillX_exec w W)
  obtain ⟨σF, c, hx, o, i, ct, hc⟩ := numsWT2_spec KL cr W P hrP h0 h1 Cδ C CD Kf sfx w hw hN
  have s1 := Exec.step (WExec.exec (2 * W + 2) hx)
  have core : Step (numsPT2 KL cr ζ Cδ C CD Kf) (numsStageCostT2 W P h0 h1 Cδ C CD Kf KL cr) (fun _ => 0)
      (rawInX w W) (wenc (2 * W + 2) σF).H (wenc (2 * W + 2) σF).A :=
    (s0.seq s1).enlarge (by unfold numsStageCostT2; omega)
  obtain ⟨m, hm⟩ := ListMachine.Row.maskBlank core (fun _ => true) (fun _ _ => rfl) 0
  have eh : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (NS + 2 + NR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have eh' : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else (wenc (2 * W + 2) σF).H i)
      (fun _ : Fin 1 => 0) : Fin (NS + 2 + NR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  refine ⟨(wenc (2 * W + 2) σF).A, m, (hm.congr_in eh rfl).congr eh' rfl, ?_, ?_, ?_⟩
  · rw [wenc_A_s, o]
  · rw [wenc_A_s, i]
  · rw [wenc_A_s, ct]

end Whole

section Dim
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.WireExponent3_5.PrimAsm.ShellT
variable {x D D2 Dv DL : ℕ}

/-- **The THR dimension stage meets `DimOK`** at `mT2 …` (ShellX's `x2_step` with `nums_stepT2`): the THR shell v4
(`ShellT.shell_runH4`) runs at `2^(m_T)`. -/
theorem dimOK_numsT2 (KL cr : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) {ζ : ℚ} (h0 : 0 < ζ)
    (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (CD Kf : ℕ) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (W : ℕ) (hN : TNeed2 W P h0 h1 Cδ C CD Kf KL cr) :
    DimOK x D D2 Dv DL (numsMT2 KL cr ζ Cδ C CD Kf) (2 * numsStageCostT2 W P h0 h1 Cδ C CD Kf KL cr + 2)
      (mT2 KL P h0 h1 Cδ C CD Kf) w W := by
  intro B hB0 hct hb
  obtain ⟨tout, m, h, o, i, -⟩ := nums_stepT2 KL cr W P hrP h0 h1 Cδ C CD Kf sfx w hw hN
  have hJ := TJ_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  have hH : ∀ j, HI (q2 x D D2 Dv DL j) = 0 := by
    intro j
    apply HI_ne
    apply ne_TJ
    rcases q2_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with ⟨-, e⟩ | ⟨-, -, e⟩ | ⟨-, -, e⟩ <;>
      rw [e, hJ]
    · rw [T0_val]; omega
    · rw [TW_val]; omega
    · have := nu_ge (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j; omega
  have hA : ∀ j, B (q2 x D D2 Dv DL j) =
      Fin.addCases (NumsX.rawInX w W) (fun _ : Fin 1 => List.replicate 0 false) j := by
    intro j
    rcases q2_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with ⟨h1', e⟩ | ⟨h1', h2', e⟩ | ⟨h1', h2', e⟩ <;>
      rw [e]
    · subst h1'
      rw [hB0]
      simp [iN, NumsX.rawInX]
    · subst h2'
      rw [hct]
      simp [cN, NumsX.rawInX, NumsX.xIN, NumsX.xCT, NumsX.sTape_eq_iffX]
    · rw [hb j]
      revert h1' h2'
      refine Fin.addCases (fun t => ?_) (fun u => ?_) j
      · intro h1' h2'
        have t1 : t ≠ sTape NumsX.xIN := fun e => h1' (by rw [e]; rfl)
        have t2 : t ≠ sTape NumsX.xCT := fun e => h2' (by rw [e]; rfl)
        simp [NumsX.rawInX, t1, t2]
      · intro _ _
        simp
  have d := dock0 h (q2 x D D2 Dv DL) q2_inj HI B hH hA
  refine ⟨_, d, ?_, ?_⟩
  · simp only [oN, Fin.addCases_left]
    exact o
  · simp only [iN, Fin.addCases_left]
    exact i

end Dim

end NearCubicWires.WireExponent3_5.PrimAsm.NumsXT2
