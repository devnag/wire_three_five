import Proof.Wire_3_5.Primitive.Writers.SBTypesBase
import Proof.Wire_3_5.Primitive.Writers.FiltNum
import Proof.Wire_3_5.Primitive.SeedFix.C4GeoV
import Proof.Wire_3_5.Primitive.SeedFix.GeoPackBase

/-! # T3: the SB identifications, proved — `SBIdentStmts l` and `SBOutsStmt l`

* the filter's widths at `(2(n+1)^{26}, cap, e)`: **`fieldBits_s`**, **`labelBits_s`** (`⌈log₂ V⌉ = natBitLength (V−1)`,
  `FiltNum.clog_eq_nbl`), **`thr_s`** (the walk's majority `e/4 + 1`), **`seedWidth_s`**;
* **`geo_s`** (`hL`, `dRow`, `dR` in the registers' shapes), **`filterParams_s`**, **`starR_s`**, **`slots_s`** (S4's words
  `4 … 7` of `frontWordsW2` are `s4Core2`'s), **`sbIdent`** : `SBIdentStmts l`;
* **`sbOuts`** : `SBOutsStmt l` (SB's register-shaped words are S4's words `4 … 7`).

Paper quantity of the main types: S4's words `4 … 7` (`s4Core2`, P3:3170-3181; the filter's field, P3:2039-2055; the
walk's threshold; `s4Small2`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.SBId
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

theorem len_ge (n : ℕ) : 2 ≤ 2 * (n + 1) ^ 26 := by
  have := Nat.one_le_pow 26 (n + 1) (by omega); omega

theorem fieldBits_s : PrimAsm.SBIdent.FieldBitsStmt := fun n cap e => by
  show Nat.clog 2 (2 * (n + 1) ^ 26) + 4 = _
  rw [PrimAsm.FiltNum.clog_eq_nbl _ (len_ge n), Nat.mul_comm 2]

theorem labelBits_s : PrimAsm.SBIdent.LabelBitsStmt := fun n cap e hc => by
  show max (Nat.clog 2 (32 * cap)) (Nat.clog 2 (2 * (n + 1) ^ 26)) = _
  rw [PrimAsm.FiltNum.clog_eq_nbl (32 * cap) (by omega), PrimAsm.FiltNum.clog_eq_nbl _ (len_ge n), Nat.mul_comm 32,
    Nat.mul_comm 2]

theorem thr_s : PrimAsm.SBIdent.ThrStmt := fun n cap e => by
  show (2 * (e / 4) + 1 + 1) / 2 = e / 4 + 1
  omega

theorem seedWidth_s : PrimAsm.SBIdent.SeedWidthStmt := fun n cap e hc => by
  have h1 := fieldBits_s n cap e
  have h2 := labelBits_s n cap e hc
  show 160 * (2 * (e / 4)) + 2 * (Filt.wOf (Filters.GapParams.fieldBits ⟨2 * (n + 1) ^ 26, cap, e⟩)
    (Filters.GapParams.labelBits ⟨2 * (n + 1) ^ 26, cap, e⟩) * 128) = _
  rw [h1, h2]
  unfold Filt.wOf
  generalize natBitLength ((n + 1) ^ 26 * 2 - 1) = A
  generalize max (natBitLength (cap * 32 - 1)) A = L
  omega

theorem geo_s : PrimAsm.SBIdent.GeoStmt := fun P =>
  ⟨rfl, by unfold PrimT.C4Geo.hL; omega,
    by show P.r / 2 * (P.b - P.s) + (P.n - P.r * P.b + 1) / 2 = _; rw [Nat.mul_comm],
    by show P.r / 2 * (P.b - P.s) + (P.n - P.r * P.b) / 2 = _; rw [Nat.mul_comm]⟩

end NearCubicWires.WireExponent3_5.PrimT.SBId
