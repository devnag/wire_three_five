import Proof.Wire_3_5.Primitive.Writers.C3WClass

/-! # C3 request writer, part 22: the budget at a call

The writers' envelopes (`EGs`: the geometry writers at `n^{geoD}`; the gate-field writers at `n^{gsD}`, `n^{gtD}`),
the fill polynomial `CvF·(n+1)^{DvC}` (**`call_hpoly`**), and the writer's steps within
`c_W·classBound (EW l) .preprocessing` (**`call_budget`**).

Paper quantity: the request writer's steps within the preprocessing class `2^{O(Ψ)}` (P3:3108). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.LocalBitMultitape NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.C3Mach NearCubicWires.WireExponent3_5.PrimAsm.C3Field
open NearCubicWires.RepairOrdinary (frame frame_length)
open NearCubicWires.RepairRepresentation (natWord)

section Consts
open NearCubicWires.WireExponent3_5.Cost

/-- The geometry writers' envelope. -/
noncomputable def EGs : Envelope := EGp PrimT.GeoPack.geoD
/-- The geometry writers' coefficient. -/
noncomputable def cGs (cr : ℕ) : ℕ := PrimT.GeoPack.geoC cr * 2 ^ PrimT.GeoPack.geoD
/-- The gate-field writers' coefficients. -/
noncomputable def cGg : ℕ := PrimT.C4GateSym.gsC * 2 ^ PrimT.C4GateSym.gsD
noncomputable def cGt : ℕ :=
  PrimT.C4GateSym.gtC PrimAsm.ThrData.thrDataStage2 * 2 ^ PrimT.C4GateSym.gtD PrimAsm.ThrData.thrDataStage2
/-- The fill polynomial's coefficient. -/
noncomputable def CvF (cr : ℕ) : ℕ := 31 * cGs cr + 9 * (cGg + cGt) + 80
/-- The size's coefficient. -/
noncomputable def KF (cN cr : ℕ) : ℕ :=
  PrimT.GeoPack.cW + 1 + cN + (cGg + cGt) + cGs cr + PrimT.FlipsPack.flipsC cr + 2 * CvF cr + 1

theorem geoD_le : PrimT.GeoPack.geoD ≤ DvC := le_max_left _ _
theorem gsD_le : PrimT.C4GateSym.gsD ≤ DvC := le_trans (le_max_left _ _) (le_max_right _ _)
theorem gtD_le : PrimT.C4GateSym.gtD PrimAsm.ThrData.thrDataStage2 ≤ DvC :=
  le_trans (le_max_right _ _) (le_max_right _ _)
theorem DvC_lt : DvC < D0 := by unfold D0; have := le_max_left DvC PrimT.FlipsPack.flipsD; omega
theorem dW_lt : PrimT.GeoPack.dW < D0 := by unfold D0; have := le_max_left PrimT.GeoPack.dW (max DvC PrimT.FlipsPack.flipsD); omega
theorem flipsD_lt : PrimT.FlipsPack.flipsD < D0 := by
  unfold D0; have := le_max_right DvC PrimT.FlipsPack.flipsD
  have := le_max_right PrimT.GeoPack.dW (max DvC PrimT.FlipsPack.flipsD); omega

end Consts

section Call
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
