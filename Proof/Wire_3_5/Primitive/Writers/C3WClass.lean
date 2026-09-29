import Proof.Wire_3_5.Primitive.Writers.C3WCostCall
import Proof.Wire_3_5.UnionMachine.PreProof
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrB
import Proof.Wire_3_5.Primitive.Writers.ThrData2

/-! # C3 request writer, part 21: the call's steps in the preprocessing class

With the load-constant floor `C_D ≥ 1` the load is at least `k + L` (`PreProof.kL_le_loadPsi`), so the call's size
`2^k·(n+1)^{D₀}·(Ψ+1)` is at most `2^{(D₀+2)Ψ}` (`size_le`), and the writer's steps are within
`c_W·2^{E·Ψ}` (**`call_class`**): `E = (D₀+2)·dGm` depends on the literals only, `c_W` on the gate's constants.

Paper quantity: the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.LocalBitMultitape NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.PrimAsm.C3Mach NearCubicWires.WireExponent3_5.PrimAsm.C3Field

/-- A polynomial envelope: preprocessing `n^A`. -/
def EGp (A : ℕ) : Envelope := ⟨0, 0, 0, 0, 0, 0, A, 0⟩

/-- The writer's envelope: preprocessing `2^{E·Ψ}`. -/
def EWc (E : ℕ) : Envelope := ⟨0, 0, 0, 0, 0, 0, 0, E⟩

theorem classBound_EGp (A n k psi : ℕ) : classBound (EGp A) .preprocessing n k psi = n ^ A := by
  simp [classBound, EGp]

theorem classBound_EWc (E n k psi : ℕ) : classBound (EWc E) .preprocessing n k psi = 2 ^ (E * psi) := by
  simp [classBound, EWc]

/-- The fill polynomial's degree: every writer's degree. -/
noncomputable def DvC : ℕ :=
  max PrimT.GeoPack.geoD (max PrimT.C4GateSym.gsD (PrimT.C4GateSym.gtD PrimAsm.ThrData.thrDataStage2))

/-- The size's degree in `n + 1`. -/
noncomputable def D0 : ℕ := max PrimT.GeoPack.dW (max DvC PrimT.FlipsPack.flipsD) + 1

end NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
