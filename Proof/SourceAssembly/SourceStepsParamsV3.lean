import Proof.Packets.BudgetSeamScalars
import Proof.SourceAssembly.SourceStepsClassR
import Proof.Packets.SrcCapsPow2

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params NearCubicWires.Admission NearCubicWires.RuntimeShape
open NearCubicWires.SourceConstruction NearCubicWires.SourceSkeleton NearCubicWires.SourceSkeleton.ClassR
namespace NearCubicWires.SourceSkeleton.ClassV3
noncomputable section

/-! ## 1. The gauge v3 and `KFc3` -/

section gauge
variable (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)

def gE0v3 : ParNat := fun s g hg hh p =>
  gE0 selector mask packets rows s g hg hh p +
    (reqE s p + 1) * PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP s) + reqE s p

/-- **The gauge exponent v3.** -/
def gEv3 : ParNat := fun s g hg hh p => (gE0v3 selector mask packets rows s g hg hh p + 64)^3

def gC0v3 : ParNat := fun s g hg hh p =>
  gC0 selector packets s g hg hh p + PCPPQueryCachedBounds.coefficient (CloseoutLanguage.selectedPCPP s) + reqC s p

/-- **The gauge coefficient v3.** -/
def gCv3 : ParNat := fun s g hg hh p => (gC0v3 selector packets s g hg hh p + 2)^(gEv3 selector mask packets rows s g hg hh p)

end gauge

section site


end site

/-! ## 3. The seam's reserve premises at `siteR3` (rounded `Vv' = VvOf2`), and census H2 at the gauge v3 -/

section fits
variable (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (s : EightSources) (g : Real) (hg : 0 < g) (hh : g < 1/2) (p : Parameters s g) (k : Nat)

theorem workspace_mono (printer : WilliamsAlgorithm) {V W : Nat} (h : V ≤ W) :
    P1TopDownPaidReusableReserves.workspace printer V ≤ P1TopDownPaidReusableReserves.workspace printer W := by
  unfold P1TopDownPaidReusableReserves.workspace
  exact Nat.mul_le_mul_left _ (by omega)

theorem rewind_mono (printer : WilliamsAlgorithm) {V W : Nat} (h : V ≤ W) :
    P1TopDownPaidReusableReserves.rewind printer V ≤ P1TopDownPaidReusableReserves.rewind printer W := by
  unfold P1TopDownPaidReusableReserves.rewind
  exact Nat.mul_le_mul_left _ (by omega)

end fits

end
end NearCubicWires.SourceSkeleton.ClassV3
end

