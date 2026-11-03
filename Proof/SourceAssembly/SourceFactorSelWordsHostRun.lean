import Proof.SourceAssembly.SourceFactorSelWordsHostRes

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.WordsHost
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
open NearCubicWires.SourceFactorSel.Words
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

section host
variable {mask : MaskProducer} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
  {packet : PacketWriter selector a} {rows : RowProducer selector a printer} {V : Nat}

/-- Every shared host value stays below the high residents' end. -/
theorem HostLay.hostV_lt (L : HostLay mask packet rows V) (N : Nat) (hN : L.wB + (N - 29) ≤ L.B + 43 + L.Pc)
    (hVB : L.B + 48 + L.Pc ≤ V) : ∀ p, 6 ≤ p → p < N → hostV L.P0 mask.work L.tc L.B L.Pc L.wB p < V := by
  intro p h6 hp
  have hc := hostV_cases L.P0 mask.work L.tc L.B L.Pc L.wB p h6
  have := L.hgB; have := L.hwB
  simp only [HostLay.B, HostLay.P0, HostLay.tc] at *
  omega

/-- **The words stage on the host.** -/
def wordsHostM (L : HostLay mask packet rows V) {k : Nat} (SB : Item4.StartBank a k) (src : Fin 6 → Fin V)
    (hV : ∀ p, 6 ≤ p → p < nW mask.work (Cold.tapes a) k → hostV L.P0 mask.work L.tc L.B L.Pc L.wB p < V) :=
  RecoveryFocus.machine (L.dock src (nW mask.work (Cold.tapes a) k) hV) (Words.wordsLoc mask SB)

end host

end
end NearCubicWires.SourceFactorSel.WordsHost

