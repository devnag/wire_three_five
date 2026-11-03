import Proof.Packets.SrcInitFit
import Proof.SourceAssembly.SourceStepsParamsV4

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params NearCubicWires.Admission NearCubicWires.RuntimeShape
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun NearCubicWires.SourceSkeleton
namespace NearCubicWires.SourceStart.InitFitV4
noncomputable section

/-- **Census H7 at `IKc4`.** -/
theorem H7_IKc4 (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (s : EightSources) (g : Real) (hg : 0 < g) (hh : g < 1/2) (p : Parameters s g)
    {d : Dims} {eX pX gW X T : ℕ}
    (pl : Place d eX pX gW (ClassV4.hRx4 selector mask packets rows s g hg hh p) (hVN selector s g hg hh p) X T)
    (L : ℕ) (mode : Bool) (target : ℕ) :
    ∃ q0, ∀ q, q0 ≤ q → ∀ b, b ≤ (C10PartsSchedule.thresholdFloor s + 1)*(q+1)^rB s g hg hh p →
      InitS.initAllXCostE pl L 1 (cVcN selector s g hg hh p) (SourceSkeleton.Params.sC s g hg hh p)
          (SourceSkeleton.Params.rC s g hg hh p) (SourceSkeleton.Params.pE s g hg hh p) (SourceSkeleton.Params.pC s g hg hh p) 3 1
          (SourceSkeleton.Params.ldE s g hg hh p) (SourceSkeleton.Params.ldC s g hg hh p) mode target q b
          (SourceSkeleton.Params.dE s g hg hh p) (SourceSkeleton.Params.dC s g hg hh p)
          (SourceSkeleton.Params.cwE s g hg hh p) (SourceSkeleton.Params.cwC s g hg hh p)
          (SourceStart.MetaStepGF.metaCostG selector s p packets L q) + 2 ≤
        (ClassV4.IKc4 selector mask packets rows s g hg hh p L).iT *
            tableClass L (ClassV4.hRx4 selector mask packets rows s g hg hh p + 1) q +
          (ClassV4.IKc4 selector mask packets rows s g hg hh p L).iP * (q+1)^(ClassV4.IKc4 selector mask packets rows s g hg hh p 0).iE := by
  have hge := ClassV4.hRx4_ge selector mask packets rows s g hg hh p
  have hld := SourceSkeleton.Params.ldC_ge s g hg hh p
  obtain ⟨q0, h0⟩ := SourceStart.InitFit.initX_fitG selector s p packets pl hge.1 (by omega) L (cVcN selector s g hg hh p)
    (SourceSkeleton.Params.sC s g hg hh p) (SourceSkeleton.Params.rC s g hg hh p) (SourceSkeleton.Params.pE s g hg hh p)
    (SourceSkeleton.Params.pC s g hg hh p) 3 1 (SourceSkeleton.Params.ldE s g hg hh p) (SourceSkeleton.Params.ldC s g hg hh p)
    (by omega) mode target (SourceSkeleton.Params.dE s g hg hh p) (SourceSkeleton.Params.dC s g hg hh p)
    (SourceSkeleton.Params.cwE s g hg hh p) (SourceSkeleton.Params.cwC s g hg hh p)
    (fun q => (C10PartsSchedule.thresholdFloor s + 1)*(q+1)^rB s g hg hh p) (SourceStart.MetaCost.pb_cpow _ _)
  exact ⟨q0, fun q hq b hb => (h0 q hq b hb).trans (Nat.le_add_right _ _)⟩

end
end NearCubicWires.SourceStart.InitFitV4

