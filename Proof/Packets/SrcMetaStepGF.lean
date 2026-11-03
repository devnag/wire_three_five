import Proof.Packets.SrcMetaStep
import Proof.SourceAssembly.SourceFactorSelMetaVals

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceStart.MetaStepGF
open NearCubicWires.SourceSkeleton.InitS (MetaRun ResExt)
noncomputable section

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

def metaMG (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L u : ℕ) :=
  MetaStep.metaM pl hh (SourceFactorSel.MetaPipe.metaVals2 selector s p packets L) u

/-- Its cost. -/
def metaCostG (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L q : ℕ) : ℕ :=
  MetaStep.metaCost (SourceFactorSel.MetaPipe.metaVals2 selector s p packets L) q

/-- Its extension width. -/
def wMG (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L : ℕ) : ℕ :=
  191 + (SourceFactorSel.MetaPipe.metaVals2 selector s p packets L).NP

end
end NearCubicWires.SourceStart.MetaStepGF

