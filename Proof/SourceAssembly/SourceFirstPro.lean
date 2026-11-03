import Proof.SourceAssembly.SourceFirst
import Proof.SourceAssembly.SourceRefillJoin

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

/-- **The loop-counter write.** -/
def counterM {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt eX pX gW) {V : Nat} (hV : d.U ≤ V)
    (cnt : Fin V) :=
  Composition.machine
    (RecoveryFocus.machine (![d.pcT e hV ⟨70, by unfold restPc; omega⟩, cnt, d.scr hV 11, d.scr hV 12] : Fin 4 → Fin V)
      RecoveryBoundedTapeCopy.machine)
    (DecompositionCountPosition.move (fun x : Fin V => if x = cnt then HeadMove.right else HeadMove.stay))

/-- **The first prologue's core.** ONE fixed machine. -/
def firstCore {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt2 se.extra sp.extra gW) {V : Nat} (hV : d.U ≤ V)
    {s7 : Nat} (g7M : Machine V s7) (cnt : Fin V) :=
  Composition.machine (Composition.machine g7M (backMachine se sp e.ext1 hV))
    (Composition.machine (refreshMachine e hV) (counterM e.ext1 hV cnt))

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

end concrete

end
end NearCubicWires.SourceConstruction.Rest
end
