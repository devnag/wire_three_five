import Proof.SourceAssembly.SourceRefillLoop

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
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-- The cycle's fuel for a prologue of cost `n` (the fuel of `SourceCyclePad.cycle_prepared_pad`, verbatim). -/
def cycFuel (mask : MaskProducer) {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (caps : RowCaps) (M2 U0 S Rw B v n : Nat) : Nat :=
  (n + 1 + SourceRequest.seedFuel mask packet r) + 1 +
    (BinaryCacheColdRun.budget (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) + 1 +
      (SLoad.Setup.cost (r.input a).length
          (SLoad.Setup.metaBits layout.w layout.degree layout.C caps).length + 1 +
        rowInitBudget a rows.coefficient rows.degree r layout.w layout.degree layout.C caps)) + 1 +
    (PCJ38fbfed565f64139_Family.budget printer (r.family a) (rows.state r layout facts caps) +
      1 + (2 * caps.descriptorReserve + 2 + 1 +
        (RowWidth.cost (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length
            M2 U0 (dataList a (r.family a) (geometryOf selector a r) layout facts).length + 1 +
          initFuel printer ⟨S, Rw, B,
            RowWidth.rw M2 U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length,
            v, (dataList a (r.family a) (geometryOf selector a r) layout facts).length⟩)))

/-- `rest`'s cost at loop point `j` (the cost of `SourceRestMain.rest_run`, verbatim). -/
def restCost {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    (g7cost : Nat → Nat) (rq : Request) (Rc w q gsLen Mb Ms j : Nat) : Nat :=
  cursorCost j + 1 + (g7cost (j+1) + 1 + backCost se sp rq Rc w q gsLen Mb Ms)

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
