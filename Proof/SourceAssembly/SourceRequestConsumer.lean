import Proof.SourceAssembly.SLoadMaskReady
import Proof.SourceAssembly.SLoadPrepared
import Proof.SourceAssembly.SourceReuse

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

/-! ## 0. The request of one monomial -/

/-- The supplier request of one monomial of a site polynomial: its `≤ 4` atoms, in factor order,
duplicates kept, compiled to native circuits of the branch mode (`Packets.request`,
`fixed-live-packet-parent-20260921/PCJ9eff70d512234a4c_Packets.lean:91`). -/
def monomialRequest (L target : Nat) (mode : Bool) {q : Nat} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (atoms : List (C10TotalDecode.Atom pcpp))
    (four : atoms.length ≤ 4) : Request :=
  if mode then
    .sym ⟨q, atoms.map C10NaturalModeAtoms.nativeSymmetricAtom⟩
      (by simp only [List.length_map]; exact four) L target
  else
    .thr ⟨q, atoms.map C10NaturalModeAtoms.nativeThresholdAtom⟩
      (by simp only [List.length_map]; exact four) L target

/-! ## 1. The resident set at the prologue's exit -/

/-! ## 2. The seed conjunct -/

/-- The seed code: the loader's lead/suffix with the identity tail. -/
def seedCode {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} (packet : PacketWriter selector a)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hminj : Function.Injective maskSlots)
    (pslots : Fin packet.ordinary.program.tapeCount → Fin U) (hsinj : Function.Injective pslots)
    (slot : Fin 13 → Fin U) (ret : Fin 4 → Fin U) (retDrv log rawDrv rawDst rawLog : Fin U) :
    MaskSeedCode mask packet U :=
  PCJ6e421fabe2aa4155_SourceReuse.identityTail
    (SLoad.MaskReady.code mask packet maskSlots hminj pslots hsinj slot ret retDrv log
      rawDrv rawDst rawLog)

/-- The seed fuel: exactly the sum `Ready` asks for, tail fuel `0`. -/
def seedFuel (mask : MaskProducer) {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    (packet : PacketWriter selector a) (r : Request) : Nat :=
  (SLoad.LeadDriver.prefixFuel a r + 1 +
    (maskBudget mask.coefficient mask.degree (maskData a r) + 1 +
      SLoad.SuffixFrame.cost r.q r.nativeWord.length (r.supportWord a).length
        (r.indexWord a).length (r.topWord a).length)) + 1 +
    (packetBudget a packet.coefficient packet.degree r + 1 + 0)

section seed

end seed

/-! ## 3. At any zero padding (the refill's clear backing) -/

/-! ## 4. The setup conjunct -/

/-- A tape the seed loader and the cold run never touch. -/
def Outside {U tc w : Nat} (slot : Fin 13 → Fin U) (maskSlots : Fin (5 + w) → Fin U)
    (pslots : Fin tc → Fin U) (poolSlots : Fin 373 → Fin U) (x : Fin U) : Prop :=
  (∀ j, slot j ≠ x) ∧ (∀ i, maskSlots i ≠ x) ∧ (∀ j, pslots j ≠ x) ∧ (∀ i, poolSlots i ≠ x)


end
end NearCubicWires.SourceRequest
