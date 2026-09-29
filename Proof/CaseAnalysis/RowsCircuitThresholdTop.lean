import Proof.CaseAnalysis.RowsCircuitLayout

/-! Complete threshold top check and retained-field publication. The same
checked gate trace supplies the support bitmap and compressed request. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdTop
open LocalBitMultitape RecoveryRootRound RadixSemantics CanonicalWitnessCodec SupplierPipeline
open CloseoutRowsGatePairHeads CloseoutRowsCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def external : Fin 7→Fin 1703:=![1694,1695,1701,1692,1702,1689,1696]
def externalData (cap : ℕ) : Fin 7→List Bool:=
  ![List.replicate cap true,List.replicate (cap+1) false,List.replicate cap false,
    List.replicate cap false,List.replicate cap false,[],List.replicate cap false]
def sources (cap : ℕ) (bank : Fin 1049→List Bool) : Fin 3→List Bool:=
  ![CloseoutRowsGateBank.padded cap bank 1033,CloseoutRowsGateBank.padded cap bank 994,
    CloseoutRowsGateBank.padded cap bank 1047]
noncomputable def middle (cap : ℕ) (input : Fin 1703→List Bool) (bank : Fin 1049→List Bool):=
  install gateSlots input (CloseoutRowsGateBank.padded cap bank)
def weights {core : ℕ} (g : SupportedNormalizedGate core):=
  ((List.ofFn g.gate.weight).flatMap RepairRepresentation.intWord).length
def theta {core : ℕ} (g : SupportedNormalizedGate core):=
  (RepairRepresentation.natWord g.gate.threshold.natAbs).length
noncomputable def output {core : ℕ} (cap : ℕ) (input : Fin 1703→List Bool) (bank : Fin 1049→List Bool)
    (g : SupportedNormalizedGate core):=
  install topPublishSlots (middle cap input bank)
    (CloseoutRowsCircuitTopPublish.output cap (weights g) (theta g) (sources cap bank))
noncomputable def parser:=RecoveryFocus.machine gateSlots (CloseoutRowsGateMeasured.machine true)
noncomputable def publish:=RecoveryFocus.machine topPublishSlots CloseoutRowsCircuitTopPublish.machine
noncomputable def machine:=CloseoutRowsGateColdPair.machine parser publish (fun b=>b 1676)
def budget (cap : ℕ) (bits : List Bool):=CloseoutRowsGateMeasured.budget bits+8*cap+22

theorem external_outside (i : Fin 7) : ∀ j,gateSlots j≠external i:=by
  have high:1688 ≤ (external i).val:=by fin_cases i <;> decide
  intro j he
  have hv:=congrArg (fun k : Fin 1703=>k.val) he
  rw [gate_val] at hv
  split_ifs at hv <;> omega

theorem publish_input {core : ℕ} (cap : ℕ) (bits : List Bool) (bank : Fin 1049→List Bool)
    (g : SupportedNormalizedGate core) (hg : decodeSupportedNormalizedGate core (value bits)=some g)
    (meaning : CloseoutRowsGateMeasured.Output true core bits bank)
    (A : Fin 1703→List Bool) (he : ∀ i,A (external i)=externalData cap i) :
    ∀ i,middle cap A bank (topPublishSlots i)=
      CloseoutRowsCircuitTopPublish.bank cap (weights g) (theta g) (sources cap bank) 0 i:=by
  obtain ⟨_native,hw,ht,_support⟩:=meaning.2.2 g hg
  have gate (j : Fin 1049):middle cap A bank (gateSlots j)=CloseoutRowsGateBank.padded cap bank j:=
    install_slot gateSlots gate_injective _ _ j
  have ext (j : Fin 7):middle cap A bank (external j)=externalData cap j:=
    (install_other _ _ _ _ (external_outside j)).trans (he j)
  intro i;fin_cases i
  · exact gate 1033
  · exact gate 994
  · change middle cap A bank (gateSlots 1041)=_
    rw [gate];change ZeroPadding.pad cap (bank 1041)=_
    change bank 1041=_ at hw;rw [hw];rfl
  · change middle cap A bank (gateSlots 1045)=_
    rw [gate];change ZeroPadding.pad cap (bank 1045)=_
    change bank 1045=_ at ht;rw [ht];rfl
  · exact gate 1047
  · exact ext 0
  · exact ext 1
  · exact ext 2
  · exact ext 3
  · exact ext 4
  · exact ext 5
  · exact ext 6

theorem publish_heads (H : Fin 1703→ℕ)
    (hg : ∀ j,H (gateSlots j)=CloseoutRowsGateMeasured.heads j)
    (he : ∀ j,H (external j)=0) : ∀ i,H (topPublishSlots i)=0:=by
  intro i;fin_cases i
  · exact hg 1033
  · exact hg 994
  · exact hg 1041
  · exact hg 1045
  · exact hg 1047
  · exact he 0
  · exact he 1
  · exact he 2
  · exact he 3
  · exact he 4
  · exact he 5
  · exact he 6

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdTop
