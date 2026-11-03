import Proof.Assembly.SourceProduction

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJc4297ab269d8423a_Source
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairRepresentation SourceInterfaces SupplierPipeline SupplierEstimator
open RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-- Original occurrence supports, with multiplicity, and the actual live count. -/
structure MaskData where
  q : Nat
  m : Nat
  K : Nat
  support : Fin m → Finset (Fin q)
  bound : K ≤ q

def MaskData.supportWord (d : MaskData) : List Bool :=
  (List.ofFn (fun i : Fin d.m => RepairOrdinary.frame
    (List.ofFn (fun x : Fin d.q => decide (x ∈ d.support i))))).flatten

def MaskData.word (d : MaskData) : List Bool :=
  List.ofFn (fun x : Fin d.q => decide (x ∈ CyclicChoice.selectedLive d.support d.K))

/-- Only existing support frames and unary domain/count drivers enter.
In particular the q-bit output is not assumed resident. -/
def MaskData.input (work : Nat) (d : MaskData) : Fin (5+work) → List Bool := fun i =>
  if i.val=0 then d.supportWord else
  if i.val=1 then CompareMachine.word d.q else
  if i.val=2 then CompareMachine.word d.K else
  if i.val=3 then CompareMachine.word d.m else []

def maskBudget (coefficient degree : Nat) (d : MaskData) : Nat :=
  coefficient * (d.q+d.K+d.m+d.supportWord.length+1)^degree

/-- One ordinary program, chosen before every runtime input and every source
hierarchy parameter. Final private words are deliberately left unconstrained. -/
structure MaskProducer where
  work : Nat
  states : Nat
  machine : Machine (5+work) states
  coefficient : Nat
  degree : Nat
  positive : 0 < coefficient
  correct : ∀ d : MaskData, ∃ B : Fin (5+work) → List Bool,
    Step machine (maskBudget coefficient degree d) (fun _ => 0) (d.input work)
      (fun _ => 0) B ∧ B ⟨4,by omega⟩=d.word

def maskData (a : DecompositionAlgorithm) (r : Request) : MaskData where
  q := r.q
  m := (r.family a).occurrences.length
  K := normalizedLiveCount r.q r.liveScale
  support := occurrenceSupport (r.family a).occurrences
  bound := normalizedLiveCount_le r.q r.liveScale

/-- Specialize the actual source loader to a paid lead, the mask worker,
and a paid suffix. The later packet program and final join stay fixed. -/
structure MaskSeedCode (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} (packet : PacketWriter selector a) (U : Nat) where
  slots : Fin packet.ordinary.program.tapeCount → Fin U
  injective : Function.Injective slots
  maskSlots : Fin (5+mask.work) → Fin U
  maskInjective : Function.Injective maskSlots
  prefixStates : Nat
  lead : Machine U prefixStates
  suffixStates : Nat
  suffix : Machine U suffixStates
  tailStates : Nat
  tail : Machine U tailStates

def MaskSeedCode.base {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a} {U : Nat}
    (c : MaskSeedCode mask packet U) : SeedCode packet U where
  slots := c.slots
  injective := c.injective
  loadStates := _
  load := Composition.machine c.lead
    (Composition.machine (RecoveryFocus.machine c.maskSlots mask.machine) c.suffix)
  tailStates := c.tailStates
  tail := c.tail

def MaskSeedCode.Ready {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a} {U : Nat}
    (c : MaskSeedCode mask packet U) (r : Request) (fuel : Nat)
    (H H' : Fin U → Nat) (A A' : Fin U → List Bool) : Prop :=
  ∃ (maskReserve : Fin (5+mask.work) → Nat)
    (maskH : Fin U → Nat) (maskA : Fin U → List Bool)
    (reserve : Fin packet.ordinary.program.tapeCount → Nat)
    (ambientH : Fin U → Nat) (ambientA : Fin U → List Bool)
    (prefixFuel suffixFuel tailFuel : Nat),
  Step c.lead prefixFuel H A
    (dockH c.maskSlots maskH (fun _ => 0))
    (install c.maskSlots maskA (fun i => ZeroPadding.pad (maskReserve i)
      ((maskData a r).input mask.work i))) ∧
  (∀ B : Fin (5+mask.work) → List Bool,
    Step mask.machine (maskBudget mask.coefficient mask.degree (maskData a r))
      (fun _ => 0) ((maskData a r).input mask.work) (fun _ => 0) B →
    B ⟨4,by omega⟩=(maskData a r).word →
    Step c.suffix suffixFuel (dockH c.maskSlots maskH (fun _ => 0))
      (install c.maskSlots maskA (fun i => ZeroPadding.pad (maskReserve i) (B i)))
      (dockH c.slots ambientH (fun _ => 0))
      (install c.slots ambientA (fun i => ZeroPadding.pad (reserve i)
        (packet.ordinary.program.inputTapes (r.input a) i)))) ∧
  (∀ B : Fin packet.ordinary.program.tapeCount → List Bool,
    Step packet.ordinary.program.machine (packetBudget a packet.coefficient packet.degree r)
      (fun _ => 0) (packet.ordinary.program.inputTapes (r.input a)) (fun _ => 0) B →
    B packet.ordinary.program.outputTape=r.raw selector a →
    Step c.tail tailFuel (dockH c.slots ambientH (fun _ => 0))
      (install c.slots ambientA (fun i => ZeroPadding.pad (reserve i) (B i))) H' A') ∧
  (prefixFuel+1+(maskBudget mask.coefficient mask.degree (maskData a r)+1+suffixFuel))+1+
    (packetBudget a packet.coefficient packet.degree r+1+tailFuel) ≤ fuel

end
end PCJc4297ab269d8423a_Source
