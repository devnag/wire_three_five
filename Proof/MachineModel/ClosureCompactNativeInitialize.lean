import Proof.MachineModel.ClosureCompactMetadata

/-! Physically produce and distribute the compact metadata into the actual
native bank. Runtime dimensions, the encoded cache, raw source, and loop
counter are explicit inputs; they are not silently treated as outputs.
The extra workspace holds the arithmetic computation, outside the native
bank. All machines and slot maps are independent of runtime data. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactNativeInitialize
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtIncidence ExtDecompositionBatch
open RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding

def native (i : Fin 277) : Fin 440 := i.castAdd 163
def metadataSlots : Fin 162 → Fin 440 := ![278,3,4,15,282,283,88,0,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,27,307,308,309,31,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,53,332,333,334,57,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,86,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,133,425,135,427,428,429,139,431,141,433,143,435,436,146,438,439]
def ports : Fin 141 → Fin 440 := native ∘ NativeFanoutLayout.ports

def heads (pos : Nat) (out : List Bool) (i : Fin 440) : Nat :=
  if i=180 then out.length else if i=262 then pos else if i=277 then 1 else 0
def base (M : Nat) (source out : List Bool) (i : Fin 440) : List Bool :=
  if i=180 then out else if i=262 then source else if i=277 then CompareMachine.word M else []

variable {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs] (Q w : Nat)

noncomputable def input (M : Nat) (source out : List Bool) : Fin 440 → List Bool :=
  install metadataSlots (base M source out)
    (CompactMetadata.input (exactListWord gs).length n gs.length (P1Radix.bits gs)
      (P1Radix.effectiveDegree gs) Q w (exactListWord gs))
noncomputable def middle (M : Nat) (source out : List Bool) : Fin 440 → List Bool :=
  install metadataSlots (input gs Q w M source out)
    (CompactMetadata.output (exactListWord gs).length n gs.length (P1Radix.bits gs)
      (P1Radix.effectiveDegree gs) Q w (exactListWord gs))
noncomputable def output (M : Nat) (source out : List Bool) : Fin 440 → List Bool :=
  install ports (middle gs Q w M source out)
    (NativeFanout.output NativeFanoutLayout.choice (P1CompactNativeMaster.words gs Q w)
      (P1CompactNativeMeasured.capacity gs Q w))

noncomputable def first := RecoveryFocus.machine metadataSlots CompactMetadata.machine
noncomputable def last := RecoveryFocus.machine ports (NativeFanout.machine NativeFanoutLayout.choice)
noncomputable def machine := Composition.machine first last
def budget := CompactMetadata.budget (exactListWord gs).length n gs.length (P1Radix.bits gs)
  (P1Radix.effectiveDegree gs) Q w + 1 + (2*P1CompactNativeMeasured.capacity gs Q w+4)



end NearCubicWires.P1Closure.CompactNativeInitialize
