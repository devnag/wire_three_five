import Proof.Packets.NormalizerMaterializeData

/-! Fresh scratch input and the one executed initializer for normalization.
Only the source records, their actual count, and the width template are present. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizeCold
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding
open Normalize

def data (B : Nat) (raw : List (List Bool)) : Fin 24→List Bool := fun i=>
  if i=0 then SuffixScan.stream (records raw)
  else if i=3 then CompareMachine.word raw.length
  else if i=13 then UnaryTemplate.tape (2*B+3) else []

def boot : Machine 24 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=16 ∨ i=17 ∨ i=21 then some false else none,
      fun i=>if i=21 then .right else .stay⟩ else none


end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizeCold
