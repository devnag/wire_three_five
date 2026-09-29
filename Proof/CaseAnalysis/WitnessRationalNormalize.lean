import Proof.CaseAnalysis.WitnessRational

/-! Actual coefficient fields are normalized at the produced policy width.
The single pre-gcd flag checks canonical framing, integer/natural validity,
positive denominator, and both original payload lengths. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RationalNormalize
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 539) : Fin 552:=i.castAdd 13
def leftSlots : Fin 5→Fin 552:=![539,343,540,541,542]
def rightSlots : Fin 5→Fin 552:=![539,535,543,544,545]
def kindSlots : Fin 6→Fin 552:=![535,546,547,548,549,550]
noncomputable def cold:=RecoveryFocus.machine old RationalCold.machine
noncomputable def left:=RecoveryFocus.machine leftSlots ClockNormalize.machine
noncomputable def right:=RecoveryFocus.machine rightSlots ClockNormalize.machine
noncomputable def kind:=RecoveryFocus.machine kindSlots CompetitorWitnessKind.machine
def finish : Machine 552 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q scan=>if q.val=0 then
    some ⟨1,fun i=>if i=551 then some (scan 148 && scan 360 && scan 536 && !scan 546 && scan 541 && scan 544)
      else none,fun _=>.stay⟩ else none
noncomputable def first:=Composition.machine cold left
noncomputable def second:=Composition.machine first right
noncomputable def third:=Composition.machine second kind
noncomputable def machine:=Composition.machine third finish


end NearCubicWires.RepairOrdinary.CloseoutWitness.RationalNormalize
