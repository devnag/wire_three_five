import Proof.MachineModel.ClosureRadix

/-! Produce the compact metadata scale from independently measured cache
bytes and radix. Reuses the first six existing arithmetic phases verbatim;
the final addition reads the separate radix word instead of the cache mass.
All parameters are runtime tape data; the machine is fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactSize
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch

def value (B n N b : Nat) := B+(n+1)*(N+1)+b+1
def middle (B n N b : Nat) : Fin 18 → List Bool :=
  Fin.addCases (m:=17) (n:=1) (motive:=fun _ => List Bool)
    (RowCommonSize.data6 B n N) (fun _ => List.replicate b true)
def slots : Fin 4 → Fin 18 := ![13,17,15,16]
def sumOutput (a b : Nat) : Fin 4 → List Bool :=
  ![List.replicate a true,List.replicate b true,List.replicate (a+b) true,List.replicate (a+b+2) false]
noncomputable def output (B n N b : Nat) : Fin 18 → List Bool :=
  install slots (middle B n N b)
    (sumOutput ((B+1)+((n+1)*N+(n+1))) b)
noncomputable def first := TapeEmbedding.machine 1 RowCommonSize.fifth
noncomputable def last := RecoveryFocus.machine slots ClockUnarySum.machine
noncomputable def machine := Composition.machine first last
def firstCost (B n N : Nat) :=
  (2*n+6)+1+WilliamsUnaryProduct.budget (n+1) N+
  1+(2*((n+1)*N+(n+1))+6)+1+4+1+(2*(B+1)+6)+
  1+(2*((B+1)+((n+1)*N+(n+1)))+6)
def budget (B n N b : Nat) := firstCost B n N+1+(2*value B n N b+6)

end NearCubicWires.P1Closure.CompactSize
