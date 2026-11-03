import Proof.SourceAssembly.SourcePoolSeedShape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePoolSeedFanout
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
noncomputable section

def masters {q : Nat} (live : Finset (Fin q)) (w : Nat) : Fin 5→List Bool:=
  ![List.replicate w true,RepairOrdinary.frame (SignedSortKey.binary w 0),
    CloseoutRowsGateSupport.gateMembers live,List.replicate (ConstantGateReusable.C w) true,
    CompareMachine.word q]
def select (i : Fin 64) : Option (Fin 5):=
  if i=9 then some 0 else if i=13 ∨ i=14 then some 1 else
  if i=39 ∨ i=45 then some 2 else if i=40 then some 3 else
  if i=42 ∨ i=46 then some 4 else none

theorem pad_pad (C D : Nat) (bits : List Bool) (h:C≤D) :
    ZeroPadding.pad D (ZeroPadding.pad C bits)=ZeroPadding.pad D bits := by
  simp only [ZeroPadding.pad,List.length_append,List.length_replicate,List.append_assoc]
  rw [←List.replicate_add]
  congr 2
  omega

theorem padded_table {q : Nat} (live : Finset (Fin q)) (B w P : Nat)
    (hc:ConstantGateReusable.C w+1≤P) (he:ConstantGateReusable.E B q≤P)
    (hl:PoolEntry.logCapacity B q≤P) (i : Fin 64) :
    ZeroPadding.pad P (PCJ6e421fabe2aa4155_SourcePoolSeedShape.table live B w i)=
    ZeroPadding.pad P (NativeFanout.word select (masters live w) i) := by
  fin_cases i <;> first | rfl | exact pad_pad _ _ _ (by omega) |
    exact (pad_replicate_false _ _ (by omega))

theorem scalar_bounds (B q : Nat) :
    ConstantGateReusable.C (B+q+1)+1≤PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q ∧
    ConstantGateReusable.E B q≤PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q ∧
    PoolEntry.logCapacity B q≤PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q := by
  have hw:1≤B+q+1:=by omega
  have h2:B+q+1≤(B+q+1)^2:=by nlinarith
  have h3:(B+q+1)^2≤(B+q+1)^3:=by
    have h:=Nat.mul_le_mul_right ((B+q+1)^2) hw
    simpa only [one_mul,pow_succ,Nat.mul_comm] using h
  unfold ConstantGateReusable.C ConstantGateReusable.E PoolEntry.logCapacity
    PCJ6e421fabe2aa4155_SourcePoolCapacity.value
  constructor
  · nlinarith
  constructor <;>nlinarith

end
end PCJ6e421fabe2aa4155_SourcePoolSeedFanout
