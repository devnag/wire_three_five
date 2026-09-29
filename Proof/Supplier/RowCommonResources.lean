import Proof.Supplier.RowCommonSize
import Proof.Supplier.RowCachedCoordinateBounds

/-! Produce the exact two native-cache capacities from the measured radix
width and common source scale. Only fixed constants index these machines. -/
namespace NearCubicWires.RepairOrdinary.RowCommonResources
open LocalBitMultitape RecoveryRootRound
open RowCommonSize (put focus_put)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (w S : ℕ) : RowCommonSize.Store := fun i=>
  if i=0 then List.replicate w true else if i=1 then List.replicate S true else []
def data1 (w S : ℕ) := put (input w S) 2 3 [true] [false]
def data2 (w S : ℕ) := put (data1 w S) 4 5
  (List.replicate (w+1) true) (List.replicate (w+1+2) false)
def data3 (w S : ℕ) := put (data2 w S) 6 7 (UnaryTemplate.tape 32) (List.replicate 34 false)
def data4 (w S : ℕ) := put (data3 w S) 8 9
  (List.replicate ((w+1)*32) true) (List.replicate (WilliamsUnaryProduct.scratch (w+1) 32) false)
def data5 (w S : ℕ) := put (data4 w S) 10 11 (UnaryTemplate.tape 256) (List.replicate 258 false)
def output (w S : ℕ) := put (data5 w S) 12 13
  (List.replicate (S*256) true) (List.replicate (WilliamsUnaryProduct.scratch S 256) false)
def slots1 : Fin 2→Fin 17 := ![2,3]
def slots2 : Fin 4→Fin 17 := ![0,2,4,5]
def slots3 : Fin 2→Fin 17 := ![6,7]
def slots4 : Fin 4→Fin 17 := ![4,6,8,9]
def slots5 : Fin 2→Fin 17 := ![10,11]
def slots6 : Fin 4→Fin 17 := ![1,10,12,13]
noncomputable def phase1 := RecoveryFocus.machine slots1 (HierarchyFixedWord.machine [true])
noncomputable def phase2 := RecoveryFocus.machine slots2 ClockUnarySum.machine
noncomputable def phase3 := RecoveryFocus.machine slots3 (HierarchyFixedWord.machine (UnaryTemplate.tape 32))
noncomputable def phase4 := RecoveryFocus.machine slots4 ClockUnaryProduct.machine
noncomputable def phase5 := RecoveryFocus.machine slots5 (HierarchyFixedWord.machine (UnaryTemplate.tape 256))
noncomputable def phase6 := RecoveryFocus.machine slots6 ClockUnaryProduct.machine
noncomputable def first := Composition.machine phase1 phase2
noncomputable def second := Composition.machine first phase3
noncomputable def third := Composition.machine second phase4
noncomputable def fourth := Composition.machine third phase5
noncomputable def machine := Composition.machine fourth phase6
def budget (w S : ℕ) := 4+(2*(w+1)+6)+70+WilliamsUnaryProduct.budget (w+1) 32+
  518+WilliamsUnaryProduct.budget S 256+5

theorem literal_ready (bits : List Bool) : ClockJoin.ReadyRun (HierarchyFixedWord.machine bits)
    (2*bits.length+2) (fun _=>[]) ![bits,List.replicate bits.length false] := by
  obtain ⟨r,hr,rt,rh,rs⟩:=HierarchyFixedWord.word_ready bits
  exact ⟨r,hr,rt,rh,rs.le⟩
theorem product_ready (d e : ℕ) : ClockJoin.ReadyRun ClockUnaryProduct.machine
    (WilliamsUnaryProduct.budget d e) (WilliamsUnaryProduct.input d e) (WilliamsUnaryProduct.output d e) := by
  obtain ⟨r,hr,rt,rh,rs⟩:=WilliamsUnaryProduct.product_ready d e
  exact ⟨r,hr,rt,rh,rs.le⟩



end NearCubicWires.RepairOrdinary.RowCommonResources
