import Proof.Supplier.RowCommonResources
import Proof.PCP.ProjectionDimensionTemplate
import Proof.Supplier.RowCommonBounds

/-! Construct exactly the existing outer row capacity from its paid raw
maximum occurrence count, common output width and native cache capacity.
The source D=256*S makes the multiplier64 reproduce the original16384. -/
namespace NearCubicWires.RepairOrdinary.RowCommonAllocation
open LocalBitMultitape RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Store := Fin 25→List Bool
def put (a : Store) (i j : Fin 25) (x y : List Bool) : Store :=
  fun k=>if k=i then x else if k=j then y else a k
def input (m p D : ℕ) : Store := fun i=>
  if i=0 then List.replicate m true else if i=1 then List.replicate p true
  else if i=2 then List.replicate D true else []
def value (m p D : ℕ) := ((m+1)*D)*64+p*16+64
def data1 (m p D : ℕ) := put (input m p D) 3 4
  (UnaryTemplate.tape D) (List.replicate (D+3) false)
def data2 (m p D : ℕ) := put (data1 m p D) 5 6
  ([true]) ([false])
def data3 (m p D : ℕ) := put (data2 m p D) 7 8
  (List.replicate (m+1) true) (List.replicate (m+1+2) false)
def data4 (m p D : ℕ) := put (data3 m p D) 9 10
  (List.replicate ((m+1)*D) true) (List.replicate (WilliamsUnaryProduct.scratch (m+1) D) false)
def data5 (m p D : ℕ) := put (data4 m p D) 11 12
  (UnaryTemplate.tape 64) (List.replicate 66 false)
def data6 (m p D : ℕ) := put (data5 m p D) 13 14
  (List.replicate (((m+1)*D)*64) true) (List.replicate (WilliamsUnaryProduct.scratch ((m+1)*D) 64) false)
def data7 (m p D : ℕ) := put (data6 m p D) 15 16
  (UnaryTemplate.tape 16) (List.replicate 18 false)
def data8 (m p D : ℕ) := put (data7 m p D) 17 18
  (List.replicate (p*16) true) (List.replicate (WilliamsUnaryProduct.scratch p 16) false)
def data9 (m p D : ℕ) := put (data8 m p D) 19 20
  (List.replicate (((m+1)*D)*64+p*16) true) (List.replicate (((m+1)*D)*64+p*16+2) false)
def data10 (m p D : ℕ) := put (data9 m p D) 21 22
  (List.replicate 64 true) (List.replicate 64 false)
def output (m p D : ℕ) := put (data10 m p D) 23 24
  (List.replicate (value m p D) true) (List.replicate (value m p D+2) false)
def slots1 : Fin 3→Fin 25 := ![2,3,4]
noncomputable def phase1 := RecoveryFocus.machine slots1 (DimensionTemplate.machine false)
def slots2 : Fin 2→Fin 25 := ![5,6]
noncomputable def phase2 := RecoveryFocus.machine slots2 (HierarchyFixedWord.machine [true])
def slots3 : Fin 4→Fin 25 := ![0,5,7,8]
noncomputable def phase3 := RecoveryFocus.machine slots3 (ClockUnarySum.machine)
def slots4 : Fin 4→Fin 25 := ![7,3,9,10]
noncomputable def phase4 := RecoveryFocus.machine slots4 (ClockUnaryProduct.machine)
def slots5 : Fin 2→Fin 25 := ![11,12]
noncomputable def phase5 := RecoveryFocus.machine slots5 (HierarchyFixedWord.machine (UnaryTemplate.tape 64))
def slots6 : Fin 4→Fin 25 := ![9,11,13,14]
noncomputable def phase6 := RecoveryFocus.machine slots6 (ClockUnaryProduct.machine)
def slots7 : Fin 2→Fin 25 := ![15,16]
noncomputable def phase7 := RecoveryFocus.machine slots7 (HierarchyFixedWord.machine (UnaryTemplate.tape 16))
def slots8 : Fin 4→Fin 25 := ![1,15,17,18]
noncomputable def phase8 := RecoveryFocus.machine slots8 (ClockUnaryProduct.machine)
def slots9 : Fin 4→Fin 25 := ![13,17,19,20]
noncomputable def phase9 := RecoveryFocus.machine slots9 (ClockUnarySum.machine)
def slots10 : Fin 2→Fin 25 := ![21,22]
noncomputable def phase10 := RecoveryFocus.machine slots10 (HierarchyFixedWord.machine (List.replicate 64 true))
def slots11 : Fin 4→Fin 25 := ![19,21,23,24]
noncomputable def phase11 := RecoveryFocus.machine slots11 (ClockUnarySum.machine)
noncomputable def joined1 := phase1
noncomputable def joined2 := Composition.machine joined1 phase2
noncomputable def joined3 := Composition.machine joined2 phase3
noncomputable def joined4 := Composition.machine joined3 phase4
noncomputable def joined5 := Composition.machine joined4 phase5
noncomputable def joined6 := Composition.machine joined5 phase6
noncomputable def joined7 := Composition.machine joined6 phase7
noncomputable def joined8 := Composition.machine joined7 phase8
noncomputable def joined9 := Composition.machine joined8 phase9
noncomputable def joined10 := Composition.machine joined9 phase10
noncomputable def machine := Composition.machine joined10 phase11
def budget (m p D : ℕ) := (2*D+8)+(4)+(2*(m+1)+6)+(WilliamsUnaryProduct.budget (m+1) D)+(134)+(WilliamsUnaryProduct.budget ((m+1)*D) 64)+(38)+(WilliamsUnaryProduct.budget p 16)+(2*(((m+1)*D)*64+p*16)+6)+(130)+(2*value m p D+6)+10




end NearCubicWires.RepairOrdinary.RowCommonAllocation
