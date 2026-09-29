import Proof.Assembly.AppendOutputLength
import Proof.Circuits.DecompositionCachedChildPosition
import Proof.Circuits.DecompositionCountDrivers

/-! Exact common row scale from the measured native cache and its two
decoded dimensions. The fixed machine computes w=B+1 and
S=2*w+(n+1)*(N+1), the scale used by the actual cached coefficient bank. -/
namespace NearCubicWires.RepairOrdinary.RowCommonSize
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Store := Fin 17→List Bool
def put (a : Store) (i j : Fin 17) (x y : List Bool) : Store :=
  fun k=>if k=i then x else if k=j then y else a k
def input (B n N : ℕ) : Store := fun i=>
  if i=0 then List.replicate B true else if i=1 then UnaryTemplate.tape n
  else if i=2 then UnaryTemplate.tape N else []
def data1 (B n N : ℕ) := put (input B n N) 3 4
  (List.replicate (n+1) true) (List.replicate (n+2) false)
def data2 (B n N : ℕ) := put (data1 B n N) 5 6
  (List.replicate ((n+1)*N) true) (List.replicate (WilliamsUnaryProduct.scratch (n+1) N) false)
def data3 (B n N : ℕ) := put (data2 B n N) 7 8
  (List.replicate ((n+1)*N+(n+1)) true) (List.replicate ((n+1)*N+(n+1)+2) false)
def data4 (B n N : ℕ) := put (data3 B n N) 9 10 [true] [false]
def data5 (B n N : ℕ) := put (data4 B n N) 11 12
  (List.replicate (B+1) true) (List.replicate (B+1+2) false)
def data6 (B n N : ℕ) := put (data5 B n N) 13 14
  (List.replicate ((B+1)+((n+1)*N+(n+1))) true)
  (List.replicate ((B+1)+((n+1)*N+(n+1))+2) false)
def slots1 : Fin 3→Fin 17 := ![1,3,4]
def slots2 : Fin 4→Fin 17 := ![3,2,5,6]
def slots3 : Fin 4→Fin 17 := ![5,3,7,8]
def slots4 : Fin 2→Fin 17 := ![9,10]
def slots5 : Fin 4→Fin 17 := ![0,9,11,12]
def slots6 : Fin 4→Fin 17 := ![11,7,13,14]
noncomputable def phase1 := RecoveryFocus.machine slots1 (UWalkUnary.machine false true)
noncomputable def phase2 := RecoveryFocus.machine slots2 ClockUnaryProduct.machine
noncomputable def phase3 := RecoveryFocus.machine slots3 ClockUnarySum.machine
noncomputable def phase4 := RecoveryFocus.machine slots4 (HierarchyFixedWord.machine [true])
noncomputable def phase5 := RecoveryFocus.machine slots5 ClockUnarySum.machine
noncomputable def phase6 := RecoveryFocus.machine slots6 ClockUnarySum.machine
noncomputable def first := Composition.machine phase1 phase2
noncomputable def second := Composition.machine first phase3
noncomputable def third := Composition.machine second phase4
noncomputable def fourth := Composition.machine third phase5
noncomputable def fifth := Composition.machine fourth phase6

theorem focus_put {t s : ℕ} (p : Machine t s) (fuel : ℕ) (src dst : Fin t→List Bool)
    (h : ClockJoin.ReadyRun p fuel src dst) (slots : Fin t→Fin 17)
    (hs : Function.Injective slots) (a : Store) (i j : Fin t) (x y : List Bool)
    (hin : ∀ k,a (slots k)=src k)
    (hout : ∀ k,put a (slots i) (slots j) x y (slots k)=dst k) :
    ClockJoin.ReadyRun (RecoveryFocus.machine slots p) fuel a (put a (slots i) (slots j) x y) := by
  have hf:=h.focus slots hs a hin
  have he:=HierarchyWidth.install_eq slots hs a (put a (slots i) (slots j) x y) dst hout (by
    intro k hk
    simp [put,Ne.symm (hk i),Ne.symm (hk j)])
  rw [he] at hf
  exact hf


end NearCubicWires.RepairOrdinary.RowCommonSize
