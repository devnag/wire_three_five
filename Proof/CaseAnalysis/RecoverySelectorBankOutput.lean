import Proof.CaseAnalysis.RecoverySelectorBudget

/-! The complete selector returns a reusable bank. This identifies every
original scalar and scratch tape; only the consumed outer stack has a
bounded false suffix before the already paid padding is applied. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorFinish
open LocalBitMultitape SourceInterfaces RepairRepresentation
open RecoveryBoundedSelectorLoop RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def foldPickData : Fin 43→Option (Fin 35):=![some 0,none,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,none,some 32,some 33,none,none,some 1,none,none,none,some 31,none,some 34]
theorem fold_pick (i : Fin 43) : RecoveryFocus.pick foldSlots i=foldPickData i := by
  fin_cases i
  · change RecoveryFocus.pick foldSlots (0 : Fin 43)=some (0 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 0
  · change RecoveryFocus.pick foldSlots (1 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(1 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (2 : Fin 43)=some (2 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 2
  · change RecoveryFocus.pick foldSlots (3 : Fin 43)=some (3 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 3
  · change RecoveryFocus.pick foldSlots (4 : Fin 43)=some (4 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 4
  · change RecoveryFocus.pick foldSlots (5 : Fin 43)=some (5 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 5
  · change RecoveryFocus.pick foldSlots (6 : Fin 43)=some (6 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 6
  · change RecoveryFocus.pick foldSlots (7 : Fin 43)=some (7 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 7
  · change RecoveryFocus.pick foldSlots (8 : Fin 43)=some (8 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 8
  · change RecoveryFocus.pick foldSlots (9 : Fin 43)=some (9 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 9
  · change RecoveryFocus.pick foldSlots (10 : Fin 43)=some (10 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 10
  · change RecoveryFocus.pick foldSlots (11 : Fin 43)=some (11 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 11
  · change RecoveryFocus.pick foldSlots (12 : Fin 43)=some (12 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 12
  · change RecoveryFocus.pick foldSlots (13 : Fin 43)=some (13 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 13
  · change RecoveryFocus.pick foldSlots (14 : Fin 43)=some (14 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 14
  · change RecoveryFocus.pick foldSlots (15 : Fin 43)=some (15 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 15
  · change RecoveryFocus.pick foldSlots (16 : Fin 43)=some (16 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 16
  · change RecoveryFocus.pick foldSlots (17 : Fin 43)=some (17 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 17
  · change RecoveryFocus.pick foldSlots (18 : Fin 43)=some (18 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 18
  · change RecoveryFocus.pick foldSlots (19 : Fin 43)=some (19 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 19
  · change RecoveryFocus.pick foldSlots (20 : Fin 43)=some (20 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 20
  · change RecoveryFocus.pick foldSlots (21 : Fin 43)=some (21 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 21
  · change RecoveryFocus.pick foldSlots (22 : Fin 43)=some (22 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 22
  · change RecoveryFocus.pick foldSlots (23 : Fin 43)=some (23 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 23
  · change RecoveryFocus.pick foldSlots (24 : Fin 43)=some (24 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 24
  · change RecoveryFocus.pick foldSlots (25 : Fin 43)=some (25 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 25
  · change RecoveryFocus.pick foldSlots (26 : Fin 43)=some (26 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 26
  · change RecoveryFocus.pick foldSlots (27 : Fin 43)=some (27 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 27
  · change RecoveryFocus.pick foldSlots (28 : Fin 43)=some (28 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 28
  · change RecoveryFocus.pick foldSlots (29 : Fin 43)=some (29 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 29
  · change RecoveryFocus.pick foldSlots (30 : Fin 43)=some (30 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 30
  · change RecoveryFocus.pick foldSlots (31 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(31 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (32 : Fin 43)=some (32 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 32
  · change RecoveryFocus.pick foldSlots (33 : Fin 43)=some (33 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 33
  · change RecoveryFocus.pick foldSlots (34 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(34 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (35 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(35 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (36 : Fin 43)=some (1 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 1
  · change RecoveryFocus.pick foldSlots (37 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(37 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (38 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(38 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (39 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(39 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (40 : Fin 43)=some (31 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 31
  · change RecoveryFocus.pick foldSlots (41 : Fin 43)=none
    simp only [RecoveryFocus.pick,dif_neg (by decide : ¬∃ j,foldSlots j=(41 : Fin 43))]
  · change RecoveryFocus.pick foldSlots (42 : Fin 43)=some (34 : Fin 35)
    exact RecoveryFocus.pick_slot foldSlots fold_injective 34

def folded (base : ℕ) (out : List Bool) (refs : List ℕ):=
  RecoveryBoundedNativeFoldLoop.State.iterate false refs.reverse ⟨base,0,0,out⟩

theorem fold_output_heads (base C total : ℕ) (out pre : List Bool) (refs : List ℕ) :
    (foldOutput base C total out pre refs).heads=
      Fin.addCases (m:=34) (n:=1) (motive:=fun _=>ℕ)
        (RecoveryBoundedNativeFold.heads (folded base out refs).out pre.length) (fun _=>1) := by
  change (Fin.addCases (m:=34) (n:=1) (motive:=fun _=>ℕ)
    (RecoveryBoundedNativeFold.heads (folded base out refs).out
      (pre++RecoveryBoundedNativeUnaryLoop.stackWords ([] : List ℕ).reverse).length) (fun _=>1))=_
  simp only [List.reverse_nil,RecoveryBoundedNativeUnaryLoop.stackWords,List.flatMap_nil,List.append_nil]

theorem fold_output_data (base C total : ℕ) (out pre : List Bool) (refs : List ℕ) :
    (foldOutput base C total out pre refs).tapes=
      fun j=>ZeroPadding.pad (foldCaps C j)
        (Fin.addCases (m:=34) (n:=1) (motive:=fun _=>List Bool)
          (RecoveryBoundedNativeFold.data 0 (folded base out refs).acc C false (folded base out refs).out
            (pre++List.replicate (folded base out refs).erased false) [])
          (fun _=>CompareMachine.word total) j) := by
  change (fun j=>ZeroPadding.pad (foldCaps C j)
    (Fin.addCases (m:=34) (n:=1) (motive:=fun _=>List Bool)
      (RecoveryBoundedNativeFold.data 0 (folded base out refs).acc C false (folded base out refs).out
        (pre++RecoveryBoundedNativeUnaryLoop.stackWords ([] : List ℕ).reverse++
          List.replicate (folded base out refs).erased false) [])
      (fun _=>CompareMachine.word total) j))=_
  simp only [List.reverse_nil,RecoveryBoundedNativeUnaryLoop.stackWords,List.flatMap_nil,List.append_nil]

def afterData (index base C D value limit total erased : ℕ) (out source pre : List Bool) (i : Fin 43) :=
  if i=40 then pre++List.replicate erased false else data index base C D value limit total out source pre i

section
end

theorem endBank_heads (index base C D value limit total pos : ℕ) (out source pre : List Bool) (refs : List ℕ) :
    (endBank index base C D value limit total pos out source pre refs).heads=
      heads (folded base out refs).out pre pos := by
  simp only [endBank,RecoveryFocus.config,fold_pick,fold_output_heads]
  funext i
  fin_cases i
  all_goals first | (change (0 : ℕ)=0; rfl) | (change (1 : ℕ)=1; rfl) |
    (change (pos : ℕ)=pos; rfl) |
    (change (folded base out refs).out.length=(folded base out refs).out.length; rfl) |
    (change pre.length=pre.length; rfl)

theorem endBank_tapes (index base C D value limit total pos : ℕ) (out source pre : List Bool) (refs : List ℕ)
    (hC : 1 ≤ C) :
    (endBank index base C D value limit total pos out source pre refs).tapes=
      afterData index (folded base out refs).acc C D value limit total (folded base out refs).erased
        (folded base out refs).out source pre := by
  simp only [endBank,RecoveryFocus.config,fold_pick,fold_output_data]
  funext i
  fin_cases i
  all_goals first | rfl | exact ZeroPadding.pad_zero _ | exact pad_false C hC

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorFinish
