import Proof.CaseAnalysis.FinalAppendPositioning
import Proof.PCP.PCPSerializerCapacityPower
import Proof.CaseAnalysis.FinalSelectorLoadMasks
import Proof.Hierarchy.HierarchyFixedWord
import Proof.CaseAnalysis.FinalPartsSchedule
import Proof.CaseAnalysis.FinalSeedEngine
import Proof.CaseAnalysis.FinalSupplierCountStage

/-! Initialize the append workspace once from the actual public raw width.

No clause/fold width is substituted. The selected schedule has callCount <=
entryWidth, so the quadratic capacity below pays the previously checked seek
and rewind. All operands are written by existing unary machines, from one raw
width tape and a fixed fresh band; their intermediate scratch is retained.
-/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10AppendWorkspaceInit

open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
open RepairSource.ProjectionNormalization CloseoutFinalSelector

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (b : ℕ) := 127 * (b + 1) ^ 2

def input (b : ℕ) : Fin 42 → List Bool := fun i => if i.val = 0 then List.replicate b true else []
def linearSlots (i : Fin 16) : Fin 42 := i.castAdd 26
def constantSlots : Fin 2 → Fin 42 := ![16, 17]
def sumSlots : Fin 4 → Fin 42 := ![5, 16, 18, 19]
def templateSlots : Fin 3 → Fin 42 := ![18, 20, 21]
def capacitySlots (i : Fin 18) : Fin 42 :=
  if i.val = 0 then 0 else ⟨21 + i.val, by omega⟩
def padSlots : Fin 4 → Fin 42 := ![39, 40, 28, 41]

theorem linearSlots_injective : Function.Injective linearSlots := by
  intro i j h
  have hv := congrArg Fin.val h
  exact Fin.ext hv
theorem capacitySlots_injective : Function.Injective capacitySlots := by decide

noncomputable def linear := RecoveryFocus.machine linearSlots (PCPSerializerCapacity.Power.machine 1 20)
noncomputable def constant := RecoveryFocus.machine constantSlots (HierarchyFixedWord.machine [true, true])
noncomputable def sum := RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def template := RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
noncomputable def power := RecoveryFocus.machine capacitySlots (PCPSerializerCapacity.Power.machine 2 127)
noncomputable def pad := RecoveryFocus.machine padSlots (CloseoutRowsEstimator.Pad.machine 2)
noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine linear constant) sum)
    template) power) pad

def budget (b : ℕ) := PCPSerializerCapacity.Power.budget 1 20 b + 1 + 6 + 1 +
  (2 * (20 * (b + 1) + 2) + 6) + 1 + (2 * (20 * b + 22) + 8) + 1 +
  PCPSerializerCapacity.Power.budget 2 127 b + 1 + (2 * capacity b + 4)

theorem budget_eq (b : ℕ) : budget b = 762 * b ^ 2 + 2958 * b + 3448 := by
  simp only [budget, PCPSerializerCapacity.Power.budget, DimensionPower.cost,
    WilliamsUnaryProduct.budget, capacity, pow_zero, pow_one]
  ring

/-- Actual initializer run: only the width is present initially. The template
and both reusable logs are outputs, not local hypotheses. -/
theorem initialize_run (b : ℕ) : ∃ out : Fin 42 → List Bool,
    Step machine (budget b) (fun _ => 0) (input b) (fun _ => 0) out ∧
    out 0 = List.replicate b true ∧
    out 20 = UnaryTemplate.tape (20 * b + 22) ∧
    out 39 = List.replicate (capacity b) false ∧
    out 40 = List.replicate (capacity b) false := by
  obtain ⟨p, hp, hp0, hp5⟩ := PCPSerializerCapacity.Power.capacity_run 1 20 b
  have first := dock_ready _ linearSlots linearSlots_injective (input b) _ _
    (step_of_clock hp) (by intro i; rfl)
  let a := install linearSlots (input b) p
  have freshA (i : Fin 42) (hi : 16 ≤ i.val) : a i = [] := by
    rw [show a i = install linearSlots (input b) p i from rfl,
      install_other _ _ _ _ (by
        intro j h; have hv := congrArg Fin.val h
        change j.val = i.val at hv; omega)]
    simp [input, show i.val ≠ 0 by omega]
  have a0 : a 0 = List.replicate b true :=
    (install_slot linearSlots linearSlots_injective _ _ 0).trans hp0
  have a5 : a 5 = List.replicate (20 * (b + 1)) true := by
    change install linearSlots (input b) p (linearSlots 5) = _
    simpa only [pow_one] using
      (install_slot linearSlots linearSlots_injective _ _ 5).trans hp5
  have second := dock_ready _ constantSlots (by decide) a _ _
    (Step.of_ready (HierarchyFixedWord.word_ready [true, true])) (by
      intro i; fin_cases i <;> exact freshA _ (by decide))
  let c := install constantSlots a (![([true, true] : List Bool), [false, false]])
  have third := dock_ready _ sumSlots (by decide) c _ _
    (step_of_clock (ClockUnarySum.sum_ready (20 * (b + 1)) 2)) (by
      intro i; fin_cases i
      · exact (install_other constantSlots _ _ _ (by decide)).trans a5
      · exact install_slot constantSlots (by decide) _ _ 0
      all_goals exact (install_other constantSlots _ _ _ (by decide)).trans (freshA _ (by decide)))
  let d := install sumSlots c
    (![List.replicate (20 * (b + 1)) true, List.replicate 2 true,
      List.replicate (20 * (b + 1) + 2) true, List.replicate (20 * (b + 1) + 2 + 2) false])
  have hwidth : 20 * (b + 1) + 2 = 20 * b + 22 := by omega
  have fourth := dock_ready _ templateSlots (by decide) d _ _
    (step_of_clock (DimensionTemplate.ready false (20 * b + 22))) (by
      intro i; fin_cases i
      · change d 18 = List.replicate (20 * b + 22) true
        rw [show d 18 = install sumSlots c _ (sumSlots 2) from rfl,
          install_slot _ (by decide), hwidth]
        rfl
      all_goals
        exact (install_other sumSlots _ _ _ (by decide)).trans
          ((install_other constantSlots _ _ _ (by decide)).trans (freshA _ (by decide))))
  let e := install templateSlots d (DimensionTemplate.output false (20 * b + 22))
  have e0 : e 0 = List.replicate b true :=
    (install_other templateSlots _ _ _ (by decide)).trans
      ((install_other sumSlots _ _ _ (by decide)).trans
        ((install_other constantSlots _ _ _ (by decide)).trans a0))
  have freshE (i : Fin 42) (hi : 22 ≤ i.val) : e i = [] := by
    have ht : ∀ j, templateSlots j ≠ i := by
      intro j hj; have hv := congrArg Fin.val hj
      fin_cases j <;> simp [templateSlots] at hv <;> omega
    have hs : ∀ j, sumSlots j ≠ i := by
      intro j hj; have hv := congrArg Fin.val hj
      fin_cases j <;> simp [sumSlots] at hv <;> omega
    have hc : ∀ j, constantSlots j ≠ i := by
      intro j hj; have hv := congrArg Fin.val hj
      fin_cases j <;> simp [constantSlots] at hv <;> omega
    exact (install_other templateSlots _ _ _ ht).trans
      ((install_other sumSlots _ _ _ hs).trans
        ((install_other constantSlots _ _ _ hc).trans (freshA _ (by omega))))
  obtain ⟨q, hq, hq0, hq7⟩ := PCPSerializerCapacity.Power.capacity_run 2 127 b
  have fifth := dock_ready _ capacitySlots capacitySlots_injective e _ _ (step_of_clock hq) (by
    intro i
    by_cases hi : i.val = 0
    · have hz : i = 0 := Fin.ext hi
      subst i; exact e0
    · simp only [DimensionPolynomial.input, hi, ↓reduceIte]
      exact freshE _ (by simp [capacitySlots, hi]; omega))
  let f := install capacitySlots e q
  have f28 : f 28 = List.replicate (capacity b) true :=
    (install_slot capacitySlots capacitySlots_injective _ _ 7).trans hq7
  have freshF (i : Fin 42) (hi : 39 ≤ i.val) : f i = [] := by
    have hn : ∀ j, capacitySlots j ≠ i := by
      intro j hj; have hv := congrArg Fin.val hj
      simp only [capacitySlots] at hv
      split_ifs at hv <;> simp only [Fin.val_zero] at hv <;> omega
    exact (install_other capacitySlots _ _ _ hn).trans (freshE _ (by omega))
  have sixth := dock_ready _ padSlots (by decide) f _ _
    (Step.of_ready (CloseoutRowsEstimator.Pad.ready (fun _ : Fin 2 => []) (capacity b))) (by
      intro i; fin_cases i
      · exact freshF _ (by decide)
      · exact freshF _ (by decide)
      · exact f28
      · exact freshF _ (by decide))
  let out := install padSlots f (CloseoutRowsEstimator.Pad.output (fun _ : Fin 2 => []) (capacity b))
  refine ⟨out, ((((first.seq second).seq third).seq fourth).seq fifth).seq sixth, ?_, ?_, ?_, ?_⟩
  · exact (install_other padSlots _ _ _ (by decide)).trans
      ((install_slot capacitySlots capacitySlots_injective _ _ 0).trans hq0)
  · exact (install_other padSlots _ _ _ (by decide)).trans
      ((install_other capacitySlots _ _ _ (by decide)).trans
        (install_slot templateSlots (by decide) _ _ 1))
  · exact (install_slot padSlots (by decide) f _ 0).trans (by
      change ZeroPadding.pad (capacity b) [] = _
      simp [ZeroPadding.pad])
  · exact (install_slot padSlots (by decide) f _ 1).trans (by
      change ZeroPadding.pad (capacity b) [] = _
      simp [ZeroPadding.pad])


end NearCubicWires.RepairOrdinary.CloseoutFinalC10AppendWorkspaceInit
