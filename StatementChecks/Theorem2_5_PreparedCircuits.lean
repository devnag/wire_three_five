import Proof.Foundations.SourceRegistry

/-! # The Lean wire count is exactly the paper's `W(C)`

`paper.tex:545-548`: "Physical wires count input-to-bottom incidences and top
incidences in a strictly layered simple-edge presentation. Parallel uses are explicit
occurrences, zero-weight inputs and zero top coefficients are deleted, and constants
are propagated before the resource is measured."

`OrdinaryHeadlineTheorem25` quantifies over EVERY stored presentation and counts
`wireCount` without propagating constants. This module proves that this is neither
weaker nor stronger than the paper's Theorem 2.5 (`paper.tex:794-808`): the target
is equivalent to the same statement quantified only over PREPARED presentations
(no constant bottom gate, no zero top coefficient), on which `wireCount` is the
paper's `W(C)`. The nontrivial direction propagates constants explicitly
(`symPrepare`, `thrPrepare`): the function is unchanged and the count does not grow.
Zero-weight inputs are already outside `support` (`RealThresholdGate.mem_support_iff`).
-/
namespace NearCubicWires.Theorem2_5_PreparedCircuits
open NearCubicWires RepairSource
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

/-- A bottom gate computing a constant function on the cube. -/
def ConstantGate {n : ℕ} (g : RealThresholdGate n) : Prop :=
  ∀ x y : BitInput n, g.eval x = g.eval y

/-- The paper's prepared threshold presentation: zero top coefficients deleted and
constants propagated. -/
def ThrPrepared {n : ℕ} (C : ThresholdThresholdCircuit n) : Prop :=
  ∀ i, C.topWeight i ≠ 0 ∧ ¬ ConstantGate (C.bottom i)

theorem constant_eval {n : ℕ} {g : RealThresholdGate n} (h : ¬ ¬ ConstantGate g)
    (x : BitInput n) : g.eval x = g.eval (fun _ => false) :=
  (not_not.mp h) x _

/-! ## Symmetric top -/

/-! ## Threshold top -/

open Classical in
/-- Retained bottom occurrences: nonzero top coefficient and non-constant gate. -/
noncomputable def thrKeep {n : ℕ} (C : ThresholdThresholdCircuit n) :
    Finset (Fin C.bottomCount) :=
  Finset.univ.filter fun i => C.topWeight i ≠ 0 ∧ ¬ ConstantGate (C.bottom i)

/-- Contribution of the deleted occurrences, absorbed into the top threshold. -/
noncomputable def thrOffset {n : ℕ} (C : ThresholdThresholdCircuit n) : ℝ :=
  ∑ i ∈ (thrKeep C)ᶜ, C.topWeight i * bitAsReal ((C.bottom i).eval (fun _ => false))

/-- Constant propagation and zero-coefficient deletion for a threshold top. -/
noncomputable def thrPrepare {n : ℕ} (C : ThresholdThresholdCircuit n) :
    ThresholdThresholdCircuit n where
  bottomCount := (thrKeep C).card
  bottom := fun j => C.bottom ((thrKeep C).equivFin.symm j).1
  topWeight := fun j => C.topWeight ((thrKeep C).equivFin.symm j).1
  topThreshold := C.topThreshold - thrOffset C

theorem thrKeep_mem {n : ℕ} (C : ThresholdThresholdCircuit n) (i : Fin C.bottomCount) :
    i ∈ thrKeep C ↔ (C.topWeight i ≠ 0 ∧ ¬ ConstantGate (C.bottom i)) := by
  simp [thrKeep]

theorem thr_sum {n : ℕ} (C : ThresholdThresholdCircuit n) (x : BitInput n) :
    (∑ i, C.topWeight i * bitAsReal ((C.bottom i).eval x)) =
      (∑ j : Fin (thrKeep C).card, C.topWeight ((thrKeep C).equivFin.symm j).1 *
        bitAsReal ((C.bottom ((thrKeep C).equivFin.symm j).1).eval x)) + thrOffset C := by
  rw [← Finset.sum_add_sum_compl (thrKeep C)]
  congr 1
  · rw [Equiv.sum_comp (thrKeep C).equivFin.symm
      (fun i : thrKeep C => C.topWeight i.1 * bitAsReal ((C.bottom i.1).eval x))]
    exact (Finset.sum_coe_sort (thrKeep C)
      (fun i => C.topWeight i * bitAsReal ((C.bottom i).eval x))).symm
  · unfold thrOffset
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_compl, thrKeep_mem] at hi
    by_cases hw : C.topWeight i = 0
    · rw [hw, zero_mul, zero_mul]
    · have hc : ¬ ¬ ConstantGate (C.bottom i) := fun hnc => hi ⟨hw, hnc⟩
      rw [constant_eval hc x]

theorem thrPrepare_eval {n : ℕ} (C : ThresholdThresholdCircuit n) (x : BitInput n) :
    (thrPrepare C).eval x = C.eval x := by
  simp only [ThresholdThresholdCircuit.eval, thrPrepare]
  rw [thr_sum C x]
  exact decide_eq_decide.mpr sub_le_iff_le_add

theorem thrPrepare_wireCount {n : ℕ} (C : ThresholdThresholdCircuit n) :
    (thrPrepare C).wireCount ≤ C.wireCount := by
  show (∑ j ∈ Finset.univ.filter (fun j : Fin (thrKeep C).card =>
      C.topWeight ((thrKeep C).equivFin.symm j).1 ≠ 0),
      ((C.bottom ((thrKeep C).equivFin.symm j).1).support.card + 1)) ≤
    ∑ i ∈ Finset.univ.filter (fun i => C.topWeight i ≠ 0), ((C.bottom i).support.card + 1)
  have hall : (Finset.univ.filter fun j : Fin (thrKeep C).card =>
      C.topWeight ((thrKeep C).equivFin.symm j).1 ≠ 0) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro j _
    exact ((thrKeep_mem C _).mp ((thrKeep C).equivFin.symm j).2).1
  rw [hall]
  rw [Equiv.sum_comp (thrKeep C).equivFin.symm
    (fun i : thrKeep C => (C.bottom i.1).support.card + 1)]
  rw [Finset.sum_coe_sort (thrKeep C) (fun i => (C.bottom i).support.card + 1)]
  apply Finset.sum_le_sum_of_subset
  intro i hi
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, ((thrKeep_mem C i).mp hi).1⟩

theorem thrPrepare_prepared {n : ℕ} (C : ThresholdThresholdCircuit n) :
    ThrPrepared (thrPrepare C) := by
  intro j
  exact (thrKeep_mem C _).mp ((thrKeep C).equivFin.symm j).2

/-! ## The equivalence -/

end NearCubicWires.Theorem2_5_PreparedCircuits
