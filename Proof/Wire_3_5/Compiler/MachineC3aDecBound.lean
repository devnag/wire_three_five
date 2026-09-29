import Proof.Wire_3_5.Compiler.MachineC3aBound

/-! # C3a′'s machine: the decomposition stage's cost (P3:1602-1615)

Paper: alg:disjoint, "Construction is polynomial in the explicit output size" (P3:1614). The decomposition stage
(`Dec.decCost`) runs base's capacity manufacture (`DimensionPolynomial`, whose cost is bounded by base's
`budget_bound`), base's allocation and the occurrence loop (each round's body below the capacity `C`, base's
`actual_capacity`). **`dec_le`**: `decCost ≤ Kd a · (|seg| + 2)^{2·deg a + 3}` with `deg a = 4·a.degree + 4` and a
constant `Kd a` depending only on the decomposition algorithm; **`cap_le`**: the capacity `C = coef a·(|seg|+1)^{deg a}`.
The paper quantity is the cost of the explicit construction of the exact children. Main declarations: `Kd`,
`degD`, **`dec_le`**, **`cap_le`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.C3a.DecBound
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.RepairOrdinary

variable (a : DecompositionAlgorithm)

/-- The decomposition's degree (base's `SourceEnvelope.degree a = 4·a.degree + 4`). -/
def degD : ℕ := SourceEnvelope.degree a

/-- The decomposition stage's constant. -/
def Kd : ℕ :=
  2 * RepairSource.ProjectionNormalization.DimensionPolynomial.coefficient (SourceEnvelope.degree a)
    (SourceEnvelope.coefficient a) + 40 * (SourceEnvelope.coefficient a + 1) + 2

theorem roundSum_le {q : ℕ} (C : ℕ) (occ : List (SupportedNormalizedGate q)) (hb : ∀ g ∈ occ, bodyCost a q g < C) :
    roundSum a C occ ≤ occ.length * (4 * C + 9) := by
  induction occ with
  | nil => simp [roundSum]
  | cons g occ ih =>
    have hg := hb g (by simp)
    have ih' := ih (fun g' hg' => hb g' (by simp [hg']))
    simp only [roundSum, List.map_cons, List.sum_cons] at ih' ⊢
    have hr : roundCost a C g + 2 ≤ 4 * C + 9 := by unfold roundCost; omega
    rw [List.length_cons, Nat.succ_mul]
    omega

theorem occ_le_seg (n : ℕ) (occ : List (SupportedNormalizedGate n)) : occ.length ≤ (C3a.Dec.segOf n occ).length := by
  have h1 := length_le_region occ
  have h2 := segment_length occ (List.replicate n true)
  simp only [C3a.Dec.segOf]
  omega

/-- **The capacity** is the decomposition's polynomial at the stream's length. -/
theorem cap_le (n : ℕ) (occ : List (SupportedNormalizedGate n)) :
    SourceEnvelope.capacity a (C3a.Dec.segOf n occ).length + 1 ≤
      (SourceEnvelope.coefficient a + 1) * ((C3a.Dec.segOf n occ).length + 2) ^ (2 * degD a + 2) := by
  set P := (C3a.Dec.segOf n occ).length
  have hX1 : 1 ≤ (P + 2) ^ (2 * degD a + 2) := Nat.one_le_pow _ _ (by omega)
  have hp : (P + 1) ^ SourceEnvelope.degree a ≤ (P + 2) ^ (2 * degD a + 2) :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by unfold degD; omega))
  have := Nat.mul_le_mul_left (SourceEnvelope.coefficient a) hp
  unfold SourceEnvelope.capacity
  nlinarith

/-- **The decomposition stage's cost** (P3:1614). -/
theorem dec_le (n : ℕ) (occ : List (SupportedNormalizedGate n)) :
    C3a.Dec.decCost a n occ ≤ Kd a * ((C3a.Dec.segOf n occ).length + 2) ^ (2 * degD a + 3) := by
  set P := (C3a.Dec.segOf n occ).length with hP
  set C := SourceEnvelope.capacity a P with hC
  have hq : n ≤ P := C3a.Dec.arity_le_seg n occ
  have hi : (segment occ (List.replicate n true)).length ≤ 1000 * (P + 2) ^ 2 := C3a.Dec.seg_le_sq n occ
  obtain ⟨hbody, _, _, _, _, hheader⟩ := SourceEnvelope.actual_capacity a occ (List.replicate n true) P hq hi
  have hDP := RepairSource.ProjectionNormalization.DimensionPolynomial.budget_bound (SourceEnvelope.degree a)
    (SourceEnvelope.coefficient a) P
  have hround := roundSum_le a C occ hbody
  have hocc := occ_le_seg n occ
  have hcap := cap_le a n occ
  set X := (P + 2) ^ (2 * degD a + 2) with hX
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hXP : (P + 2) ^ (2 * degD a + 3) = X * (P + 2) := by rw [hX, pow_succ]
  set DC := RepairSource.ProjectionNormalization.DimensionPolynomial.coefficient (SourceEnvelope.degree a)
    (SourceEnvelope.coefficient a)
  have hDP' : RepairSource.ProjectionNormalization.DimensionPolynomial.budget (SourceEnvelope.degree a)
      (SourceEnvelope.coefficient a) P ≤ DC * X := hDP
  have hin : C3a.Dec.innerCost a n occ ≤ DC * X + 20 * ((P + 1) * (C + 1)) := by
    unfold C3a.Dec.innerCost Cold.entryBudget Prelude.occurrenceBudget
    rw [Prelude.budget_eq]
    unfold loopCost
    simp only [List.length_replicate]
    rw [← hP, ← hC]
    have hmul : occ.length * (4 * C + 9) ≤ P * (4 * C + 9) := Nat.mul_le_mul_right _ hocc
    nlinarith
  have hPC : (P + 1) * (C + 1) ≤ (SourceEnvelope.coefficient a + 1) * (X * (P + 2)) := by
    have := Nat.mul_le_mul hcap (le_refl (P + 2))
    nlinarith
  unfold C3a.Dec.decCost
  rw [hXP]
  unfold Kd
  nlinarith


end NearCubicWires.WireExponent3_5.CompilerMachine.C3a.DecBound
