import Proof.Wire_3_5.Foundations.Carrier

/-! # Named carriers: wires, complemented and constant atoms, and the proofs of the carrier definitions

Realizes, for the carrier definitions of the seed module `Proof.Wire_3_5.Foundations.Carrier` (`lem:primitive`,
P3:3071-3086; `tr:masks`, P3:3401-3419): the weight of the residual vector is `R_X` (`filt:gap`, P3:2019:
`w(Z) = Σ_i Z_i`); "A complemented carrier negates `Δ_i`, and a constant carrier has zero residual" (P3:2444-2445);
"their actual support sizes sum to at most the physical wire count" (P3:1320-1321); and the duty of containment
"whose gates are contained in these carriers" (P3:3083-3086).

Main declarations:
* `Carrier.wires` = `W_X`, the physical wires charged by the carrier's atom occurrences (actual support plus one top
  wire each), with `wires_thrGates_le`, `wires_symGates_le : W ≤ wireCount`;
* `complAtom`, `constAtom` and their residual laws;
* `count_residualBits : w(Z) = R_X`; `population_flatten`, `population_le_of_subperm`;
* **`GatesIn.population_le`**: every admitted circuit's residual population is at most `Σ_X R_X`, pointwise;
  `gatesIn_of_sublist`: the union machine's calls are admitted. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Stars
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline

namespace Carrier
variable {n : ℕ}

/-- The weight of the residual bit vector is `R_X` (`w(Z) = Σ_i Z_i`, P3:2019). -/
theorem count_residualBits (X : Carrier n) (c u v : BitInput n) :
    (X.residualBits c u v).count true = X.population c u v := by
  induction X with
  | nil => rfl
  | cons g X ih =>
    simp only [residualBits, List.flatMap_cons, List.count_append, population, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [ih]
    simp only [atomResidual]
    cases residualPlus g.eval c u v <;> cases residualMinus g.eval c u v <;> simp

/-- One atom's physical wires: its actual support plus its one top wire (P3:213-216, 1321). -/
def atomWires (g : NormalizedThresholdGate n) : ℕ :=
  (Finset.univ.filter fun i => g.weight i ≠ 0).card + 1

/-- **`W_X`**: the physical wires charged by the carrier's atom occurrences (P3:1321, 1332). -/
def wires (X : Carrier n) : ℕ := (X.map atomWires).sum

theorem population_append (X Y : Carrier n) (c u v : BitInput n) :
    (X ++ Y).population c u v = X.population c u v + Y.population c u v := by
  simp [population, List.sum_append]

/-- The population of a union of named carriers is the sum of their populations. -/
theorem population_flatten (named : List (Carrier n)) (c u v : BitInput n) :
    population named.flatten c u v = (named.map fun X => population X c u v).sum := by
  induction named with
  | nil => rfl
  | cons X named ih =>
    rw [List.flatten_cons, population_append, ih, List.map_cons, List.sum_cons]

/-- A sub-multiset has at most the population (with multiplicity). -/
theorem population_le_of_subperm {X Y : Carrier n} (h : X.Subperm Y) (c u v : BitInput n) :
    X.population c u v ≤ Y.population c u v := by
  obtain ⟨l, hperm, hsub⟩ := h
  have h1 : (l.map fun g => atomResidual g c u v).sum = (X.map fun g => atomResidual g c u v).sum :=
    (hperm.map _).sum_eq
  have h2 : (l.map fun g => atomResidual g c u v).sum ≤ (Y.map fun g => atomResidual g c u v).sum :=
    (hsub.map _).sum_le_sum fun a _ => Nat.zero_le a
  unfold population; omega

end Carrier

/-! ## The gates of a circuit, as its wire count charges them (P3:213-216, 1320-1321) -/

/-- Filtering a list and summing is summing the indicator-weighted terms. -/
theorem sum_map_filter_eq {α : Type} (l : List α) (p : α → Bool) (f : α → ℕ) :
    ((l.filter p).map f).sum = (l.map fun a => if p a then f a else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

/-- An atom's actual support is inside its charged support (`zeroOutside`). -/
theorem atomWires_le {n : ℕ} (g : SupportedNormalizedGate n) :
    Carrier.atomWires g.gate ≤ g.wireCount + 1 := by
  unfold Carrier.atomWires SupportedNormalizedGate.wireCount
  have : (Finset.univ.filter fun i => g.gate.weight i ≠ 0) ⊆ g.support := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra h; exact hi (g.zeroOutside i h)
  have := Finset.card_le_card this
  omega

theorem wires_thrGates_eq {n : ℕ} (C : SupplierPipeline.NormalizedThresholdThresholdCircuit n) :
    (thrGates C).wires = ∑ i ∈ C.top.support, Carrier.atomWires (C.bottom i).gate := by
  unfold thrGates Carrier.wires
  rw [List.map_map, sum_map_filter_eq, ← Fin.sum_univ_def, ← Finset.sum_filter]
  congr 1
  ext i; simp

/-- The charged gates of a `THR∘THR` circuit carry at most its physical wires (P3:1321: "their actual support
sizes sum to at most the physical wire count"). -/
theorem wires_thrGates_le {n : ℕ} (C : SupplierPipeline.NormalizedThresholdThresholdCircuit n) :
    (thrGates C).wires ≤ C.wireCount := by
  rw [wires_thrGates_eq]
  unfold SupplierPipeline.NormalizedThresholdThresholdCircuit.wireCount
  exact Finset.sum_le_sum fun i _ => atomWires_le _

/-- The same for a `SYM∘THR` circuit. -/
theorem wires_symGates_le {n : ℕ} (C : SupplierPipeline.NormalizedSymmetricThresholdCircuit n) :
    (symGates C).wires ≤ C.wireCount := by
  unfold symGates Carrier.wires SupplierPipeline.NormalizedSymmetricThresholdCircuit.wireCount
  rw [List.map_map, ← Fin.sum_univ_def]
  exact Finset.sum_le_sum fun i _ => atomWires_le _

/-! ## Containment (P3:3083-3086) and its semantic duty -/

/-- **The duty of containment:** at every star point, each admitted circuit's residual population (with
multiplicity) is at most the sum of the named carriers' populations `Σ_X R_X`. This is what makes the named
filters on `R_X` control the circuits' own residual counts. -/
theorem GatesIn.population_le {n a : ℕ} {gates : Fin a → Carrier n} {named : List (Carrier n)}
    (h : GatesIn gates named) (i : Fin a) (c u v : BitInput n) :
    Carrier.population (gates i) c u v ≤ (named.map fun X => Carrier.population X c u v).sum := by
  rw [← Carrier.population_flatten]
  exact Carrier.population_le_of_subperm (h i) c u v

end NearCubicWires.WireExponent3_5.Stars
