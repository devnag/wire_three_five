import Proof.Wire_3_5.Primitive.Writers.Enum

/-! # PA (d), SYM decode (value level): the enumerated SYM state of an index, digit by digit

The SYM batch enumerates the call's states `T = (GapSeed × FlatSeed) × SymState` by `Enum.symIndexEquiv` (seed pair
major, joint state minor; the joint state in the mixed radix `Π_j (m_j+1)²`, each digit `(t_j^+, t_j^−)` by
`finProdFinEquiv`). A register program recovers the state of an index `t < symNT` by divisions: this file states the
components as numbers.

* **`symEnum_vals`**: the filter seed's index `t / Π / |FlatSeed|`, the list seed's index `t / Π % |FlatSeed|`, the
  joint state's index `t % Π` (`Π = Π_j (m_j+1)²`);
* **`stateDigit`**: the joint state's components at `j`: `x / Π_{k<j}(m_k+1)² % (m_j+1)²`, then `/ (m_j+1)` and
  `% (m_j+1)`;
* `gapSeed_of_val`, `flatSeed_of_val`: the seeds as `equiv.symm ⟨index, _⟩` (the forms the FILTER and POP setups take).

Paper quantity of the main type: the SYM state `(e, e', τ)` of the batch's index `t` (samp:seed P3:2913-2917,
row:matrix P3:2658-2660). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDecEnum
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimAsm.Enum

/-- **The joint state's digit `j`**: components `x / Π_{k<j}(m_k+1)² % (m_j+1)²`, then `/ (m_j+1)`, `% (m_j+1)`. -/
theorem stateDigit {a : ℕ} (m : Fin a → ℕ) (x : Fin (∏ j, (m j + 1) * (m j + 1))) (j : Fin a) :
    (((symStateEquiv m).symm x j).1 : ℕ) =
        x / (∏ k : Fin j, (m (Fin.castLE j.is_lt.le k) + 1) * (m (Fin.castLE j.is_lt.le k) + 1)) %
          ((m j + 1) * (m j + 1)) / (m j + 1) ∧
    (((symStateEquiv m).symm x j).2 : ℕ) =
        x / (∏ k : Fin j, (m (Fin.castLE j.is_lt.le k) + 1) * (m (Fin.castLE j.is_lt.le k) + 1)) %
          ((m j + 1) * (m j + 1)) % (m j + 1) :=
  ⟨rfl, rfl⟩

section Call
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
  (carriers : List (Carrier n))

/-- The number of joint states `Π_j (m_j+1)²`. -/
abbrev nSt : ℕ := ∏ j, (symM (I.starParams n hs) Cs j + 1) * (symM (I.starParams n hs) Cs j + 1)

/-- The number of list seeds. -/
abbrev nFlat : ℕ := Fintype.card (symListParams I n a Cs carriers).FlatSeed

/-- The number of filter seeds. -/
abbrev nGap : ℕ := Fintype.card (GapSeed (I.filterParams .sym n))

theorem symNT_eq : symNT I hs Cs carriers = nGap (n := n) I * nFlat I Cs carriers * nSt I hs Cs := rfl

/-- **The enumerated state of an index `t < symNT`, as numbers.** -/
theorem symEnum_vals (t : ℕ) (ht : t < symNT I hs Cs carriers) :
    ((gapSeedEquiv _ (symEnum I hs Cs carriers t).1.1 : ℕ) = t / nSt I hs Cs / nFlat I Cs carriers) ∧
    ((flatSeedEquiv _ (symEnum I hs Cs carriers t).1.2 : ℕ) = t / nSt I hs Cs % nFlat I Cs carriers) ∧
    ((symStateEquiv _ (symEnum I hs Cs carriers t).2 : ℕ) = t % nSt I hs Cs) := by
  have e : symEnum I hs Cs carriers t = (symIndexEquiv I hs Cs carriers).symm ⟨t, ht⟩ := by
    unfold symEnum
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt ht)
  rw [e]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [symIndexEquiv, Equiv.prodCongr] <;> rfl

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.SymDecEnum
