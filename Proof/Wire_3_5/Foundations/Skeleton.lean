import Lean
import Statement_Wire_3_5
import Proof.Wire_3_5.Foundations.Runtime
import Bindings.CLW20_Theorem1_13
import Proof.CaseAnalysis.Assembly
import Proof.Circuits.PolynomialOrdinaryClock
import Proof.Foundations.SupplierPipeline
import Proof.Wire_3_5.Foundations.Carrier
import Proof.Wire_3_5.Foundations.GapFilter
import Proof.Wire_3_5.Foundations.SkeletonBase


noncomputable section
set_option maxRecDepth 4096


/-! # The transfer skeleton: row B from the literals and one fused `Parts`

Realizes the transfer of `tr:appendix` (P3:3232-3957) consumer backward from `rowB`:
* the last step (P3:3813-3853): an `E^NP` certificate plus per-class hardness at every fixed multiplier give
  `WireExponent3_5` (`wireExponent3_5_of_parts`; the onset is the maximum of the two class onsets);
* the refuter step (P3:3699-3702): "By Lemma tr:soundness this machine is one-sided. Once its clock is `o(T(N))`,
  the refuter consequently returns a rejected hierarchy yes-instance at every sufficiently large `N`"
  (`refuter_rejected_yes_at`, from the CLW20 Theorem 1.13 literal at the clock), at the clock of P3:3633, "Choose a polynomial
  hierarchy clock `T(N)=N^{C_clk}`";
* `lem:primitive` (P3:3066-3116) as `FusedPrimitive I`, indexed by the caller's inputs `I : PrimitiveInputs B`
  (P3:3068-3084): its estimate of the masked mean `E_{e,x}[M(e,x) ∏ C_i(x)]` (`prim:truth`, P3:3087-3091) exists
  only as the output word of one program whose budget is the per-call budget of the time ledger `B`
  (`prim:runtime`, P3:3105-3115), with error `n^{−D}` on every admissible tuple; the circuits `C_i` are circuits of
  the class mode (`Mode.Circuit`, the Theorem 2.5 integer syntax) and their functions are `Mode.eval`, a definition;
  a call carries its named carriers and the common star translation, which are per-run data (the machine "guesses
  [...] one sparse grid sum for each distinct PCPP variable" and then "selects the common star translation,
  constructs the shared coordinate filters", P3:3669-3674); an admissible tuple is one whose gates
  are contained in the named carriers (`GatesIn`, P3:3083-3086), and the mask `M(e,x)` is the product of the
  `filt:gap` regular filters of the named carriers' signed mixed-residual populations at the translation, with one
  common seed (P3:3074-3080, 3432-3436), a definition, not an input;
* the union weak machine (P3:3669-3697) as `UnionConstruction I`: a construction applied to the primitive, with
  `tr:soundness` (P3:3504-3554) and `tr:time` (P3:3797-3811) stated for every primitive at `I`; `tr:time` is the
  split of `Runtime3`, so the machine's `o(T(N))` clock comes from `Runtime3.littleO`;
* canonical recovery, `E^NP`, and Cases 1 and 2 (P3:3704-3779) as `Recovery U P`, indexed by the machine built
  from `P`.

Main types: `Parts`, one structure fusing the time ledger, the primitive's inputs, the union construction, the
primitive and the recovery obligations; and the root producer `literals_rowB_of_parts : (Literals → Parts) →
Literals → rowB`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.CLW20Theorem113 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Filters

/-! ## The seam to the statement (P3:3813-3853) -/

/-! ## The refuter step (P3:3699-3702) -/

/-! ## The primitive (`lem:primitive`, P3:3066-3116) -/

namespace PrimitiveInputs

end PrimitiveInputs

/-! ## The union weak machine (P3:3669-3697) -/

/-! ## Recovery, `E^NP`, and Cases 1 and 2 (P3:3704-3779) -/

/-- The refuter step (§H.6: "Run the fixed refuter to obtain z") at one clock `T`, from CLW20 Theorem 1.13 at that clock:
for every one-sided machine within `o(T)`, past an onset, a hierarchy yes-instance the machine rejects. -/
theorem refuter_rejected_yes_at {T : ℕ → ℕ}
    (literal : _root_.NearCubicWires.Bindings.CLW20Theorem113.Theorem1_13At T) :
    ∃ L : Language, InNTIME T L ∧ ∀ M : OrdinaryWeakMachine, OrdinaryLittleO M T → OneSided M L →
      ∃ onset : ℕ, ∀ n, onset ≤ n → ∃ x : BitInput n, L n x = true ∧ ¬ M.accepts n x := by
  obtain ⟨L, hL, _R, _d, refutes⟩ := literal
  refine ⟨L, hL, fun M hM hone => ?_⟩
  obtain ⟨n₀, hone⟩ := hone
  obtain ⟨_C, onset, hrun⟩ := refutes M hM
  refine ⟨max onset n₀, fun n hn => ?_⟩
  obtain ⟨x, _hx, hne⟩ := hrun n (le_of_max_le_left hn)
  have hiff := (machineValue_ne_iff M n x (L n x)).mp hne
  have hrej : ¬ M.accepts n x := fun hacc => by
    have h1 := hone n (le_of_max_le_right hn) x hacc
    have h2 := hiff.mp hacc
    rw [h1] at h2
    exact Bool.noConfusion h2
  refine ⟨x, ?_, hrej⟩
  cases hLx : L n x
  · exact absurd (hiff.mpr hLx) hrej
  · rfl

/-- **The root, fused.** The refuter is applied to `U.build P L`, whose `o(T(N))` clock is `Runtime3.littleO` of
the ledger `B` with the machine's split; `P` is consumed. -/
theorem rowB_of_fused (literals : Literals) {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
    {I : PrimitiveInputs B} (U : UnionConstruction I) (P : FusedPrimitive I) (D : Recovery U P) : rowB := by
  obtain ⟨L, hL, refuted⟩ := refuter_rejected_yes_at (literals.clw113 kclk)
  have hrej := refuted (U.build P L) (U.runtime3 P L).littleO (U.soundness P L hL)
  exact wireExponent3_5_of_parts (1 / 8) (11 / 2) (9 / 2) (D.language L) (D.certificate L)
    (D.thr L hL hrej) (D.sym L hL hrej)

/-! ## The one open part -/

/-- Row B from the nine literals and one `Parts`. -/
theorem rowB_of_parts (literals : Literals) (parts : Parts) : rowB :=
  rowB_of_fused literals parts.union parts.primitive parts.recovery

/-- **The root producer**, in the shape of the target `Literals → rowB`: its one premise is `Literals → Parts`. -/
theorem literals_rowB_of_parts (parts : Literals → Parts) : Literals → rowB :=
  fun literals => rowB_of_parts literals (parts literals)

end NearCubicWires.WireExponent3_5

end
