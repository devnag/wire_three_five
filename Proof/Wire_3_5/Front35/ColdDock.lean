import W3.Draft.C3Front
import Proof.Amplification.RecoveryFocusDock
import Proof.MachineModel.Runs

/-!
# The cold front end of the outer step, docked at any layout

Paper v2, §H.5, the outer step of the weak machine: "On a source word `z ∈ {0,1}^N` with `N = 2^a` [...] the weak machine
guesses a circuit `Γ_src` [...] It rejects unless the description of `Γ_src` is well formed and has at most `λ_a` bits,
and it checks deterministically that `Γ_src(bin_a(i)0^{q−a}) = z_i` for every `i < N` [...] runs `A_G` on
`⟨Γ_src⟩_a` [...] guesses a second circuit `Γ_pf` [...] gives the outer verifier `H_Γ`", followed by the PCPP of `H_Γ`
("Systematic parities are constructed from the PCPP output"); the weak machine "rejects every input whose length is not
a power of two" (§H.5, clock paragraph).

The machine is a `ColdNativeW` front end (generic in the import `mw`, the succinct verifier `SV` and the PCPP algorithm
`a`). From `frame x` and `frame raw` (`raw` the payload of the guess's pair field) it decides `Passes` — `N = 2^ν`, the
index guards, the decoded pair within `q^G` gates, the description-length guard `λ_ν` and the source check — on its flag
tape, and on a pass leaves the PCPP clause cache of the request of `H_Γ` (`requestAt mw SV a ν Γ`, whose circuit is
`(Outer.Dat mw SV ν Γ).D`). **`cold_step`** docks one run at injective slots of an ambient bank.

Paper quantity of the main statement: the flag `Passes` and the PCPP output of `H_Γ` (`Outer.Dat`).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Front35

open _root_.NearCubicWires _root_.NearCubicWires.LocalBitMultitape _root_.NearCubicWires.RepairOrdinary
open _root_.NearCubicWires.RepairRepresentation _root_.NearCubicWires.RepairSource NearCubicGates.Close
open W3.NearCubicWires.RepairSource.Outer3

/-- **One run of the cold front end, docked at `slots`**: from its input (`frame x`, `frame raw`, every other tape blank)
at the slots, all heads `0`, the focused machine halts within the front end's budget with the verdict `Passes` on the
flag tape (head `0`) and, on a pass, the PCPP clause cache of `H_Γ`'s request at the cache slots; tapes outside the slots
are untouched. -/
theorem cold_step (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
    (SV : Outer.SuccinctVerifier H L) (a : PointwisePCPPAlgorithm) (cutoff D degree copies : ℕ) (delta : ℚ)
    (C : ColdNativeW mw SV a cutoff D degree copies delta) {n : ℕ} (x : BitInput n) (raw : List Bool)
    (h16 : 16 * raw.length ≤ n) {u : ℕ} (slots : Fin C.tapes → Fin u) (hinj : Function.Injective slots)
    (H0 : Fin u → ℕ) (A0 : Fin u → List Bool) (hH : ∀ j, H0 (slots j) = 0)
    (hA : ∀ j, A0 (slots j) = C.input (List.ofFn x) raw j) :
    ∃ (H1 : Fin u → ℕ) (A1 : Fin u → List Bool),
      ExtDecompositionBatch.Step (RecoveryFocus.machine slots C.machine) (C.budget n x raw) H0 A0 H1 A1 ∧
      H1 (slots C.flagSlot) = 0 ∧ readTapeBit (A1 (slots C.flagSlot)) 0 = C.passed (List.ofFn x) raw ∧
      (C.passed (List.ofFn x) raw = true → ∀ B : Outer.OuterGuess (Outer.width mw SV n),
        Worker.Decodes (Outer.width mw SV n) raw B →
        let r := requestAt mw SV a (Nat.log 2 n) B
        (∀ j : Fin 19, A1 (slots (C.cacheSlots j)) =
          PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
            (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) [] j) ∧
        (∀ j : Fin 19, H1 (slots (C.cacheSlots j)) = PCPPQueryClauseReuse.heads j)) ∧
      (∀ i, (∀ j, slots j ≠ i) → H1 i = H0 i ∧ A1 i = A0 i) := by
  obtain ⟨act, -, hrun, -, -, -, hfh, hflag, hcache⟩ := C.run x raw h16
  obtain ⟨res, hres, -, -, hh, ht, haway⟩ := RecoveryFocus.dock slots hinj C.machine _ H0 A0
    (initialConfiguration C.machine (C.input (List.ofFn x) raw)) (fun j => hH j) (fun j => hA j) act hrun
  refine ⟨res.final.heads, res.final.tapes, ExtDecompositionBatch.Step.of_run hres rfl rfl, ?_, ?_, ?_, ?_⟩
  · rw [hh]; exact hfh
  · rw [ht]; exact hflag
  · intro hp B hB
    obtain ⟨c1, c2, -⟩ := hcache B hp hB
    exact ⟨fun j => by rw [ht]; exact c1 j, fun j => by rw [hh]; exact c2 j⟩
  · exact haway

end NearCubicWires.WireExponent3_5.UnionMachine.Front35
