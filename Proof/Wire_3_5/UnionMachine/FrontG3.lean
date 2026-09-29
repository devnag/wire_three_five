import Proof.Wire_3_5.Recovery.CaseTwoPadGSource

/-! # C6 front, U3+U4: the padded source docked at any layout (P3:3669-3671; G3)

Realizes "Systematic parities are constructed from the PCPP output" (P3:3672) at its source: the PCPP output of the
padded request of the guessed oracle (`osourceG_run`, G3), run on tapes of the front. From the framed
hierarchy word (C6's `hier_ready`), the raw oracle description (C6's `oracle_ready`), `1^q` and `1^cap`
(C6's `cap_ready`) at the images of G3's entry tapes, every other G3 tape blank and every G3 head at `0`, the
focused machine halts within `obudgetG` steps with the clause cache at the images of G3's output slots; its tape `0`
holds the PCPP output word `pcppOutput request (a.output request)` that the table writer streams (C6 CHECKPOINT (b3)
step 6). Tapes outside the focus are untouched.

Main statement: **`g3_step`**. Paper quantity: the PCPP output of the substituted circuit of the guessed oracle. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontG3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

/-- **G3 docked at the slots `slots`**: the focused machine's step from G3's entry (at the slots) to its clause cache
(at the slots of its output tapes), the rest of the ambient bank unchanged. -/
theorem g3_step (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2)))
    (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad) (hpad : k + 3 ≤ Cpad) (r : InputRequest) (q : ℕ)
    (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
    (O : BooleanCircuit q) (cap : ℕ) (hcap : 64 * (O.size + q + 4) + 1 ≤ cap)
    {u : ℕ} (slots : Fin (gtapes source a k) → Fin u) (hinj : Function.Injective slots)
    (H0 : Fin u → ℕ) (A0 : Fin u → List Bool) (hH : ∀ j, H0 (slots j) = 0)
    (hA : ∀ j, A0 (slots j) = oinputG source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap j) :
    let request := PCPPRequestBoundary.request a
      (padSubstituted source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad hq O)
    ∃ (H1 : Fin u → ℕ) (A1 : Fin u → List Bool),
      ExtDecompositionBatch.Step (RecoveryFocus.machine slots
          (omachineG source a k H.coefficient Cpad (VerifierEncoding.code H.verifier)))
        (obudgetG source a H Cpad hpad r hq O cap) H0 A0 H1 A1 ∧
      (∀ j, A1 (slots (oslotsG source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))) =
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size + request.arity)) [] j) ∧
      (∀ j, H1 (slots (oslotsG source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))) =
        PCPPQueryClauseReuse.heads j) ∧
      (∀ i, (∀ j, slots j ≠ i) → H1 i = H0 i ∧ A1 i = A0 i) := by
  intro request
  obtain ⟨res, hrun, -, htap, hhead, -⟩ := osourceG_run source a H Cpad hcoeff hpad r q hq O cap hcap
  obtain ⟨res', hrun', -, -, hh', ht', haway⟩ := RecoveryFocus.dock slots hinj
    (omachineG source a k H.coefficient Cpad (VerifierEncoding.code H.verifier)) _ H0 A0
    (initialConfiguration (omachineG source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (oinputG source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap))
    (fun j => hH j) (fun j => hA j) res hrun
  refine ⟨res'.final.heads, res'.final.tapes, ExtDecompositionBatch.Step.of_run hrun' rfl rfl, ?_, ?_, ?_⟩
  · intro j; rw [ht']; exact htap j
  · intro j; rw [hh']; exact hhead j
  · exact haway

end NearCubicWires.WireExponent3_5.UnionMachine.FrontG3
