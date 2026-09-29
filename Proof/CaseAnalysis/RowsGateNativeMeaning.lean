import Proof.CaseAnalysis.RowsGateNativeFrame

/-! The physical native word is exactly the corrected source request.
Bottom gates keep their full arity; the retained top uses its original
sorted support map. The same strict threshold is used in both cases. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateNative
open LocalBitMultitape RepairRepresentation CloseoutRowsGateSupport
open SupplierPipeline CompilerSemantics RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_bound {n : ℕ} (g : NormalizedThresholdGate n) :
    ∀ field∈gateFields g,field.2.length ≤ g.encodingBits := by
  intro field hf
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
  simp only [intField,binary_length]
  change intBitLength (g.weight i) ≤ g.encodingBits
  have hsum := Finset.single_le_sum (fun j _ => Nat.zero_le (intBitLength (g.weight j)))
    (Finset.mem_univ i)
  unfold NormalizedThresholdGate.encodingBits
  omega

theorem ordinary_weights {n : ℕ} (g : NormalizedThresholdGate n) (s : Finset (Fin n)) :
    weights false (gateFields g) (gateMembers s)=(List.ofFn g.weight).flatMap intWord := by
  unfold weights
  rw [show (gateFields g).length=n by simp [gateFields],gate_emission]
  simp [selected,keep,PCPPQueryField.selected,List.ofFn_eq_map,List.flatMap_map]

theorem ordinary_word {n : ℕ} (g : SupportedNormalizedGate n) (source : List Bool)
    (hs : readTapeBit source 1=decide (g.gate.threshold<0)) :
    word false (gateFields g.gate) (gateMembers g.support) source g.gate.threshold.natAbs=
      thresholdWord (nonStrictAsStrict g.gate) := by
  change natWord (gateFields g.gate).length++weights false (gateFields g.gate) (gateMembers g.support)++
    CloseoutRowsStrictNative.produced source g.gate.threshold.natAbs=_
  rw [show (gateFields g.gate).length=n by simp [gateFields],ordinary_weights,
    CloseoutRowsStrictNative.produced_eq source g.gate.threshold hs]
  rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsGateNative
